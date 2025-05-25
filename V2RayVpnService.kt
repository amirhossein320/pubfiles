package com.vpn.saronet.sevice

import android.app.Notification
import android.app.NotificationChannel
import android.app.NotificationManager
import android.app.PendingIntent
import android.app.Service
import android.content.BroadcastReceiver
import android.content.Context
import android.content.Intent
import android.content.IntentFilter
import android.content.res.Configuration
import android.graphics.Color
import android.net.ConnectivityManager
import android.net.LocalSocket
import android.net.LocalSocketAddress
import android.net.Network
import android.net.NetworkCapabilities
import android.net.NetworkRequest
import android.net.TrafficStats
import android.net.VpnService
import android.os.Build
import android.os.Bundle
import android.os.ParcelFileDescriptor
import android.os.StrictMode
import android.util.Log
import androidx.annotation.RequiresApi
import androidx.core.app.NotificationCompat
import androidx.core.content.ContextCompat
import androidx.lifecycle.viewModelScope
import com.tencent.mmkv.MMKV
import com.vpn.saronet.App
import com.vpn.saronet.BuildConfig
import com.vpn.saronet.R
import com.vpn.saronet.data.local.SettingsPrefRepositoryImp
import com.vpn.saronet.data.local.UserPrefRepositoryImp
import com.vpn.saronet.domain.model.AppConfig
import com.vpn.saronet.domain.model.AppConfig.ANG_PACKAGE
import com.vpn.saronet.domain.model.AppConfig.LOOPBACK
import com.vpn.saronet.domain.model.AppConfig.TAG_DIRECT
import com.vpn.saronet.domain.model.ProfileItem
import com.vpn.saronet.domain.model.convertV2RayConfigToProfileItem
import com.vpn.saronet.domain.model.getDomainPort
import com.vpn.saronet.ui.screen.main.ConnectionState
import com.vpn.saronet.ui.screen.main.MainActivity
import com.vpn.saronet.util.MessageUtil
import com.vpn.saronet.util.PluginUtil
import com.vpn.saronet.util.Utils
import com.vpn.saronet.util.toSpeedString
import com.vpn.saronet.util.toTrafficString
import dagger.hilt.android.AndroidEntryPoint
import go.Seq
import io.reactivex.rxjava3.core.Observable
import io.reactivex.rxjava3.disposables.Disposable
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.Job
import kotlinx.coroutines.SupervisorJob
import kotlinx.coroutines.async
import kotlinx.coroutines.cancel
import kotlinx.coroutines.delay
import kotlinx.coroutines.flow.collectLatest
import kotlinx.coroutines.flow.distinctUntilChanged
import kotlinx.coroutines.flow.first
import kotlinx.coroutines.flow.last
import kotlinx.coroutines.flow.map
import kotlinx.coroutines.flow.update
import kotlinx.coroutines.launch
import kotlinx.coroutines.runBlocking
import kotlinx.serialization.encodeToString
import kotlinx.serialization.json.Json
import kotlinx.serialization.json.jsonObject
import libv2ray.CoreCallbackHandler
import libv2ray.CoreController
import libv2ray.Libv2ray
import timber.log.Timber
import java.io.File
import java.util.Locale
import javax.inject.Inject
import kotlin.collections.forEach
import kotlin.io.use
import kotlin.jvm.java
import kotlin.let
import kotlin.math.min
import kotlin.ranges.step
import kotlin.text.substring
import kotlin.toString

@AndroidEntryPoint
class V2RayVpnService : VpnService(), ServiceControl {

    companion object {
        private const val VPN_MTU = 1500
        private const val PRIVATE_VLAN4_CLIENT = "10.10.10.1"
        private const val PRIVATE_VLAN4_ROUTER = "10.10.10.2"
        private const val PRIVATE_VLAN6_CLIENT = "fc00::10:10:10:1"
        private const val PRIVATE_VLAN6_ROUTER = "fc00::10:10:10:2"
        private const val TUN2SOCKS = "libtun2socks.so"

        const val NOTIFICATION_ID = 1
        const val NOTIFICATION_PENDING_INTENT_CONTENT = 0
        const val NOTIFICATION_PENDING_INTENT_STOP_V2RAY = 1
        const val NOTIFICATION_PENDING_INTENT_RESTART_V2RAY = 2
        const val NOTIFICATION_ICON_THRESHOLD = 3000
    }

    @Inject
    lateinit var userPref: UserPrefRepositoryImp

    @Inject
    lateinit var appPref: SettingsPrefRepositoryImp

    @Inject
    lateinit var appJson: Json
    private var mInterface: ParcelFileDescriptor? = null
    private var isRunning = false
    private lateinit var process: Process
    private var elapsedTime = 0L
    private var lastQueryTime = 0L
    private var mBuilder: NotificationCompat.Builder? = null
    private var mDisposable: Disposable? = null
    private var mNotificationManager: NotificationManager? = null
    private val coreController: CoreController = Libv2ray.newCoreController(CoreCallback())
    private var currentConfig: ProfileItem? = null
    private val messageReceiver = ReceiveMessageHandler()
    private val job = SupervisorJob()
    private val serviceScope = CoroutineScope(Dispatchers.IO + job)
    private var notificationTitle = "SaroNet"
    private var isScreenOn = true

    private var trafficJob: Job? = null
    private var downloadTraffic: Long = 0L
    private var uploadTraffic: Long = 0L

    enum class State {
        START, STOP, RESTART, WIDGET, TRAFFIC, CHECK
    }


     inner class CoreCallback : CoreCallbackHandler {
        /**
         * Called when V2Ray core starts up.
         * @return 0 for success, any other value for failure.
         */
        override fun startup(): Long {
            return 0
        }

        /**
         * Called when V2Ray core shuts down.
         * @return 0 for success, any other value for failure.
         */
        override fun shutdown(): Long {
            return try {
                stopService()
                0
            } catch (e: Exception) {
                Timber.e(e, "Failed to stop service in callback")
                -1
            }
        }

        /**
         * Called when V2Ray core emits status information.
         * @param l Status code.
         * @param s Status message.
         * @return Always returns 0.
         */
        override fun onEmitStatus(l: Long, s: String?): Long {
            return 0
        }


    }

    @delegate:RequiresApi(Build.VERSION_CODES.P)
    private val defaultNetworkRequest by lazy {
        NetworkRequest.Builder()
            .addCapability(NetworkCapabilities.NET_CAPABILITY_INTERNET)
            .addCapability(NetworkCapabilities.NET_CAPABILITY_NOT_RESTRICTED)
            .build()
    }

    private val connectivity by lazy { getSystemService(CONNECTIVITY_SERVICE) as ConnectivityManager }

    @delegate:RequiresApi(Build.VERSION_CODES.P)
    private val defaultNetworkCallback by lazy {
        object : ConnectivityManager.NetworkCallback() {
            override fun onAvailable(network: Network) {
                setUnderlyingNetworks(arrayOf(network))
            }

            override fun onCapabilitiesChanged(
                network: Network,
                networkCapabilities: NetworkCapabilities
            ) {
                // it's a good idea to refresh capabilities
                setUnderlyingNetworks(arrayOf(network))
            }

            override fun onLost(network: Network) {
                setUnderlyingNetworks(null)
            }
        }
    }

    override fun onCreate() {
        super.onCreate()
        connectivity.registerNetworkCallback(defaultNetworkRequest, defaultNetworkCallback)
        val policy = StrictMode.ThreadPolicy.Builder().permitAll().build()
        StrictMode.setThreadPolicy(policy)
        Seq.setContext(applicationContext)
        Libv2ray.initCoreEnv(Utils.userAssetPath(this.applicationContext), Utils.getDeviceIdForXUDPBaseKey())


        try {
            val mFilter = IntentFilter(AppConfig.BROADCAST_ACTION_SERVICE)
            mFilter.addAction(Intent.ACTION_SCREEN_ON)
            mFilter.addAction(Intent.ACTION_SCREEN_OFF)
            mFilter.addAction(Intent.ACTION_USER_PRESENT)
            ContextCompat.registerReceiver(
                this@V2RayVpnService,
                messageReceiver,
                mFilter,
                Utils.receiverFlags()
            )
        } catch (e: Exception) {
            Timber.tag(ANG_PACKAGE).d(e.toString())
        }
    }

    override fun onRevoke() {
        stopV2Ray()
    }

    override fun onDestroy() {
        Timber.d("destroy vpn")
        cancelNotification()
        serviceScope.cancel()
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.P) {
            try {
                connectivity.unregisterNetworkCallback(defaultNetworkCallback)
            } catch (ignored: Exception) {
                ignored.printStackTrace()
            }
        }
        try {
            this.unregisterReceiver(messageReceiver)
        } catch (e: Exception) {
            Timber.tag(ANG_PACKAGE).d(e.toString())
        }
        super.onDestroy()
    }

    override fun onStartCommand(intent: Intent?, flags: Int, startId: Int): Int {
        Timber.d("service start command ${intent?.action}")
        when (intent?.action) {
            State.START.toString() -> {
                startV2rayPoint()
                return START_STICKY
            }

            State.STOP.toString() -> {
                if (isRunning) {
                    stopV2Ray()
                }
                return START_NOT_STICKY
            }

            State.RESTART.toString() -> {
                if (isRunning) stopV2Ray()
                startV2rayPoint()
                return START_STICKY
            }

            State.CHECK.toString() -> {
                if (isRunning) MessageUtil.sendMsg2UI(
                    this@V2RayVpnService,
                    AppConfig.MSG_STATE_RESUME_SUCCESS,
                    Pair(elapsedTime, Pair(downloadTraffic, uploadTraffic))
                )
                return START_NOT_STICKY
            }

            State.WIDGET.toString() -> {
                if (isRunning) stopV2Ray()
                else startV2rayPoint()
                return START_STICKY
            }

            State.TRAFFIC.toString() -> {
                updateNotification(
                    intent.getStringExtra("downText").toString(),
                    intent.getStringExtra("upText").toString()
                )
                return START_NOT_STICKY
            }
        }
        return START_REDELIVER_INTENT
    }

    override fun getService(): Service {
        return this
    }

    override fun startService() {

    }

    override fun stopService() {
        stopV2Ray(true)
    }

    override fun vpnProtect(socket: Int): Boolean {
        return protect(socket)
    }

    @RequiresApi(Build.VERSION_CODES.N)
    override fun attachBaseContext(newBase: Context?) {
        super.attachBaseContext(newBase)
    }

    private suspend fun setup() {
        Timber.d("amir")
        val prepare = prepare(this)
        if (prepare != null) {
            return
        }

        // If the old interface has exactly the same parameters, use it!
        // Configure a builder while parsing the parameters.
        val builder = Builder()
        //val enableLocalDns = defaultDPreference.getPrefBoolean(AppConfig.PREF_LOCAL_DNS_ENABLED, false)

        builder.setMtu(VPN_MTU)
        builder.addAddress(PRIVATE_VLAN4_CLIENT, 30)
        //builder.addDnsServer(PRIVATE_VLAN4_ROUTER)
//        val bypassLan = SettingsManager.routingRulesetsBypassLan()
//        if (bypassLan) {
//            resources.getStringArray(R.array.bypass_private_ip_address).forEach {
//                val addr = it.split('/')
//                builder.addRoute(addr[0], addr[1].toInt())
//            }
//        } else {
        builder.addRoute("0.0.0.0", 0)
//        }

//        if (MmkvManager.decodeSettingsBool(AppConfig.PREF_PREFER_IPV6) == true) {
//            builder.addAddress(PRIVATE_VLAN6_CLIENT, 126)
//            if (bypassLan) {
//                builder.addRoute("2000::", 3) //currently only 1/8 of total ipV6 is in use
//            } else {
//                builder.addRoute("::", 0)
//            }
//        }

//        if (MmkvManager.decodeSettingsBool(AppConfig.PREF_LOCAL_DNS_ENABLED) == true) {
//            builder.addDnsServer(PRIVATE_VLAN4_ROUTER)
//        } else {
//        Utils.getVpnDnsServers()
//            .forEach {
//                if (Utils.isPureIpAddress(it)) {
//                    builder.addDnsServer(it)
//                }
//            }
//        }

        builder.setSession(currentConfig?.remarks.toString())

        val selfPackageName = BuildConfig.APPLICATION_ID
        serviceScope.async {
            appPref.getIgnoreApps().let {
                Timber.d("apps ->  $it")
                if (it.isEmpty()) builder.addDisallowedApplication(selfPackageName)
                else it.forEach { app ->
                    builder.addDisallowedApplication(app)
                }
            }
        }.await()
//        if (MmkvManager.decodeSettingsBool(AppConfig.PREF_PER_APP_PROXY)) {
//            val apps = MmkvManager.decodeSettingsStringSet(AppConfig.PREF_PER_APP_PROXY_SET)
//            val bypassApps = MmkvManager.decodeSettingsBool(AppConfig.PREF_BYPASS_APPS)
//            //process self package
//            if (bypassApps) apps?.add(selfPackageName) else apps?.remove(selfPackageName)
//            apps?.forEach {
//                try {
//                    if (bypassApps)
//                        builder.addDisallowedApplication(it)
//                    else
//                        builder.addAllowedApplication(it)
//                } catch (e: PackageManager.NameNotFoundException) {
//                    Log.d(ANG_PACKAGE, "setup error : --${e.localizedMessage}")
//                }
//            }
//        } else {
//            builder.addDisallowedApplication(selfPackageName)
//        }

        // Close the old interface since the parameters have been changed.
        try {
            mInterface?.close()
        } catch (ignored: Exception) {
            // ignored
        }

        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.P) {
            try {
                connectivity.requestNetwork(defaultNetworkRequest, defaultNetworkCallback)
            } catch (e: Exception) {
                e.printStackTrace()
            }
        }

        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.Q) {
            builder.setMetered(false)
//            if (MmkvManager.decodeSettingsBool(AppConfig.PREF_APPEND_HTTP_PROXY)) {
//                builder.setHttpProxy(
//                    ProxyInfo.buildDirectProxy(
//                        LOOPBACK,
//                        SettingsManager.getHttpPort()
//                    )
//                )
//            }
        }

        // Create a new interface using the builder and save the parameters.
        try {
            mInterface = builder.establish()!!
            isRunning = true
            runTun2socks()
        } catch (e: Exception) {
            Timber.e(e)
            // non-nullable lateinit var
            e.printStackTrace()
            stopV2Ray()
        }
    }

    private fun runTun2socks() {
        val socksPort = AppConfig.PORT_SOCKS.toInt()
        val cmd = arrayListOf(
            File(applicationContext.applicationInfo.nativeLibraryDir, TUN2SOCKS).absolutePath,
            "--netif-ipaddr",
            PRIVATE_VLAN4_ROUTER,
            "--netif-netmask",
            "255.255.255.252",
            "--socks-server-addr",
            "$LOOPBACK:${socksPort}",
            "--tunmtu",
            VPN_MTU.toString(),
            "--sock-path",
            "sock_path",//File(applicationContext.filesDir, "sock_path").absolutePath,
            "--enable-udprelay",
            "--loglevel",
            "notice"
        )

//        if (MmkvManager.decodeSettingsBool(AppConfig.PREF_PREFER_IPV6)) {
//            cmd.add("--netif-ip6addr")
//            cmd.add(PRIVATE_VLAN6_ROUTER)
//        }
//        if (MmkvManager.decodeSettingsBool(AppConfig.PREF_LOCAL_DNS_ENABLED)) {
//            val localDnsPort = Utils.parseInt(
//                MmkvManager.decodeSettingsString(AppConfig.PREF_LOCAL_DNS_PORT),
//                AppConfig.PORT_LOCAL_DNS.toInt()
//            )
//            cmd.add("--dnsgw")
//            cmd.add("$LOOPBACK:${localDnsPort}")
//        }
        Timber.tag(packageName).d("amir ${cmd.toString()}")

        try {
            val proBuilder = ProcessBuilder(cmd)
            proBuilder.redirectErrorStream(true)
            process = proBuilder
                .directory(applicationContext.filesDir)
                .start()
            Thread {
                Timber.tag(packageName).d("$TUN2SOCKS check")
                process.waitFor()
                Timber.tag(packageName).d("$TUN2SOCKS exited")
                if (isRunning) {
                    Timber.tag(packageName).d("$TUN2SOCKS restart")
                    runTun2socks()
                }
            }.start()
            Timber.tag(packageName).d(process.toString())

            sendFd()
        } catch (e: Exception) {
            Timber.tag(packageName).d(e.toString())
        }
    }

    private fun sendFd() {
        val fd = mInterface?.fileDescriptor
        val path = File(applicationContext.filesDir, "sock_path").absolutePath
        Timber.tag(packageName).d(path)

        CoroutineScope(Dispatchers.IO).launch {
            var tries = 0
            while (true) try {
                Thread.sleep(50L shl tries)
                Timber.tag(packageName).d("sendFd tries: $tries")
                LocalSocket().use { localSocket ->
                    localSocket.connect(
                        LocalSocketAddress(
                            path,
                            LocalSocketAddress.Namespace.FILESYSTEM
                        )
                    )
                    localSocket.setFileDescriptorsForSend(arrayOf(fd))
                    localSocket.outputStream.write(42)
                }
                break
            } catch (e: Exception) {
                Timber.tag(packageName).d(e.toString())
                if (tries > 5) break
                tries += 1
            }
        }
    }

    private fun stopV2Ray(isForced: Boolean = true) {
        isRunning = false
        try {
            Timber.d("tun2socks destroy")
            process.destroy()
        } catch (e: Exception) {
            Timber.d(e.toString())
        }

        stopV2rayPoint()

        if (isForced) {
            //stopSelf has to be called ahead of mInterface.close(). otherwise v2ray core cannot be stooped
            //It's strage but true.
            //This can be verified by putting stopself() behind and call stopLoop and startLoop
            //in a row for several times. You will find that later created v2ray core report port in use
            //which means the first v2ray core somehow failed to stop and release the port.
            stopSelf()

            try {
                mInterface?.close()
            } catch (ignored: Exception) {
                ignored.printStackTrace()
            }
        }
    }

    fun startV2Ray() {
        if (coreController.isRunning) return
        val intent = Intent(applicationContext, V2RayVpnService::class.java)
        intent.action = State.START.toString()
        if (Build.VERSION.SDK_INT > Build.VERSION_CODES.N_MR1) {
            startForegroundService(intent)
        } else {
            startService(intent)
        }
    }

    fun startV2rayPoint() {
        serviceScope.launch(Dispatchers.IO) {
            if (!userPref.isLogged()) {
                stopV2Ray()
                return@launch
            }
            var selectedConfig = appPref.getSelectedConfig() ?: run {
                stopV2Ray()
                return@launch
            }
            val jsonConfig = selectedConfig.first
            notificationTitle = selectedConfig.second
            MessageUtil.sendMsg2UI(this@V2RayVpnService, AppConfig.MSG_STATE_RUNNING, "")
            val config =
                convertV2RayConfigToProfileItem(appJson.parseToJsonElement(jsonConfig).jsonObject)
            if (coreController.isRunning) {
                MessageUtil.sendMsg2UI(this@V2RayVpnService, AppConfig.MSG_STATE_START, "")
                return@launch
            }

            currentConfig = config

            try {
                Timber.e("Started loop")
                coreController.startLoop(jsonConfig)
            } catch (e: Exception) {
                Timber.e(e, "Failed to start Core loop")
            }

            if (coreController.isRunning) {
                elapsedTime = System.currentTimeMillis()
                initTrafficTimer()
                MessageUtil.sendMsg2UI(
                    this@V2RayVpnService,
                    AppConfig.MSG_STATE_START_SUCCESS,
                    Pair(0L, Pair(downloadTraffic, uploadTraffic))
                )
                showNotification()
                setup()
//                PluginUtil.runPlugin(this@V2RayVpnService, jsonConfig, domainPort)
            } else {
                MessageUtil.sendMsg2UI(this@V2RayVpnService, AppConfig.MSG_STATE_START_FAILURE, "")
                cancelNotification()
            }
        }

    }

    fun stopV2rayPoint() {

        if (coreController.isRunning) {
            CoroutineScope(Dispatchers.IO).launch {
                try {
                    coreController.stopLoop()
                } catch (e: Exception) {
                    Timber.tag(ANG_PACKAGE).d(e.toString())
                }
            }
        }

        MessageUtil.sendMsg2UI(this, AppConfig.MSG_STATE_STOP_SUCCESS, "")
        cancelNotification()
        trafficJob?.cancel()

        PluginUtil.stopPlugin()
    }

    private fun measureV2rayDelay() {
        CoroutineScope(Dispatchers.IO).launch {
//            var time = -1L
//            var errStr = ""
//            if (v2rayPoint.isRunning) {
//                try {
//                    time = v2rayPoint.measureDelay(Utils.getDelayTestUrl())
//                } catch (e: Exception) {
//                    Timber.tag(ANG_PACKAGE).d("measureV2rayDelay: $e")
//                    errStr = e.message?.substringAfter("\":") ?: "empty message"
//                }
//                if (time == -1L) {
//                    try {
//                        time = v2rayPoint.measureDelay(Utils.getDelayTestUrl(true))
//                    } catch (e: Exception) {
//                        Timber.tag(ANG_PACKAGE).d("measureV2rayDelay: $e")
//                        errStr = e.message?.substringAfter("\":") ?: "empty message"
//                    }
//                }
//            }
//            val result = if (time == -1L) {
//                this@V2RayVpnService.getString(R.string.connection_test_error)
//            } else {
//                this@V2RayVpnService.getString(R.string.connection_test_available)
//            }
//
//            MessageUtil.sendMsg2UI(
//                this@V2RayVpnService,
//                AppConfig.MSG_MEASURE_DELAY_SUCCESS,
//                result
//            )
        }
    }

    private fun showNotification() {
        val flags = if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M) {
            PendingIntent.FLAG_IMMUTABLE or PendingIntent.FLAG_UPDATE_CURRENT
        } else {
            PendingIntent.FLAG_UPDATE_CURRENT
        }

        val startMainIntent = Intent(this, MainActivity::class.java)
        val contentPendingIntent = PendingIntent.getActivity(
            this,
            NOTIFICATION_PENDING_INTENT_CONTENT,
            startMainIntent,
            flags
        )

        val stopV2RayIntent = Intent(AppConfig.BROADCAST_ACTION_SERVICE)
        stopV2RayIntent.`package` = ANG_PACKAGE
        stopV2RayIntent.putExtra("key", AppConfig.MSG_STATE_STOP)
        val stopV2RayPendingIntent = PendingIntent.getBroadcast(
            this,
            NOTIFICATION_PENDING_INTENT_STOP_V2RAY,
            stopV2RayIntent,
            flags
        )

        val restartV2RayIntent = Intent(AppConfig.BROADCAST_ACTION_SERVICE)
        restartV2RayIntent.`package` = ANG_PACKAGE
        restartV2RayIntent.putExtra("key", AppConfig.MSG_STATE_RESTART)
        val restartV2RayPendingIntent = PendingIntent.getBroadcast(
            this,
            NOTIFICATION_PENDING_INTENT_RESTART_V2RAY,
            restartV2RayIntent,
            flags
        )

        val channelId =
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
                createNotificationChannel()
            } else {
                // If earlier version channel ID is not used
                // https://developer.android.com/reference/android/support/v4/app/NotificationCompat.Builder.html#NotificationCompat.Builder(android.content.Context)
                ""
            }

        val (stopTitle, restartTitle) = getLocalizedContext().let {
            val stop = it.getString(R.string.notification_action_stop_v2ray)
            val restart = it.getString(R.string.title_service_restart)
            stop to restart
        }
        mBuilder = NotificationCompat.Builder(this, channelId)
            .setSmallIcon(R.drawable.logo_white)
            .setContentTitle(notificationTitle)
            .setContentText("\u2191 0 kb \u2502 \u2193 0 kb")
            .setPriority(NotificationCompat.PRIORITY_MIN)
            .setOngoing(true)
            .setUsesChronometer(true)
            .setShowWhen(false)
            .setOnlyAlertOnce(true)
            .setContentIntent(contentPendingIntent)
            .addAction(
                R.drawable.ic_stop_24dp,
                stopTitle,
                stopV2RayPendingIntent
            )
            .addAction(
                R.drawable.ic_restore_24dp,
                restartTitle,
                restartV2RayPendingIntent
            )
        //.build()

        //mBuilder?.setDefaults(NotificationCompat.FLAG_ONLY_ALERT_ONCE)  //取消震动,铃声其他都不好使
        try {
            startForeground(NOTIFICATION_ID, mBuilder?.build())
        } catch (e: Exception) {
            stopSelf()
        }
    }

    @RequiresApi(Build.VERSION_CODES.O)
    private fun createNotificationChannel(): String {
        val channelId = AppConfig.RAY_NG_CHANNEL_ID
        val channelName = AppConfig.RAY_NG_CHANNEL_NAME
        val chan = NotificationChannel(
            channelId,
            channelName, NotificationManager.IMPORTANCE_HIGH
        )
        chan.lightColor = Color.DKGRAY
        chan.importance = NotificationManager.IMPORTANCE_NONE
        chan.lockscreenVisibility = Notification.VISIBILITY_PRIVATE
        getNotificationManager()?.createNotificationChannel(chan)
        return channelId
    }

    fun cancelNotification() {
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.N) {
            stopForeground(STOP_FOREGROUND_REMOVE)
        } else {
            stopForeground(true)
        }

        lastQueryTime = 0L
        elapsedTime = 0L
        mBuilder = null
        mDisposable?.dispose()
        mDisposable = null
    }

    private fun updateNotification(contentText: String?, proxyTraffic: Long, directTraffic: Long) {
        if (mBuilder != null) {
            if (proxyTraffic < NOTIFICATION_ICON_THRESHOLD && directTraffic < NOTIFICATION_ICON_THRESHOLD) {
                mBuilder?.setSmallIcon(R.mipmap.ic_launcher)
            } else if (proxyTraffic > directTraffic) {
                mBuilder?.setSmallIcon(R.mipmap.ic_launcher)
            } else {
                mBuilder?.setSmallIcon(R.mipmap.ic_launcher)
            }
            mBuilder?.setStyle(NotificationCompat.BigTextStyle().bigText(contentText))
            mBuilder?.setContentText(contentText) // Emui4.1 need content text even if style is set as BigTextStyle
            getNotificationManager()?.notify(NOTIFICATION_ID, mBuilder?.build())
        }
    }

    private fun updateNotification(downText: String, upText: String) {
        if (mBuilder != null) {
            mBuilder?.setContentTitle(notificationTitle)
            mBuilder?.setContentText("\u2191 $upText \u2502 \u2193 $downText")
            getNotificationManager()?.notify(NOTIFICATION_ID, mBuilder?.build())
        }
    }

    private fun getNotificationManager(): NotificationManager? {
        if (mNotificationManager == null) {
            mNotificationManager =
                getSystemService(Context.NOTIFICATION_SERVICE) as NotificationManager
        }
        return mNotificationManager
    }

    private fun startSpeedNotification() {
        if (mDisposable == null && coreController.isRunning && false) {
            var lastZeroSpeed = false
//            val outboundTags = currentConfig?.getAllOutboundTags()
//            outboundTags?.remove(TAG_DIRECT)

            mDisposable = Observable.interval(3, java.util.concurrent.TimeUnit.SECONDS)
                .subscribe {
                    val queryTime = System.currentTimeMillis()
                    val sinceLastQueryInSeconds = (queryTime - lastQueryTime) / 1000.0
                    var proxyTotal = 0L
                    val text = StringBuilder()
//                    outboundTags?.forEach {
//                        val up = v2rayPoint.queryStats(it, AppConfig.UPLINK)
//                        val down = v2rayPoint.queryStats(it, AppConfig.DOWNLINK)
//                        if (up + down > 0) {
//                            appendSpeedString(
//                                text,
//                                it,
//                                up / sinceLastQueryInSeconds,
//                                down / sinceLastQueryInSeconds
//                            )
//                            proxyTotal += up + down
//                        }
//                    }
//                    val directUplink = v2rayPoint.queryStats(TAG_DIRECT, AppConfig.UPLINK)
//                    val directDownlink = v2rayPoint.queryStats(TAG_DIRECT, AppConfig.DOWNLINK)
//                    val zeroSpeed = proxyTotal == 0L && directUplink == 0L && directDownlink == 0L
//                    if (!zeroSpeed || !lastZeroSpeed) {
//                        if (proxyTotal == 0L) {
//                            appendSpeedString(text, outboundTags?.firstOrNull(), 0.0, 0.0)
//                        }
//                        appendSpeedString(
//                            text, TAG_DIRECT, directUplink / sinceLastQueryInSeconds,
//                            directDownlink / sinceLastQueryInSeconds
//                        )
//                        updateNotification(
//                            text.toString(),
//                            proxyTotal,
//                            directDownlink + directUplink
//                        )
//                    }
//                    lastZeroSpeed = zeroSpeed
                    lastQueryTime = queryTime
                }
        }
    }

    private fun appendSpeedString(text: StringBuilder, name: String?, up: Double, down: Double) {
        var n = name ?: "no tag"
        n = n.substring(0, min(n.length, 6))
        text.append(n)
        for (i in n.length..6 step 2) {
            text.append("\t")
        }
        text.append("•  ${up.toLong().toSpeedString()}↑  ${down.toLong().toSpeedString()}↓\n")
    }

    private fun stopSpeedNotification() {
        mDisposable?.let {
            it.dispose() //stop queryStats
            mDisposable = null
            updateNotification(currentConfig?.remarks, 0, 0)
        }
    }

    fun getLocalizedContext(): Context {
        val locale = Locale(runBlocking {
            appPref.getAllData().language.key
        })
        Locale.setDefault(locale)

        val config = Configuration(baseContext.resources.configuration)
        config.setLocale(locale)
        config.setLayoutDirection(locale)

        return baseContext.createConfigurationContext(config)
    }

    private fun initTrafficTimer() {
        trafficJob = serviceScope.launch(Dispatchers.Default) {
            while (true) {
                currentConfig?.getAllOutboundTags()?.forEach {
                    downloadTraffic += coreController.queryStats(it, AppConfig.DOWNLINK)
                    uploadTraffic += coreController.queryStats(it, AppConfig.UPLINK)
                }
                downloadTraffic += coreController.queryStats(TAG_DIRECT, AppConfig.DOWNLINK)
                uploadTraffic += coreController.queryStats(TAG_DIRECT, AppConfig.UPLINK)

                if (isScreenOn) {
                    updateNotification(
                        downloadTraffic.toTrafficString(),
                        uploadTraffic.toTrafficString()
                    )
                }
                val intent = Intent(AppConfig.BROADCAST_ACTION_ACTIVITY).apply {
                    putExtra("state", State.TRAFFIC.name)
                    putExtras(
                        Bundle().apply {
                            putString("downText", downloadTraffic.toTrafficString())
                            putString("upText", uploadTraffic.toTrafficString())
                        })

                }
                sendBroadcast(intent)
                delay(1000)
            }
        }
    }

//    inner class V2RayCallback() : V2RayVPNServiceSupportsSet {
//        override fun shutdown(): Long {
//            return try {
//                this@V2RayVpnService.stopService()
//                0
//            } catch (e: Exception) {
//                Timber.tag(ANG_PACKAGE).d(e.toString())
//                -1
//            }
//        }
//
//        override fun prepare(): Long {
//            return 0
//        }
//
//        override fun protect(l: Long): Boolean {
//            return this@V2RayVpnService.vpnProtect(l.toInt())
//        }
//
//        override fun onEmitStatus(l: Long, s: String?): Long {
//            return 0
//        }
//
//        override fun setup(s: String): Long {
//            return try {
//                startService()
//                lastQueryTime = System.currentTimeMillis()
//                startSpeedNotification()
//                0
//            } catch (e: Exception) {
//                Timber.tag(ANG_PACKAGE).d(e.toString())
//                -1
//            }
//        }
//    }

    private inner class ReceiveMessageHandler : BroadcastReceiver() {
        override fun onReceive(ctx: Context?, intent: Intent?) {

            val state = intent?.getStringExtra("state")
            Timber.d(state.toString())
            when (state) {
                State.START.name -> startV2rayPoint()
                State.STOP.name -> stopV2Ray()
                State.RESTART.name -> {
                    stopV2Ray()
                    Thread.sleep(500L)
                    startV2rayPoint()
                }

                State.TRAFFIC.name -> {

                }

                State.CHECK.name -> {
                    if (isRunning) MessageUtil.sendMsg2UI(
                        this@V2RayVpnService,
                        AppConfig.MSG_STATE_RESUME_SUCCESS,
                        Pair(elapsedTime, Pair(downloadTraffic, uploadTraffic))
                    )
                }

                State.WIDGET.name -> {
                    if (isRunning) stopV2Ray()
                    else startV2rayPoint()
                }
            }

            when (intent?.getIntExtra("key", 0)) {
                AppConfig.MSG_REGISTER_CLIENT -> {
                    if (coreController.isRunning) {
                        MessageUtil.sendMsg2UI(
                            this@V2RayVpnService,
                            AppConfig.MSG_STATE_START_SUCCESS,
                            Pair(elapsedTime, Pair(downloadTraffic, uploadTraffic))
                        )
                    } else {
                        MessageUtil.sendMsg2UI(
                            this@V2RayVpnService,
                            AppConfig.MSG_STATE_NOT_RUNNING,
                            ""
                        )
                    }
                }

                AppConfig.MSG_UNREGISTER_CLIENT -> {
                    // nothing to do
                }

                AppConfig.MSG_STATE_START -> {
                    // nothing to do
                }

                AppConfig.MSG_STATE_STOP -> {
                    Timber.tag(ANG_PACKAGE).d("Stop Service")
                    stopV2Ray()
                }

                AppConfig.MSG_STATE_RESTART -> {
                    Timber.tag(ANG_PACKAGE).d("Restart Service")
                    stopV2Ray()
                    Thread.sleep(500L)
                    startV2Ray()
                }

                AppConfig.MSG_MEASURE_DELAY -> {
                    measureV2rayDelay()
                }
            }

            when (intent?.action) {
                Intent.ACTION_SCREEN_OFF -> {
                    Timber.tag(ANG_PACKAGE).d("SCREEN_OFF, stop querying stats")
                    stopSpeedNotification()
                    isScreenOn = false
                }

                Intent.ACTION_SCREEN_ON -> {
                    Timber.tag(ANG_PACKAGE).d("SCREEN_ON, start querying stats")
                    startSpeedNotification()
                    isScreenOn = true
                }
            }
        }
    }

}
