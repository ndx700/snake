package com.example.snake

import android.app.Activity
import android.app.AlertDialog
import android.content.Context
import android.content.res.Configuration
import android.graphics.Color
import android.os.*
import android.view.*
import android.widget.*
import java.io.File
import kotlin.math.roundToInt

/** Layout assigns actual space to toolbar, board and HUD; nothing floats over the board. */
class MainActivity:Activity() {
    private lateinit var prefs:android.content.SharedPreferences
    private lateinit var trainer:SnakeTrainer
    private lateinit var game:SnakeView
    private lateinit var hud:SnakeHud
    private lateinit var content:LinearLayout
    private lateinit var scroll:ScrollView
    private lateinit var score:TextView
    private lateinit var trainButton:Button
    private lateinit var manualButton:Button
    private lateinit var aiButton:Button
    private lateinit var pauseButton:Button
    private val handler=Handler(Looper.getMainLooper())
    private var mode=1 // 0 manual, 1 watch, 2 train; foreground only.
    private var resumed=false
    private var fast=false
    companion object { private var crashInstalled=false }
    private val refresh=object:Runnable {
        override fun run() {
            if(!resumed) return
            update();handler.postDelayed(this,250)
        }
    }
    private fun dp(v:Int)=(v*resources.displayMetrics.density).roundToInt()
    override fun onCreate(savedInstanceState:Bundle?) {
        installCrashHandler()
        super.onCreate(savedInstanceState)
        window.addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON)
        prefs=getSharedPreferences("snake_prefs",Context.MODE_PRIVATE)
        mode=savedInstanceState?.getInt("mode")?:prefs.getInt("new_mode",1)
        fast=prefs.getBoolean("fast_training",false)
        trainer=SnakeTrainer.shared(File(filesDir,"snake_rl_sarsa.bin"))
        game=SnakeView(this).apply {modelProvider={trainer.model()}}
        game.restore(savedInstanceState?.getIntArray("game"))
        game.setPaused(savedInstanceState?.getBoolean("paused")?:false)
        game.speedMultiplier=savedInstanceState?.getFloat("speed",1f)?:1f
        hud=SnakeHud(this)
        val root=LinearLayout(this).apply {orientation=LinearLayout.VERTICAL;setBackgroundColor(Color.rgb(7,10,18))}
        // Insets include status/nav bars and display cutout on Android 9+; consumed once at root.
        root.setOnApplyWindowInsetsListener { v,insets ->
            val left:Int;val top:Int;val right:Int;val bottom:Int
            if(Build.VERSION.SDK_INT>=30) {
                val i=insets.getInsets(WindowInsets.Type.systemBars() or WindowInsets.Type.displayCutout())
                left=i.left;top=i.top;right=i.right;bottom=i.bottom
            } else {
                @Suppress("DEPRECATION") val i=insets
                val cut=if(Build.VERSION.SDK_INT>=28) i.displayCutout else null
                @Suppress("DEPRECATION") val l=i.systemWindowInsetLeft
                @Suppress("DEPRECATION") val t=i.systemWindowInsetTop
                @Suppress("DEPRECATION") val r=i.systemWindowInsetRight
                @Suppress("DEPRECATION") val b=i.systemWindowInsetBottom
                left=maxOf(l,cut?.safeInsetLeft?:0);top=maxOf(t,cut?.safeInsetTop?:0)
                right=maxOf(r,cut?.safeInsetRight?:0);bottom=maxOf(b,cut?.safeInsetBottom?:0)
            }
            v.setPadding(left,top,right,bottom);insets
        }
        score=TextView(this).apply {setTextColor(Color.WHITE);textSize=16f;setPadding(dp(12),dp(6),dp(12),dp(4))}
        root.addView(score,LinearLayout.LayoutParams(-1,-2))
        val buttons=LinearLayout(this).apply {orientation=LinearLayout.VERTICAL;setPadding(dp(6),0,dp(6),dp(4))}
        fun row():LinearLayout=LinearLayout(this).apply {orientation=LinearLayout.HORIZONTAL;buttons.addView(this,LinearLayout.LayoutParams(-1,-2))}
        fun button(row:LinearLayout,title:String,action:()->Unit):Button {
            val b=Button(this).apply {text=title;textSize=12f;setTextColor(Color.WHITE);setBackgroundColor(Color.rgb(32,57,78));minWidth=0;minimumWidth=0
                minHeight=dp(48);minimumHeight=dp(48);setPadding(dp(3),dp(6),dp(3),dp(6));setOnClickListener { action() }}
            row.addView(b,LinearLayout.LayoutParams(0,-2,1f).apply {setMargins(dp(2),dp(2),dp(2),dp(2))});return b
        }
        val row1=row()
        manualButton=button(row1,"手动玩") {selectMode(0)}
        aiButton=button(row1,"看AI玩") {selectMode(1)}
        trainButton=button(row1,"训练AI") {selectMode(if(mode==2) 1 else 2)}
        val row2=row()
        pauseButton=button(row2,"暂停") {
            if(mode==2) { if(trainer.stats.active) trainer.stop() else trainer.start(fast) }
            else game.setPaused(!game.paused)
            update()
        }
        button(row2,"重新开始") { if(mode==2) Toast.makeText(this,"训练会自动开始下一局",Toast.LENGTH_SHORT).show() else game.reset() }
        button(row2,"设置") {settings()}
        root.addView(buttons,LinearLayout.LayoutParams(-1,-2))
        content=LinearLayout(this).apply {
            orientation=if(resources.configuration.orientation==Configuration.ORIENTATION_LANDSCAPE) LinearLayout.HORIZONTAL else LinearLayout.VERTICAL
        }
        scroll=ScrollView(this).apply {isFillViewport=false;clipToPadding=true;addView(hud,FrameLayout.LayoutParams(-1,-2))}
        content.addView(game);content.addView(scroll)
        root.addView(content,LinearLayout.LayoutParams(-1,0,1f))
        setContentView(root);root.requestApplyInsets()
        game.onChanged={update()};selectMode(mode)
        val crash=File(filesDir,"last_crash.txt")
        if(crash.exists()) {
            val view=TextView(this).apply {textSize=12f;setPadding(dp(16),dp(12),dp(16),dp(12));text=crash.readText().take(20000);setTextIsSelectable(true)}
            AlertDialog.Builder(this).setTitle("上次崩溃日志").setView(ScrollView(this).apply {addView(view)})
                .setPositiveButton("已阅读") {_,_->crash.delete()}.setNegativeButton("保留",null).show()
        }
    }
    private fun selectMode(newMode:Int) {
        val old=mode;mode=newMode.coerceIn(0,2)
        prefs.edit().putInt("new_mode",mode).apply()
        if(mode==2) {
            game.pause();game.visibility=View.GONE
            if(resumed) trainer.start(fast)
        } else {
            trainer.stop();game.visibility=View.VISIBLE;game.setAI(mode==1)
            if(old==2 && mode==1) game.reset()
            if(resumed) game.resume()
        }
        val landscape=content.orientation==LinearLayout.HORIZONTAL
        game.layoutParams=if(landscape) LinearLayout.LayoutParams(0,-1,1f) else LinearLayout.LayoutParams(-1,0,if(mode==0) 3f else 1.4f)
        scroll.layoutParams=if(landscape) LinearLayout.LayoutParams(0,-1,if(mode==2) 1f else 0.9f) else LinearLayout.LayoutParams(-1,0,1f)
        update()
    }
    private fun update() {
        if(!::hud.isInitialized) return
        val s=trainer.stats
        score.text=if(mode==2) "训练AI · ${s.games}局 · 最佳${s.best}" else "分数 ${game.game.score} · 最高 ${prefs.getInt("high_score",0)}"
        manualButton.setBackgroundColor(if(mode==0) Color.rgb(39,145,102) else Color.rgb(32,57,78))
        aiButton.setBackgroundColor(if(mode==1) Color.rgb(116,75,168) else Color.rgb(32,57,78))
        trainButton.text=if(mode==2) "停止训练" else "训练AI"
        trainButton.setBackgroundColor(if(mode==2) Color.rgb(188,72,60) else Color.rgb(32,57,78))
        pauseButton.text=if(mode==2) if(s.active) "暂停训练" else "继续训练" else if(game.paused) "继续" else "暂停"
        hud.update(s,game,trainer.model(),mode==2,prefs.getInt("high_score",0))
    }
    private fun settings() {
        AlertDialog.Builder(this).setTitle("设置").setItems(arrayOf("训练强度：${if(fast) "高速" else "均衡"}","观看速度","蛇皮肤（免费）","棋盘主题（免费）","音乐 / 音效 / 振动","模型说明")) {_,which ->
            when(which) {
                0->{fast=!fast;trainer.fast=fast;prefs.edit().putBoolean("fast_training",fast).apply();Toast.makeText(this,if(fast) "高速训练" else "均衡训练",Toast.LENGTH_SHORT).show()}
                1->AlertDialog.Builder(this).setTitle("观看速度").setItems(arrayOf("0.5倍","1倍","2倍","4倍","8倍","16倍")) {_,i->game.speedMultiplier=floatArrayOf(.5f,1f,2f,4f,8f,16f)[i]}.show()
                2->chooseTheme("蛇皮肤","equipped_skin",arrayOf("经典绿","海洋蓝","烈焰红","暗夜紫","黄金","RGB神龙"),arrayOf("green","blue","red","purple","gold","rainbow"))
                3->chooseTheme("棋盘主题","equipped_board",arrayOf("经典纯黑","极简白","霓虹蓝","森林绿","赛博朋克","RGB流光"),arrayOf("dark","light","neon","forest","cyberpunk","rainbow_board"))
                4->{val keys=arrayOf("music","sound","vibration");val checked=BooleanArray(3){prefs.getBoolean(keys[it],true)}
                    AlertDialog.Builder(this).setTitle("声音与振动").setMultiChoiceItems(arrayOf("背景音乐","吃食音效","振动"),checked) {_,i,on->prefs.edit().putBoolean(keys[i],on).apply();game.updateAudio()}.setPositiveButton("完成",null).show()}
                5->AlertDialog.Builder(this).setTitle("模型说明").setMessage("训练在后台执行，离开应用会暂停并保存。每64局独立评测，观看AI使用保留模型。新算法不会读取旧版Q表。两万以上是否稳定达成，需要实际训练与评测确认。删除应用可能丢失模型。").setPositiveButton("知道了",null).show()
            }
        }.show()
    }
    private fun chooseTheme(title:String,key:String,names:Array<String>,ids:Array<String>) {
        AlertDialog.Builder(this).setTitle(title).setSingleChoiceItems(names,ids.indexOf(prefs.getString(key,ids[0])).coerceAtLeast(0)) {d,i->prefs.edit().putString(key,ids[i]).apply();game.invalidate();d.dismiss()}.show()
    }
    override fun onResume() {
        super.onResume();resumed=true
        if(mode==2) trainer.start(fast) else game.resume()
        handler.post(refresh)
    }
    override fun onPause() {
        resumed=false;handler.removeCallbacks(refresh);game.pause();trainer.stop();super.onPause()
    }
    override fun onSaveInstanceState(out:Bundle) {
        out.putInt("mode",mode);out.putBoolean("paused",game.paused);out.putFloat("speed",game.speedMultiplier);out.putIntArray("game",game.game.saveState());super.onSaveInstanceState(out)
    }
    override fun onDestroy() {handler.removeCallbacksAndMessages(null);game.dispose();trainer.stop();super.onDestroy()}
    private fun installCrashHandler() {
        if(crashInstalled) return
        crashInstalled=true
        val previous=Thread.getDefaultUncaughtExceptionHandler();val app=applicationContext
        Thread.setDefaultUncaughtExceptionHandler {thread,error ->
            try {File(app.filesDir,"last_crash.txt").writeText("${java.util.Date()}\n线程 ${thread.name}\n${error.stackTraceToString()}")} catch(_:Exception) {}
            previous?.uncaughtException(thread,error)
        }
    }
}
