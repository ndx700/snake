package com.example.snake

import android.content.Context
import android.graphics.*
import android.media.ToneGenerator
import android.media.AudioManager
import android.os.*
import android.util.AttributeSet
import android.view.*
import java.util.concurrent.Executors
import kotlin.math.*

/** Board only: no diagnostic cards are ever drawn over the playing area. */
class SnakeView @JvmOverloads constructor(context: Context,attrs: AttributeSet?=null): View(context,attrs) {
    val game=SnakeEngine()
    var onChanged: (() -> Unit)?=null
    var modelProvider: () -> FloatArray = { FloatArray(SnakePolicy.FEATURES) }
    var aiOn=true; private set
    var paused=false; private set
    var speedMultiplier=1f
    var reason="准备开始"; private set
    var region=0; private set
    var tailSafe=false; private set
    private val prefs=context.getSharedPreferences("snake_prefs",Context.MODE_PRIVATE)
    private val paint=Paint(Paint.ANTI_ALIAS_FLAG)
    private var cell=0f; private var ox=0f; private var oy=0f
    private var running=false; private var disposed=false; private var tick=0L
    private var revision=0L; private var thinking=false
    private var ready: SnakePolicy.Choice?=null
    private val pool=Executors.newSingleThreadExecutor { r -> Thread(r,"Snake-Viewer") }
    private val copy=SnakeEngine(seed=1); private val policy=SnakePolicy(copy)
    private val turns=java.util.ArrayDeque<Int>()
    private var sx=0f; private var sy=0f
    private var tone: ToneGenerator?=null
    private val bgm=BgmPlayer()
    private val handler=Handler(Looper.getMainLooper())
    private data class Spark(var x:Float,var y:Float,val vx:Float,val vy:Float,var life:Float)
    private val sparks=ArrayList<Spark>()
    private var lastDraw=0L
    private var gain=0;private var gainTime=0L
    private val frame=object: Choreographer.FrameCallback {
        override fun doFrame(time:Long) {
            if(!running || disposed) return
            val now=time/1_000_000L
            if(!paused && !game.ended) {
                if(aiOn && ready==null && !thinking) requestChoice()
                if(tick==0L) tick=now
                val duration=(game.speedMs/speedMultiplier.coerceIn(0.5f,16f)).toLong().coerceAtLeast(8)
                if(now-tick>=duration && (!aiOn || ready!=null)) {
                    val choice=ready
                    if(choice!=null) { reason=choice.reason;region=choice.region;tailSafe=choice.tailSafe }
                    val action=if(aiOn) choice!!.action else if(turns.isEmpty()) game.direction else turns.removeFirst()
                    ready=null; val result=game.step(action); revision++; tick=now
                    if(result>0) {
                        effect(result)
                        if(game.score>prefs.getInt("high_score",0)) prefs.edit().putInt("high_score",game.score).apply()
                    }
                    if(game.ended) {
                        reason=when(game.cause) { "WIN"->"棋盘已吃满";"HUNGER"->"饥饿超时";"WALL"->"撞墙";else->"撞到身体" }
                        if(game.score>prefs.getInt("high_score",0)) prefs.edit().putInt("high_score",game.score).apply()
                        if(prefs.getBoolean("vibration",true)) vibrate(90)
                        if(aiOn) { val endRevision=revision
                            handler.postDelayed({ if(revision==endRevision && running && aiOn && !paused && game.ended) reset() },1200)
                        }
                    }
                    onChanged?.invoke()
                }
            }
            invalidate(); Choreographer.getInstance().postFrameCallback(this)
        }
    }
    private fun requestChoice() {
        thinking=true; val token=revision; val state=game.saveState(); val weights=modelProvider()
        pool.execute {
            val result=try { if(copy.restoreState(state)) policy.choose(weights) else null } catch(_: Exception) { null }
            handler.post {
                thinking=false
                if(!disposed && revision==token && aiOn) ready=result
            }
        }
    }
    fun setAI(on:Boolean) { aiOn=on;revision++;ready=null;turns.clear();reason=if(on) "AI接管" else "滑动或点击控制"; onChanged?.invoke() }
    fun setPaused(value:Boolean) { paused=value;tick=0L;updateAudio();onChanged?.invoke() }
    fun reset() { revision++;ready=null;turns.clear();game.reset();tick=0L;reason="新一局";sparks.clear();onChanged?.invoke();invalidate() }
    fun resume() {
        if(running || disposed) return
        running=true;tick=0L;updateAudio();Choreographer.getInstance().postFrameCallback(frame)
    }
    fun pause() { running=false;bgm.stop();Choreographer.getInstance().removeFrameCallback(frame) }
    fun updateAudio() {
        if(running && !paused && prefs.getBoolean("music",true)) bgm.start() else bgm.stop()
    }
    fun restore(state:IntArray?) { if(state!=null && game.restoreState(state)) { revision++;ready=null;invalidate() } }
    private fun vibrate(ms:Long) {
        try {
            val v=if(Build.VERSION.SDK_INT>=31) (context.getSystemService(Context.VIBRATOR_MANAGER_SERVICE) as VibratorManager).defaultVibrator
                else @Suppress("DEPRECATION") (context.getSystemService(Context.VIBRATOR_SERVICE) as Vibrator)
            v.vibrate(VibrationEffect.createOneShot(ms,VibrationEffect.DEFAULT_AMPLITUDE))
        } catch(_: Exception) {}
    }
    private fun effect(value:Int) {
        gain=value;gainTime=SystemClock.uptimeMillis()
        repeat(14) { sparks.add(Spark(game.head%game.cols+0.5f,game.head/game.cols+0.5f,
            kotlin.random.Random.nextFloat()*2-1,kotlin.random.Random.nextFloat()*2-1,1f)) }
        if(prefs.getBoolean("vibration",true)) vibrate(18)
        if(prefs.getBoolean("sound",true)) try {
            if(tone==null) tone=ToneGenerator(AudioManager.STREAM_MUSIC,35)
            tone?.startTone(ToneGenerator.TONE_PROP_BEEP,50)
        } catch(_: Exception) {}
    }
    override fun onSizeChanged(w:Int,h:Int,ow:Int,oh:Int) {
        cell=min((w-paddingLeft-paddingRight).toFloat()/game.cols,(h-paddingTop-paddingBottom).toFloat()/game.rows).coerceAtLeast(0f)
        ox=paddingLeft+(w-paddingLeft-paddingRight-cell*game.cols)/2f
        oy=paddingTop+(h-paddingTop-paddingBottom-cell*game.rows)/2f
    }
    private fun color():Int=when(prefs.getString("equipped_skin","green")) {
        "blue"->Color.rgb(52,152,219);"red"->Color.rgb(231,76,60);"purple"->Color.rgb(155,89,182)
        "gold"->Color.rgb(241,196,15);else->Color.rgb(46,204,113)
    }
    override fun onDraw(c:Canvas) {
        val board=prefs.getString("equipped_board","dark")
        val bg=when(board) { "light"->Color.rgb(240,240,240);"neon"->Color.rgb(10,25,47);"forest"->Color.rgb(27,46,26);"cyberpunk"->Color.rgb(43,15,59);else->Color.BLACK }
        c.drawColor(bg)
        val now=SystemClock.uptimeMillis();val dt=if(lastDraw==0L) 0f else ((now-lastDraw)/1000f).coerceAtMost(0.05f);lastDraw=now
        paint.style=Paint.Style.STROKE;paint.strokeWidth=resources.displayMetrics.density*0.5f
        paint.color=when(board) { "light"->Color.LTGRAY;"forest"->Color.rgb(46,74,45);"cyberpunk"->Color.MAGENTA;else->Color.rgb(20,65,85) }
        if(board=="rainbow_board") paint.color=Color.HSVToColor(floatArrayOf((now/40%360).toFloat(),0.6f,0.7f))
        for(i in 0..game.cols) c.drawLine(ox+i*cell,oy,ox+i*cell,oy+game.rows*cell,paint)
        for(i in 0..game.rows) c.drawLine(ox,oy+i*cell,ox+game.cols*cell,oy+i*cell,paint)
        paint.style=Paint.Style.FILL
        if(game.food>=0) {
            val x=ox+(game.food%game.cols+0.5f)*cell;val y=oy+(game.food/game.cols+0.5f)*cell
            paint.color=Color.argb(90,255,80,80);c.drawCircle(x,y,cell*0.38f,paint)
            paint.color=Color.RED;c.drawCircle(x,y,cell*0.22f,paint);paint.color=Color.WHITE;c.drawCircle(x,y,cell*0.07f,paint)
        }
        paint.strokeWidth=cell*0.62f;paint.strokeCap=Paint.Cap.ROUND
        for(i in game.length-1 downTo 0) {
            val a=game.cellAt(i);paint.color=if(prefs.getString("equipped_skin","green")=="rainbow")
                Color.HSVToColor(floatArrayOf(((i*23+now/40)%360).toFloat(),0.8f,0.95f)) else color()
            val x=ox+(a%game.cols+0.5f)*cell;val y=oy+(a/game.cols+0.5f)*cell
            if(i>0) { val b=game.cellAt(i-1);c.drawLine(x,y,ox+(b%game.cols+0.5f)*cell,oy+(b/game.cols+0.5f)*cell,paint) }
            c.drawCircle(x,y,cell*(if(i==0) 0.36f else 0.30f),paint)
        }
        val hx=ox+(game.head%game.cols+0.5f)*cell;val hy=oy+(game.head/game.cols+0.5f)*cell
        val dx=when(game.direction) {1->0.12f;3->-0.12f;else->0f};val dy=when(game.direction) {2->0.12f;0->-0.12f;else->0f}
        paint.color=Color.WHITE;c.drawCircle(hx+cell*(0.13f+dx),hy+cell*(0.13f+dy),cell*0.075f,paint)
        c.drawCircle(hx-cell*(0.13f-dx),hy-cell*(0.13f-dy),cell*0.075f,paint)
        sparks.forEach { if(!paused) {it.x+=it.vx*dt*3;it.y+=it.vy*dt*3;it.life-=dt*1.5f}
            paint.color=Color.argb((it.life*255).toInt().coerceIn(0,255),255,220,0)
            c.drawCircle(ox+it.x*cell,oy+it.y*cell,cell*0.05f,paint) }
        sparks.removeAll { it.life<=0 }
        if(now-gainTime<650 && gain>0) { paint.color=Color.YELLOW;paint.textSize=cell*0.5f;paint.textAlign=Paint.Align.CENTER;c.drawText("+$gain",hx,hy-cell,paint) }
        if(game.ended || paused) {
            paint.color=Color.argb(175,0,0,0);c.drawRect(ox,oy,ox+game.cols*cell,oy+game.rows*cell,paint)
            paint.color=Color.WHITE;paint.textAlign=Paint.Align.CENTER;paint.textSize=min(cell*1.1f,24*resources.displayMetrics.scaledDensity)
            c.drawText(if(paused) "已暂停" else if(game.cause=="WIN") "棋盘已吃满！" else "本局结束",width/2f,height/2f,paint)
            paint.textSize=min(cell*0.6f,14*resources.displayMetrics.scaledDensity)
            c.drawText(if(paused) "点继续按钮恢复" else "分数 ${game.score} · 点击重开",width/2f,height/2f+cell*1.4f,paint)
        }
    }
    override fun performClick():Boolean { super.performClick();return true }
    override fun onTouchEvent(e:MotionEvent):Boolean {
        when(e.actionMasked) {
            MotionEvent.ACTION_DOWN->{sx=e.x;sy=e.y;return true}
            MotionEvent.ACTION_UP->{
                performClick();if(game.ended) {reset();return true};if(aiOn || paused) return true
                var dx=e.x-sx;var dy=e.y-sy
                if(max(abs(dx),abs(dy))<16*resources.displayMetrics.density) { dx=e.x-(ox+(game.head%game.cols+0.5f)*cell);dy=e.y-(oy+(game.head/game.cols+0.5f)*cell) }
                val a=if(abs(dx)>abs(dy)) if(dx>0) 1 else 3 else if(dy>0) 2 else 0
                val prev=turns.peekLast()?:game.direction
                if(a!=(prev+2)%4 && turns.size<2) turns.addLast(a)
                return true
            }
            MotionEvent.ACTION_CANCEL->return true
        }
        return true
    }
    fun dispose() {
        if(disposed) return
        pause();disposed=true;revision++;handler.removeCallbacksAndMessages(null);pool.shutdownNow()
        tone?.release();tone=null;bgm.stop()
    }
    override fun onDetachedFromWindow() { dispose();super.onDetachedFromWindow() }
}
