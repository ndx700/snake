package com.example.snake

import android.content.Context
import android.graphics.*
import android.graphics.drawable.GradientDrawable
import android.view.View
import android.widget.LinearLayout
import android.widget.TextView
import kotlin.math.*

/** Native measured cards + scroll container in Activity; font scaling cannot overlap other cards. */
class SnakeHud(context:Context):LinearLayout(context) {
    private val status=value()
    private val score=value(22f)
    private val learning=value()
    private val decision=value()
    private val causes=value()
    private val curve=Curve(context)
    private val weights=Weights(context)
    private val progress=Progress(context)
    private val donut=Donut(context)
    private fun dp(v:Int)=(v*resources.displayMetrics.density).roundToInt()
    init {
        orientation=VERTICAL;setPadding(dp(10),dp(8),dp(10),dp(16))
        card("运行状态",status)
        val scoreBody=LinearLayout(context).apply {orientation=VERTICAL
            addView(score,LayoutParams(-1,-2));addView(progress,LayoutParams(-1,dp(120))) }
        card("成绩中心",scoreBody)
        card("强化学习",learning)
        card("成绩趋势 · 最近120局",curve)
        card("AI决策",decision)
        card("真实学习参数",weights)
        val deathBody=LinearLayout(context).apply {orientation=VERTICAL
            addView(causes,LayoutParams(-1,-2));addView(donut,LayoutParams(-1,dp(140))) }
        card("结束原因",deathBody)
    }
    private fun value(size:Float=14f)=TextView(context).apply {
        setTextColor(Color.rgb(219,231,244));textSize=size;setLineSpacing(dp(3).toFloat(),1.05f)
        setPadding(0,dp(5),0,dp(5));setTextIsSelectable(true)
    }
    private fun card(title:String,body:View) {
        val c=LinearLayout(context).apply {
            orientation=VERTICAL;setPadding(dp(14),dp(12),dp(14),dp(12))
            background=GradientDrawable().apply {setColor(Color.rgb(16,24,39));cornerRadius=dp(14).toFloat();setStroke(dp(1),Color.rgb(35,56,80))}
        }
        c.addView(TextView(context).apply {text=title;textSize=13f;setTextColor(Color.rgb(80,200,233));typeface=Typeface.DEFAULT_BOLD})
        c.addView(body,LayoutParams(-1,if(body is Curve) dp(170) else if(body is Weights) (dp(430)*max(1f,resources.configuration.fontScale)).roundToInt() else -2))
        addView(c,LayoutParams(-1,-2).apply {bottomMargin=dp(10)})
    }
    fun update(s:SnakeTrainer.Stats,g:SnakeView,model:FloatArray,training:Boolean,high:Int) {
        fun f(v:Float)=String.format(java.util.Locale.getDefault(),"%.1f",v)
        status.text="${if(training) "● 后台训练" else if(g.aiOn) "● 观看AI" else "● 手动游戏"}  ·  ${s.status}\n"+
            "已完成 ${s.games} 局  ·  有效更新 ${s.updates}\n训练 ${f(s.gamesPerMinute)} 局/分钟  ·  ${f(s.stepsPerSecond)} 步/秒"
        score.text=if(training) "当前 ${s.actor.score} · 长度 ${s.actor.length}/225\n最佳 ${s.best}\n近期均分 ${f(s.mean)}\n评测均分 ${f(s.validation)}\n保留模型 ${f(s.championValidation)}" else
            "本局 ${g.game.score}   最高 $high\n长度 ${g.game.length}/${g.game.capacity}"
        learning.text="SARSA(λ) · 16维动作特征\n累计步数 ${s.steps}\n探索率 ${f(s.epsilon*100)}%  ·  完成评测 ${s.evaluations} 次\n"+
            "每64局使用16个固定种子评测；仅晋升成绩更好的模型。\n训练均分含探索，观看AI使用保留模型。"
        decision.text=if(training) "${s.actor.reason}\n饥饿 ${s.actor.hunger}/500  ·  预计可达区域 ${s.actor.region}\n尾巴通路 ${if(s.actor.tailSafe) "可达" else "未确认"}\n安全食物路径 → 展开尾巴路线 → 空间逃生" else "${g.reason}\n饥饿 ${g.game.hunger}/500  ·  可达区域 ${g.region}\n尾巴通路 ${if(g.tailSafe) "可达" else "未确认"}\n"+
            "安全食物路径 → 展开尾巴路线 → 空间逃生\n路径检查负责避险，学习参数调整候选动作。"
        progress.length=if(training) s.actor.length else g.game.length;progress.invalidate()
        donut.values=s.deaths;donut.invalidate()
        val d=s.deaths
        causes.text="撞墙 ${d[0]}  ·  撞身 ${d[1]}\n饥饿 ${d[2]}  ·  吃满 ${d[3]}"
        curve.values=s.history;curve.invalidate();weights.values=if(training && s.learningWeights.size==SnakePolicy.FEATURES) s.learningWeights.toFloatArray() else model;weights.invalidate()
    }
    private class Progress(context:Context):View(context) {
        var length=1
        private val p=Paint(Paint.ANTI_ALIAS_FLAG)
        override fun onDraw(c:Canvas) {
            val r=min(width,height)*0.38f;val x=width/2f;val y=height/2f
            p.style=Paint.Style.STROKE;p.strokeWidth=r*0.14f;p.color=Color.rgb(35,56,80)
            c.drawCircle(x,y,r,p);p.color=Color.rgb(60,218,158)
            c.drawArc(RectF(x-r,y-r,x+r,y+r),-90f,360f*length/225f,false,p)
            p.style=Paint.Style.FILL;p.color=Color.WHITE;p.textAlign=Paint.Align.CENTER;p.textSize=r*0.48f
            c.drawText("${length*100/225}%",x,y+p.textSize*0.35f,p)
        }
    }
    private class Donut(context:Context):View(context) {
        var values:List<Long> = listOf(0,0,0,0)
        private val p=Paint(Paint.ANTI_ALIAS_FLAG)
        override fun onDraw(c:Canvas) {
            val r=min(width,height)*0.38f;val x=width/2f;val y=height/2f
            val colors=intArrayOf(Color.rgb(237,122,90),Color.rgb(192,103,213),Color.rgb(245,187,66),Color.rgb(60,218,158))
            val sum=values.sum().coerceAtLeast(1);var start=-90f
            p.style=Paint.Style.STROKE;p.strokeWidth=r*0.24f;p.color=Color.rgb(35,56,80);c.drawCircle(x,y,r,p)
            for(i in values.indices) {val sweep=360f*values[i]/sum;p.color=colors[i]
                c.drawArc(RectF(x-r,y-r,x+r,y+r),start,sweep,false,p);start+=sweep }
            p.style=Paint.Style.FILL;p.color=Color.WHITE;p.textAlign=Paint.Align.CENTER;p.textSize=r*0.38f
            c.drawText("${values.sum()}局",x,y+p.textSize*0.35f,p)
        }
    }
    private class Curve(context:Context):View(context) {
        var values:List<Int> = emptyList()
        private val p=Paint(Paint.ANTI_ALIAS_FLAG)
        override fun onDraw(c:Canvas) {
            val density=resources.displayMetrics.density;val scaled=resources.displayMetrics.scaledDensity
            val left=min(width*0.25f,56*density);val right=width-8*density
            val top=25*density;val bottom=height-22*density
            if(right<=left || bottom<=top) return
            val maxValue=max(1,values.maxOrNull()?:1).toFloat()
            p.textSize=min(10*scaled,width/28f);p.textAlign=Paint.Align.RIGHT;p.strokeWidth=density
            for(i in 0..3) {
                val y=bottom-(bottom-top)*i/3f;p.color=Color.rgb(35,56,80);c.drawLine(left,y,right,y,p)
                p.color=Color.LTGRAY;c.drawText((maxValue*i/3).toInt().toString(),left-4*density,y+3*density,p)
            }
            p.textAlign=Paint.Align.LEFT
            if(values.isEmpty()) {p.color=Color.LTGRAY;c.drawText("完成训练后显示曲线",left,top,p);return}
            fun draw(avg:Boolean,color:Int) {
                p.color=color;p.style=Paint.Style.STROKE;p.strokeWidth=if(avg) 2*density else density
                val path=Path()
                for(i in values.indices) {
                    val v=if(avg) {val from=max(0,i-4);values.subList(from,i+1).average().toFloat()} else values[i].toFloat()
                    val x=left+(right-left)*i/max(1,values.size-1);val y=bottom-(bottom-top)*v/maxValue
                    if(i==0) path.moveTo(x,y) else path.lineTo(x,y)
                }
                c.drawPath(path,p);p.style=Paint.Style.FILL
            }
            draw(false,Color.rgb(62,121,183));draw(true,Color.rgb(60,218,158))
            p.color=Color.rgb(60,218,158);c.drawText("绿：5局均线    蓝：每局成绩",left,top-6*density,p)
        }
    }
    private class Weights(context:Context):View(context) {
        var values=FloatArray(SnakePolicy.FEATURES)
        private val p=Paint(Paint.ANTI_ALIAS_FLAG)
        private val labels=listOf("偏置","吃食","距离改善","食物路径","空间比例","尾巴通路","可行动作","蛇长","饥饿","重复访问","安全路线","边缘","向上","向右","向下","向左")
        override fun onDraw(c:Canvas) {
            p.textSize=min(11*resources.displayMetrics.scaledDensity,width/30f);p.textAlign=Paint.Align.LEFT
            val labelW=min(width*0.44f,110*resources.displayMetrics.density)
            val end=width-44*resources.displayMetrics.density;val center=(labelW+end)/2f
            val half=max(1f,(end-labelW)/2f);val row=height/17f
            for(i in values.indices) {
                val y=row*(i+1);p.color=Color.LTGRAY
                c.drawText(labels[i],0f,y,p)
                p.color=Color.rgb(35,56,80);c.drawRect(labelW,y-row*0.42f,end,y+row*0.08f,p)
                val delta=values[i].coerceIn(-16f,16f)/16f*half
                p.color=if(delta>=0) Color.rgb(60,218,158) else Color.rgb(237,122,90)
                c.drawRect(min(center,center+delta),y-row*0.42f,max(center,center+delta),y+row*0.08f,p)
                p.textAlign=Paint.Align.RIGHT;p.color=Color.WHITE
                c.drawText(String.format(java.util.Locale.ROOT,"%.2f",values[i]),width.toFloat(),y,p);p.textAlign=Paint.Align.LEFT
            }
        }
    }
}
