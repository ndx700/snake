package com.example.snake

import android.content.Context
import android.graphics.*
import android.os.Build
import android.os.Handler
import android.os.Looper
import android.os.SystemClock
import android.os.VibrationEffect
import android.os.Vibrator
import android.os.VibratorManager
import android.util.AttributeSet
import android.view.Choreographer
import android.view.MotionEvent
import android.view.View
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicLong
import kotlin.math.abs
import kotlin.math.max
import kotlin.math.min
import kotlin.math.sqrt
import kotlin.random.Random

/**
 * SnakeView
 *
 * aiMode = 0 : 手动
 * aiMode = 1 : 正常 AI + Canvas
 * aiMode = 2 : 真正的无棋盘高速强化学习训练
 *
 * 训练模式的原则：
 * 1. 训练线程绝不调用 Canvas / invalidate / Choreographer。
 * 2. 多 worker 并行跑独立局面，减少锁竞争。
 * 3. UI 只约 4 次/秒读取一次统计和轨迹快照。
 * 4. Q 表批量合并、低频保存，避免 SharedPreferences 拖慢 CPU。
 */
class SnakeView @JvmOverloads constructor(
    context: Context, attrs: AttributeSet? = null
) : View(context, attrs) {

    private val cols = 15
    private val rows = 15
    private val ACTIONS = 4
    private val STATE_COUNT = 720
    private val GAMMA = 0.94f

    private data class P(val x: Int, val y: Int)
    private data class Candidate(val d: P, val score: Float, val reason: String, val legal: Boolean)
    private data class Snapshot(
        var strategy: String = "AUTO", var reason: String = "初始化", var danger: Int = 1,
        var region: Int = 1, var spaceRatio: Float = 1f, var tailReachable: Boolean = false,
        var foodReachable: Boolean = false, var foodDistance: Int = -1, var hunger: Int = 0,
        var chosen: P = P(0, 0), var candidates: List<Candidate> = emptyList(),
        var depth: Int = 0, var nodes: Int = 0
    )
    private data class Sim(val body: ArrayDeque<P>, val ate: Boolean)
    private data class Particle(var x: Float, var y: Float, var vx: Float, var vy: Float, var life: Float, val color: Int)
    private data class FloatText(var x: Float, var y: Float, var life: Float, val text: String)

    private val snake = ArrayDeque<P>()
    private val queue = ArrayDeque<P>()
    private val dirs = listOf(P(0, -1), P(0, 1), P(-1, 0), P(1, 0))
    private var dir = P(1, 0)
    private var food = P(5, 5)

    private var score = 0
    private var highScore = 0
    private var money = 0
    private var gameOver = false
    private var running = false
    private var aiMode = 1
    private var forcedStrategy = -1
    private var gameSpeed = 150L
    private var accumulator = 0L
    private var lastFrame = 0L

    private var combo = 0
    private var hunger = 0
    private var deathCause = "无"
    private var lastDeathInfo = ""
    private var ai = Snapshot()

    private var aggression = 1.15f
    private var safetyMargin = 1.10f
    private var shortcutBonus = 0.90f
    private var deathWall = 0
    private var deathSelf = 0
    private var deathTrap = 0
    private var totalGames = 0

    private val q = Array(STATE_COUNT) { FloatArray(ACTIONS) }
    private val n = Array(STATE_COUNT) { IntArray(ACTIONS) }
    private var lastState = -1
    private var lastAction = -1
    private var learningSteps = 0
    private var dirtyLearning = false

    var onScoreChanged: ((Int) -> Unit)? = null
    var onMoneyChanged: ((Int) -> Unit)? = null

    private val prefs = context.getSharedPreferences("snake_prefs", Context.MODE_PRIVATE)
    private val vibrator: Vibrator? =
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S)
            (context.getSystemService(Context.VIBRATOR_MANAGER_SERVICE) as? VibratorManager)?.defaultVibrator
        else {
            @Suppress("DEPRECATION")
            context.getSystemService(Context.VIBRATOR_SERVICE) as? Vibrator
        }

    private var bodyColor = Color.rgb(46, 204, 113)
    private var headColor = Color.rgb(39, 174, 96)
    private var bgColor = Color.BLACK
    private var gridColor = Color.CYAN
    private var rainbowSkin = false
    private val hsv = IntArray(360) { Color.HSVToColor(floatArrayOf(it.toFloat(), 1f, 1f)) }

    private val particles = mutableListOf<Particle>()
    private val floats = mutableListOf<FloatText>()
    private val paint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val text = Paint(Paint.ANTI_ALIAS_FLAG)
    private val panel = Paint(Paint.ANTI_ALIAS_FLAG)
    private val border = Paint(Paint.ANTI_ALIAS_FLAG)
    private val gridPaint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val snakePaint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val headPaint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val foodPaint = Paint(Paint.ANTI_ALIAS_FLAG)
    private var flash = 0f
    private var beamNodes = 0
    private var beamDepthUsed = 0

    // ---------- 高速训练 HUD 数据 ----------
    private var trainer: HeadlessTrainer? = null
    private val uiHandler = Handler(Looper.getMainLooper())
    private var trainingUiDirty = false
    private var trainingLastUiGames = 0L
    private var trainingLastUiTime = 0L
    private var trainingLastUiSpeed = 0L
    private var trainingBest = 0
    private var trainingAvg = 0.0
    private var trainingRecentAvg = 0.0
    private var trainingGames = 0L
    private var trainingLearning = 0L
    private var trainingCurrentScore = 0
    private var trainingCurrentLength = 1
    private var trainingCurrentSteps = 0
    private var trainingFood = 0
    private var trainingStrategy = "AUTO"
    private var trainingStatus = "未启动"
    private var trainingWorkers = 0
    private var trainingElapsed = 0L
    @Volatile private var trainingSnapshot = IntArray(0)
    @Volatile private var trainingSnapshotLength = 0
    @Volatile private var trainingSnapshotFood = -1
    @Volatile private var trainingSnapshotHead = -1
    @Volatile private var trainingSnapshotDir = 3

    private val frame = object : Choreographer.FrameCallback {
        override fun doFrame(ns: Long) {
            if (!running) return
            if (aiMode == 2) {
                invalidate()
                Choreographer.getInstance().postFrameCallback(this)
                return
            }
            if (lastFrame == 0L) lastFrame = ns
            val dt = ((ns - lastFrame) / 1_000_000L).coerceAtMost(100L)
            lastFrame = ns
            accumulator += dt
            while (accumulator >= gameSpeed) {
                updateGame()
                accumulator -= gameSpeed
            }
            updateEffects(dt / 16f)
            invalidate()
            Choreographer.getInstance().postFrameCallback(this)
        }
    }

    private val trainingUiRunnable = object : Runnable {
        override fun run() {
            if (aiMode == 2 && running) {
                refreshTrainingHud()
                uiHandler.postDelayed(this, 250L)
            }
        }
    }

    init {
        highScore = prefs.getInt("high_score", 0)
        money = prefs.getInt("money", 0)
        aggression = prefs.getFloat("learn_aggression", 1.15f).coerceIn(0.65f, 1.45f)
        safetyMargin = prefs.getFloat("learn_safety", 1.10f).coerceIn(0.95f, 2.20f)
        shortcutBonus = prefs.getFloat("learn_shortcut", 0.90f).coerceIn(0.55f, 1.30f)
        deathWall = prefs.getInt("stat_wall", 0)
        deathSelf = prefs.getInt("stat_self", 0)
        deathTrap = prefs.getInt("stat_trap", 0)
        totalGames = prefs.getInt("stat_total", 0)
        for (s in 0 until STATE_COUNT) for (a in 0 until ACTIONS) {
            q[s][a] = prefs.getFloat("q2_${s}_$a", 0f)
            n[s][a] = prefs.getInt("n2_${s}_$a", 0)
        }
        updateCurrentSkin()
        updateCurrentBoard()
        reset()
    }

    fun getAIMode() = aiMode

    fun setAIMode(m: Int) {
        if (m == aiMode) return
        stopHeadlessTraining()
        aiMode = m.coerceIn(0, 2)
        reset()
        if (aiMode == 2 && running) startHeadlessTraining()
    }

    fun startTraining() {
        setAIMode(2)
        if (running) startHeadlessTraining()
    }

    fun stopTraining() {
        if (aiMode == 2) stopHeadlessTraining()
    }

    fun isTraining() = aiMode == 2 && trainer?.isRunning() == true

    fun setForcedStrategy(s: Int) {
        forcedStrategy = s
        trainer?.forcedStrategy = s
        invalidate()
    }

    fun updateCurrentSkin() {
        when (prefs.getString("equipped_skin", "green")) {
            "blue" -> setSnakeColors(Color.rgb(52, 152, 219), Color.rgb(41, 128, 185), false)
            "red" -> setSnakeColors(Color.rgb(231, 76, 60), Color.rgb(192, 57, 43), false)
            "purple" -> setSnakeColors(Color.rgb(155, 89, 182), Color.rgb(142, 68, 173), false)
            "gold" -> setSnakeColors(Color.rgb(241, 196, 15), Color.rgb(243, 156, 18), false)
            "rainbow" -> setSnakeColors(Color.WHITE, Color.WHITE, true)
            else -> setSnakeColors(Color.rgb(46, 204, 113), Color.rgb(39, 174, 96), false)
        }
        invalidate()
    }

    private fun setSnakeColors(body: Int, head: Int, rainbow: Boolean) {
        bodyColor = body; headColor = head; rainbowSkin = rainbow
        snakePaint.color = body; snakePaint.style = Paint.Style.STROKE
        snakePaint.strokeCap = Paint.Cap.ROUND; snakePaint.strokeJoin = Paint.Join.ROUND
        headPaint.color = head
    }

    fun updateCurrentBoard() {
        when (prefs.getString("equipped_board", "dark")) {
            "light" -> { bgColor = Color.rgb(240, 240, 240); gridColor = Color.rgb(200, 200, 200) }
            "neon" -> { bgColor = Color.rgb(10, 25, 47); gridColor = Color.CYAN }
            "forest" -> { bgColor = Color.rgb(27, 46, 26); gridColor = Color.rgb(46, 74, 45) }
            "cyberpunk" -> { bgColor = Color.rgb(43, 15, 59); gridColor = Color.MAGENTA }
            "rainbow_board" -> { bgColor = Color.BLACK; gridColor = Color.WHITE }
            else -> { bgColor = Color.BLACK; gridColor = Color.CYAN }
        }
        invalidate()
    }

    fun reset() {
        if (aiMode == 2) {
            snake.clear(); snake.add(P(cols / 2, rows / 2)); dir = P(1, 0)
            score = 0; combo = 0; hunger = 0; gameOver = false
            deathCause = "无"; lastDeathInfo = ""
            trainingStatus = "等待训练"
            invalidate()
            return
        }
        snake.clear(); queue.clear()
        snake.add(P(cols / 2, rows / 2)); dir = P(1, 0)
        score = 0; combo = 0; hunger = 0; gameOver = false
        deathCause = "无"; lastDeathInfo = ""; gameSpeed = 150L
        accumulator = 0; lastFrame = 0; lastState = -1; lastAction = -1
        beamNodes = 0; beamDepthUsed = 0; particles.clear(); floats.clear(); flash = 0f
        ai = Snapshot(chosen = dir); placeFood()
        onScoreChanged?.invoke(score); invalidate()
    }

    fun resume() {
        if (running) return
        running = true; lastFrame = 0
        if (aiMode == 2) {
            startHeadlessTraining()
            uiHandler.removeCallbacks(trainingUiRunnable)
            uiHandler.post(trainingUiRunnable)
        }
        Choreographer.getInstance().postFrameCallback(frame)
    }

    fun pause() {
        running = false
        Choreographer.getInstance().removeFrameCallback(frame)
        uiHandler.removeCallbacks(trainingUiRunnable)
        if (aiMode == 2) stopHeadlessTraining() else if (dirtyLearning) saveLearning()
    }

    // ==================== 正常游戏 ====================

    private fun updateGame() {
        if (gameOver) return
        if (aiMode != 0) queue.add(chooseMove())
        if (queue.isNotEmpty()) {
            val requested = queue.removeFirst()
            if (!isReverse(requested, dir) && legalDirection(requested)) dir = requested
        }
        if (dir == P(0, 0)) return
        val nh = P(snake.first().x + dir.x, snake.first().y + dir.y)
        if (!inside(nh)) { die("WALL"); return }
        val ate = nh == food
        val body = snake.toList(); val hitIndex = body.indexOf(nh); val tail = snake.last()
        if (hitIndex >= 0 && !(nh == tail && !ate)) {
            val simulated = simulate(nh, dir); val region = freeRegion(simulated.body)
            die(if (region < max(2, (snake.size * safetyMargin).toInt())) "TRAP" else "SELF"); return
        }
        snake.addFirst(nh)
        val reward: Float
        if (ate) {
            score += 10 + min(combo, 20); combo++; hunger = 0; money++
            if (score > highScore) { highScore = score; prefs.edit().putInt("high_score", highScore).apply() }
            onScoreChanged?.invoke(score); onMoneyChanged?.invoke(money)
            prefs.edit().putInt("money", money).apply()
            val region = freeRegion(snake); val ratio = region.toFloat() / max(1, snake.size)
            reward = (when { ratio >= 4f && tailReachable(snake) -> 3.8f; ratio >= 2.8f -> 2.7f; ratio >= 1.8f -> 1.5f; else -> .35f }) + min(combo, 20) * .025f
            spawnFoodEffect(nh); placeFood(); gameSpeed = max(65L, 150L - (snake.size / 8) * 5L)
        } else {
            snake.removeLast(); hunger++; combo = max(0, combo - 1)
            val region = freeRegion(snake); val ratio = region.toFloat() / max(1, snake.size)
            val tail = tailReachable(snake); val mobility = countSafeMoves(snake)
            var r = .025f; if (tail) r += .055f; if (ratio >= 4f) r += .08f; if (mobility >= 3) r += .035f
            if (ratio < 1.5f) r -= .18f; if (mobility <= 1) r -= .30f; if (hunger > 24) r -= .06f; reward = r
        }
        learnTransition(reward, false); stepsSafeSave()
    }

    private fun chooseMove(): P {
        val candidates = dirs.map { evaluate(it) }; val legal = candidates.filter { it.legal }
        if (legal.isEmpty()) return dir
        val danger = calculateDanger(); val state = encodeState(snake, danger); val strategy = selectStrategy(state, danger)
        val scored = when (strategy) { 0 -> legal.maxByOrNull { bfsScore(it) }; 1 -> legal.maxByOrNull { tailScore(it) }; 2 -> legal.maxByOrNull { hamScore(it) }; else -> beamBest(legal, danger) } ?: legal.first()
        val final = if (forcedStrategy >= 0) {
            val fs = if (forcedStrategy == 4) 3 else forcedStrategy.coerceIn(0, 3)
            when (fs) { 0 -> legal.maxByOrNull { bfsScore(it) }; 1 -> legal.maxByOrNull { tailScore(it) }; 2 -> legal.maxByOrNull { hamScore(it) }; else -> beamBest(legal, danger) } ?: scored
        } else scored
        lastState = state; lastAction = strategy
        val region = freeRegion(snake); val foodDist = distance(snake.first(), food, snake, true)
        ai = Snapshot(strategyName(if (forcedStrategy >= 0) if (forcedStrategy == 4) 3 else forcedStrategy else strategy), reasonFor(final, strategy, danger), danger, region, region.toFloat()/max(1,snake.size), tailReachable(snake), foodDist >= 0, foodDist, hunger, final.d, candidates, beamDepthUsed, if(strategy==3) beamNodes else candidates.size)
        return final.d
    }

    private fun evaluate(d: P): Candidate {
        if (!legalDirection(d)) return Candidate(d, -1e9f, "撞墙/身体", false)
        val sim = simulate(snake.first(), d); val region = freeRegion(sim.body); val tail = tailReachable(sim.body)
        val fd = distance(sim.body.first(), food, sim.body, true); val mobility = countSafeMoves(sim.body); val ratio = region.toFloat()/max(1,sim.body.size)
        var s = region*14f + mobility*48f + if(tail)260f else -360f
        if(ratio<1.35f) s-=700f; if(mobility<=1) s-=280f
        if(fd>=0) s += aggression*(if(ratio>=2.8f&&tail)360f else 95f)/(fd+1) else s-=if(hunger>20)180f else 80f
        if(sim.ate) s += when { ratio>=4f&&tail->1000f; ratio>=2.8f->620f; ratio>=1.8f->180f; else->-550f }*aggression.coerceIn(.75f,1.25f)
        val h=sim.body.first(); val edge=min(min(h.x,cols-1-h.x),min(h.y,rows-1-h.y)); s-=max(0,2-edge)*(75f+snake.size*.4f)
        s-=max(0f,snake.size*safetyMargin-region)*42f
        val reason=when{sim.ate&&ratio>=2.8f&&tail->"安全吃食物并保留出口";sim.ate->"食物可得但需要控制风险";tail&&ratio>=3f->"保持尾巴可达并扩大空间";mobility<=1->"避免单出口死路";else->"综合空间、尾巴、食物与长期风险"}
        return Candidate(d,s,reason,true)
    }
    private fun bfsScore(c: Candidate)=c.score+(distance(simulate(snake.first(),c.d).body.first(),food,simulate(snake.first(),c.d).body,true).let{if(it>=0)190f/(it+1) else -80f})
    private fun tailScore(c: Candidate)=c.score+(if(tailReachable(simulate(snake.first(),c.d).body))520f else -720f)
    private fun hamScore(c: Candidate)=c.score+(if(hamIndex(c.d)>=0)150f*shortcutBonus else -100f)

    private fun beamBest(legal: List<Candidate>, danger: Int): Candidate {
        var best=legal.maxByOrNull{it.score}?:legal.first(); var bestScore=-1e30f; beamNodes=0
        val length=snake.size; val maxDepth=when{danger>=5->4;danger==4->5;length>=55->7;else->6}; val width=when{danger>=5->6;danger==4->8;length>=70->10;else->9}; beamDepthUsed=maxDepth
        data class Node(val body:ArrayDeque<P>,val first:P,val score:Float)
        var layer=legal.map{Node(simulate(snake.first(),it.d).body,it.d,it.score)}
        for(depth in 1..maxDepth){if(layer.isEmpty())break;val next=ArrayList<Node>(layer.size*3);for(node in layer){beamNodes++;if(node.score>bestScore){bestScore=node.score;best=legal.firstOrNull{it.d==node.first}?:best};if(depth==maxDepth)continue;val pd=directionOfFirst(node.body);for(d in dirs){if(isReverse(d,pd)||!canSim(node.body,d))continue;val sm=simulateOn(node.body,d);val r=freeRegion(sm.body);val ratio=r.toFloat()/max(1,sm.body.size);val tail=tailReachable(sm.body);val mob=countSafeMoves(sm.body);val fd=distance(sm.body.first(),food,sm.body,true);var sc=node.score+r*7.5f+mob*25f+if(tail)135f else -190f;if(ratio<1.35f)sc-=520f;if(mob<=1)sc-=180f;if(fd>=0)sc+=if(ratio>=2.8f&&tail)125f else 35f;if(fd>=0)sc+=45f/(fd+1);if(sm.ate)sc+=when{ratio>=4f&&tail->650f;ratio>=2.8f->380f;ratio>=1.8f->90f;else->-420f};next.add(Node(sm.body,node.first,sc))}};layer=next.sortedByDescending{it.score}.take(width)};return best
    }

    private fun selectStrategy(state:Int,danger:Int):Int{
        if(forcedStrategy>=0)return if(forcedStrategy==4)3 else forcedStrategy.coerceIn(0,3)
        val priors=floatArrayOf(if(snake.size<30).55f else .25f,if(danger>=4)1.10f else .55f,if(snake.size>=45).85f else .20f,when{danger<=2&&snake.size>=45->1.25f;danger<=3->.95f;else->.50f})
        if(hunger>18)priors[0]+=.35f;if(danger>=4)priors[1]+=.45f
        var best=0;var bv=-1e30f;val total=n[state].sum();val logTerm=kotlin.math.ln((total+2).toFloat())
        for(a in 0 until ACTIONS){val v=n[state][a];val ex=if(v==0)1.35f else .72f*sqrt(logTerm/v);val value=q[state][a]+priors[a]+ex;if(value>bv){bv=value;best=a}};return best
    }

    private fun encodeState(body:ArrayDeque<P>,danger:Int):Int{
        val ls=when{body.size<20->0;body.size<40->1;body.size<70->2;else->3};val d=(danger-1).coerceIn(0,4);val tail=if(tailReachable(body))1 else 0;val ratio=freeRegion(body).toFloat()/max(1,body.size);val sp=when{ratio<1.8f->0;ratio<3.5f->1;else->2};val fd=distance(body.first(),food,body,true);val fs=when{fd<0->0;fd<=5->2;else->1};val hu=if(hunger>=18)1 else 0
        return (((((ls*5+d)*2+tail)*3+sp)*3+fs)*2+hu).coerceIn(0,STATE_COUNT-1)
    }

    private fun learnTransition(reward:Float,terminal:Boolean){if(aiMode==0||lastState !in 0 until STATE_COUNT||lastAction !in 0 until ACTIONS)return;val s=lastState;val a=lastAction;val visits=n[s][a];val alpha=when{visits<8->.28f;visits<30->.16f;visits<100->.085f;else->.035f};val target=if(terminal)reward else reward+GAMMA*(q[encodeState(snake,calculateDanger())].maxOrNull()?:0f);q[s][a]+=alpha*(target-q[s][a]);n[s][a]++;learningSteps++;dirtyLearning=true;if(learningSteps%100==0)saveLearning()}
    private fun stepsSafeSave(){if(dirtyLearning&&learningSteps%100==0)saveLearning()}

    private fun saveLearning(){val e=prefs.edit().putFloat("learn_aggression",aggression).putFloat("learn_safety",safetyMargin).putFloat("learn_shortcut",shortcutBonus).putInt("stat_wall",deathWall).putInt("stat_self",deathSelf).putInt("stat_trap",deathTrap).putInt("stat_total",totalGames).putInt("money",money);for(s in 0 until STATE_COUNT)for(a in 0 until ACTIONS){e.putFloat("q2_${s}_$a",q[s][a]);e.putInt("n2_${s}_$a",n[s][a])};e.apply();dirtyLearning=false}

    private fun die(cause:String){gameOver=true;deathCause=cause;when(cause){"WALL"->deathWall++;"SELF"->deathSelf++;else->deathTrap++};learnTransition(when(cause){"WALL"->-10f;"SELF"->-12f;else->-15f},true);totalGames++;aggression=when(cause){"WALL"->max(.70f,aggression*.985f);"SELF"->max(.70f,aggression*.975f);else->max(.70f,aggression*.955f)};if(cause=="TRAP")safetyMargin=min(2.20f,safetyMargin*1.035f);lastDeathInfo="死亡=$cause  长度=${snake.size}  分数=$score  空间=${ai.region}";saveLearning();flash=1f;invalidate()}
    private fun reasonFor(c:Candidate,strategy:Int,danger:Int)=when{!c.legal->"此方向不合法";danger>=5->"高危局面，优先保命";c.reason=="安全吃食物并保留出口"->"安全吃食物并保留后路";c.reason=="保持尾巴可达并扩大空间"->"保持尾巴出口并扩大空间";c.reason=="避免单出口死路"->"避免进入单出口死路";strategy==3->"BEAM 正在比较未来多步路线";else->"综合空间、尾巴、食物与长期价值"}
    private fun strategyName(s:Int)=when(s){0->"BFS 食物";1->"TAIL 追尾";2->"HAM 路线";3->"BEAM 前瞻";else->"AUTO"}

    private fun simulate(head:P,d:P)=simulateOn(ArrayDeque(snake),d)
    private fun simulateOn(src:ArrayDeque<P>,d:P):Sim{val b=ArrayDeque(src);if(b.isEmpty())return Sim(b,false);val nh=P(b.first().x+d.x,b.first().y+d.y);if(!inside(nh))return Sim(b,false);val ate=nh==food;if(b.contains(nh)&&!(nh==b.last()&&!ate))return Sim(b,false);b.addFirst(nh);if(!ate)b.removeLast();return Sim(b,ate)}
    private fun canSim(body:ArrayDeque<P>,d:P):Boolean{if(body.isEmpty())return false;val h=body.first();val nh=P(h.x+d.x,h.y+d.y);if(!inside(nh))return false;val ate=nh==food;return !body.contains(nh)||(nh==body.last()&&!ate)}
    private fun legalDirection(d:P)=d!=P(0,0)&&!isReverse(d,dir)&&canSim(snake,d)
    private fun isReverse(a:P,b:P)=a.x==-b.x&&a.y==-b.y
    private fun directionOfFirst(body:ArrayDeque<P>):P=if(body.size<2)dir else P(body.elementAt(0).x-body.elementAt(1).x,body.elementAt(0).y-body.elementAt(1).y)
    private fun inside(p:P)=p.x in 0 until cols&&p.y in 0 until rows

    private fun freeRegion(body:ArrayDeque<P>):Int{if(body.isEmpty())return 0;val blocked=HashSet(body);val start=body.first();blocked.remove(start);val seen=HashSet<P>();val qu=ArrayDeque<P>();qu.add(start);seen.add(start);while(qu.isNotEmpty()){val p=qu.removeFirst();for(d in dirs){val n=P(p.x+d.x,p.y+d.y);if(inside(n)&&!blocked.contains(n)&&seen.add(n))qu.add(n)}};return seen.size}
    private fun countSafeMoves(body:ArrayDeque<P>):Int{if(body.isEmpty())return 0;val h=body.first();val bd=directionOfFirst(body);return dirs.count{val nh=P(h.x+it.x,h.y+it.y);inside(nh)&&(!body.contains(nh)||(nh==body.last()&&nh!=food))&&!isReverse(it,bd)}}
    private fun tailReachable(body:ArrayDeque<P>)=body.isNotEmpty()&&distance(body.first(),body.last(),body,true)>=0
    private fun distance(start:P,target:P,body:Collection<P>,allowTail:Boolean):Int{if(start==target)return 0;val blocked=HashSet(body);if(allowTail&&body.isNotEmpty())blocked.remove(body.last());blocked.remove(start);val qq=ArrayDeque<Pair<P,Int>>();val seen=HashSet<P>();qq.add(start to 0);seen.add(start);while(qq.isNotEmpty()){val z=qq.removeFirst();for(d in dirs){val np=P(z.first.x+d.x,z.first.y+d.y);if(np==target)return z.second+1;if(inside(np)&&!blocked.contains(np)&&seen.add(np))qq.add(np to z.second+1)}};return -1}
    private fun calculateDanger():Int{val region=freeRegion(snake);val ratio=region.toFloat()/max(1,snake.size);val mobility=countSafeMoves(snake);return when{mobility<=0->5;ratio<1.5f->5;ratio<2.2f->4;ratio<3.4f->3;ratio<5f->2;else->1}}
    private fun hamIndex(d:P):Int{val h=snake.first();val np=P(h.x+d.x,h.y+d.y);return if(inside(np))np.x*rows+np.y else -1}
    private fun placeFood(){val free=ArrayList<P>();for(x in 0 until cols)for(y in 0 until rows){val p=P(x,y);if(!snake.contains(p))free.add(p)};if(free.isNotEmpty())food=free[Random.nextInt(free.size)]}
    private fun spawnFoodEffect(p:P){repeat(14){particles.add(Particle(p.x.toFloat(),p.y.toFloat(),Random.nextFloat()-.5f,Random.nextFloat()-.5f,1f,Color.YELLOW))};floats.add(FloatText(p.x.toFloat(),p.y.toFloat(),1f,"+10"))}
    private fun updateEffects(dt:Float){flash=max(0f,flash-dt*.035f);particles.forEach{it.x+=it.vx*dt;it.y+=it.vy*dt;it.life-=dt*.035f};particles.removeAll{it.life<=0};floats.forEach{it.y-=dt*.04f;it.life-=dt*.025f};floats.removeAll{it.life<=0}}

    // ==================== 真正的无棋盘训练器 ====================

    private inner class HeadlessTrainer {
        private val runningFlag = AtomicBoolean(false)
        private val stopFlag = AtomicBoolean(false)
        private var executor = Executors.newFixedThreadPool(max(1, Runtime.getRuntime().availableProcessors()))
        private val games = AtomicLong(0)
        private val scoreSum = AtomicLong(0)
        private val recentRing = LongArray(128)
        private var recentPos = 0
        private var recentCount = 0
        private val recentLock = Any()
        private val best = AtomicLong(0)
        private val learn = AtomicLong(0)
        private val startedAt = AtomicLong(0)
        private val workerCount = max(1, Runtime.getRuntime().availableProcessors())
        @Volatile var forcedStrategy = this@SnakeView.forcedStrategy
        private val workers = ArrayList<Worker>()

        fun start() {
            if (!runningFlag.compareAndSet(false, true)) return
            stopFlag.set(false)
            games.set(0); scoreSum.set(0); best.set(0); learn.set(0); startedAt.set(SystemClock.elapsedRealtime())
            workers.clear()
            executor.shutdownNow()
            executor = Executors.newFixedThreadPool(workerCount)
            repeat(workerCount) { i ->
                val w=Worker(i)
                workers.add(w)
                executor.execute { w.loop() }
            }
            trainingWorkers=workerCount; trainingStatus="训练中"
        }

        fun stop() {
            if (!runningFlag.compareAndSet(true, false)) return
            stopFlag.set(true)
            executor.shutdownNow()
            try { executor.awaitTermination(500, TimeUnit.MILLISECONDS) } catch (_: InterruptedException) {}
            mergeAll()
            if (dirtyLearning) saveLearning()
            trainingStatus="已停止"
        }

        fun isRunning()=runningFlag.get()&&!stopFlag.get()
        fun games()=games.get(); fun best()=best.get(); fun learning()=learn.get()
        fun avg()=if(games()==0L)0.0 else scoreSum.get().toDouble()/games()
        fun recentAvg():Double=synchronized(recentLock){if(recentCount==0)0.0 else recentRing.take(recentCount).sum().toDouble()/recentCount}
        fun speed():Long{val ms=max(1L,SystemClock.elapsedRealtime()-startedAt.get());return games()*1000L/ms}

        fun refreshSnapshot(){
            var chosen:Worker?=null;var bestMetric=-1
            for(w in workers){val metric=w.currentScore*1000+w.currentLength*10+w.currentSteps/100;if(metric>bestMetric){bestMetric=metric;chosen=w}}
            if(chosen!=null){chosen.snapshotInto(this@SnakeView)}
        }

        private fun record(score:Int){
            val g=games.incrementAndGet();scoreSum.addAndGet(score.toLong());while (true) { val oldBest=best.get(); if(score.toLong()<=oldBest || best.compareAndSet(oldBest,score.toLong())) break }
            synchronized(recentLock){recentRing[recentPos]=score.toLong();recentPos=(recentPos+1)%recentRing.size;recentCount=min(recentCount+1,recentRing.size)}
            if(g%4096L==0L){mergeAll();saveLearning()}
        }

        private fun mergeAll(){
            synchronized(q){
                for(w in workers)w.mergeInto(q,n)
            }
            dirtyLearning=true
        }

        private inner class Worker(private val id:Int){
            // primitive 状态：避免 ArrayDeque/P/HashSet 的大量对象分配。
            private val board=IntArray(cols*rows)
            private val body=IntArray(cols*rows)
            private val localQ=FloatArray(STATE_COUNT*ACTIONS)
            private val localN=IntArray(STATE_COUNT*ACTIONS)
            private val bfs=IntArray(cols*rows)
            private val seen=BooleanArray(cols*rows)
            private val rng=Random((System.nanoTime().toInt() xor (id * 0x9E3779B9)))
            @Volatile var currentScore=0
            @Volatile var currentLength=1
            @Volatile var currentSteps=0
            @Volatile var currentFood=-1
            @Volatile var currentHead=112
            @Volatile var currentDir=3
            private var len=1
            private var head=112
            private var food=0
            private var direction=3
            private var score=0
            private var hunger=0
            private var lastS=-1
            private var lastA=-1
            private var steps=0
            private var foods=0
            private var episodes=0

            init{ synchronized(q){for(i in localQ.indices)localQ[i]=q[i/ACTIONS][i%ACTIONS];for(i in localN.indices)localN[i]=n[i/ACTIONS][i%ACTIONS]} }

            fun loop(){
                try{
                    while(!stopFlag.get()&&!Thread.currentThread().isInterrupted){runEpisode();episodes++;if(episodes%256==0)mergeInto(q,n)}
                }catch(_:InterruptedException){}finally{mergeInto(q,n)}
            }

            private fun resetEpisode(){
                java.util.Arrays.fill(board,0);len=1;head=112;body[0]=head;board[head]=1;direction=3;score=0;hunger=0;steps=0;foods=0;food=pickFood();lastS=-1;lastA=-1
                publish()
            }

            private fun publish(){
                currentScore=score;currentLength=len;currentSteps=steps;currentFood=food;currentHead=head;currentDir=direction
            }

            private fun runEpisode(){
                resetEpisode()
                var dead=false
                while(!dead&&!stopFlag.get()&&steps<20000){
                    val danger=danger();val state=state(danger);val action=chooseAction(state,danger);lastS=state;lastA=action
                    val next=move(action)
                    val reward=next.first;dead=next.second
                    val nextState=if(dead)0 else state(danger())
                    learn(state,action,reward,dead,nextState)
                    steps++;currentSteps=steps;currentScore=score;currentLength=len
                    if(steps and 63==0)publish()
                }
                currentScore=score;currentLength=len;currentSteps=steps
                record(score)
            }

            private fun chooseAction(state:Int,danger:Int):Int{
                val forced=forcedStrategy
                if(forced>=0)return if(forced==4)3 else forced.coerceIn(0,3)
                val priors=floatArrayOf(if(len<30).55f else .25f,if(danger>=4)1.1f else .55f,if(len>=45).85f else .2f,if(danger<=2&&len>=45)1.25f else if(danger<=3).95f else .5f)
                if(hunger>18)priors[0]+=.35f;if(danger>=4)priors[1]+=.45f
                var bestA=0;var bestV=-1e30f;var total=0
                for(a in 0 until ACTIONS)total+=localN[state*ACTIONS+a]
                val logTerm=kotlin.math.ln((total+2).toFloat())
                for(a in 0 until ACTIONS){val visits=localN[state*ACTIONS+a];val mean=localQ[state*ACTIONS+a];val explore=if(visits==0)1.35f else .72f*sqrt(logTerm/visits);val v=mean+priors[a]+explore;if(v>bestV){bestV=v;bestA=a}}
                return bestA
            }

            // 4个“策略动作”不是方向，而是高速训练版策略选择：每种策略分别挑一个方向。
            private fun move(strategy:Int):Pair<Float,Boolean>{
                val dirs4=intArrayOf(0,1,2,3);var chosen=-1;var best=-1e30f
                for(d in dirs4){if(!legal(d))continue;val sc=when(strategy){0->foodScore(d);1->tailScoreFast(d);2->hamScoreFast(d);else->beamScoreFast(d)};if(sc>best){best=sc;chosen=d}}
                if(chosen<0){return -15f to true}
                val oldHead=head;val nx=oldHead%cols+intArrayOf(0,0,-1,1)[chosen];val ny=oldHead/cols+intArrayOf(-1,1,0,0)[chosen]
                if(nx !in 0 until cols||ny !in 0 until rows)return -12f to true
                val nh=ny*cols+nx;val ate=nh==food;val tail=body[len-1]
                if(board[nh]!=0 && !(nh==tail&&!ate))return -12f to true
                if(!ate)board[tail]=0
                val oldLen=len
                val newLen=if(ate)min(cols*rows,oldLen+1)else oldLen
                for(i in newLen-1 downTo 1)body[i]=body[i-1]
                body[0]=nh;len=newLen;head=nh;board[nh]=1;direction=chosen
                var reward=.025f
                if(ate){score+=10+min(foods,20);foods++;hunger=0;food=pickFood();reward=2.5f+min(foods,20)*.05f}else hunger++
                val r=regionFast();val ratio=r.toFloat()/max(1,len);if(ratio<1.4f)reward-=.15f;if(safeMovesFast()<=1)reward-=.25f
                currentFood=food;currentHead=head;currentDir=direction
                return reward to false
            }

            private fun legal(d:Int):Boolean{
                val rev=(direction==0&&d==1)||(direction==1&&d==0)||(direction==2&&d==3)||(direction==3&&d==2);if(rev)return false
                val x=head%cols+intArrayOf(0,0,-1,1)[d];val y=head/cols+intArrayOf(-1,1,0,0)[d];if(x !in 0 until cols||y !in 0 until rows)return false;val nh=y*cols+x
                return board[nh]==0||nh==body[len-1]
            }

            private fun foodScore(d:Int)=commonScore(d)+if(pathDistance(d)>=0)220f/(pathDistance(d)+1) else -150f
            private fun tailScoreFast(d:Int)=commonScore(d)+(if(tailReachableFast(d))420f else -520f)
            private fun hamScoreFast(d:Int)=commonScore(d)+if((head+d+direction+7)%7>=0)70f else 0f
            private fun beamScoreFast(d:Int):Float{
                var s=commonScore(d);val x=head%cols+intArrayOf(0,0,-1,1)[d];val y=head/cols+intArrayOf(-1,1,0,0)[d];if(x in 0 until cols&&y in 0 until rows){val idx=y*cols+x;s+=regionAfter(d)*5f;if(idx==food)s+=400f}
                return s
            }
            private fun commonScore(d:Int):Float{val r=regionAfter(d);var s=r*12f+safeMovesAfter(d)*38f;if(r<max(8,len))s-=350f;if(safeMovesAfter(d)<=1)s-=250f;return s}

            private fun regionAfter(d:Int):Int{
                val x=head%cols+intArrayOf(0,0,-1,1)[d];val y=head/cols+intArrayOf(-1,1,0,0)[d];if(x !in 0 until cols||y !in 0 until rows)return 0;val nh=y*cols+x
                java.util.Arrays.fill(seen,false);var qs=0;var qe=0;bfs[qe++]=nh;seen[nh]=true;while(qs<qe){val p=bfs[qs++];val px=p%cols;val py=p/cols;for(k in 0..3){val xx=px+intArrayOf(0,0,-1,1)[k];val yy=py+intArrayOf(-1,1,0,0)[k];if(xx !in 0 until cols||yy !in 0 until rows)continue;val ni=yy*cols+xx;if(!seen[ni]&&(board[ni]==0||ni==body[len-1]||ni==nh)){seen[ni]=true;bfs[qe++]=ni}}};return qe
            }
            private fun safeMovesAfter(d:Int):Int{val x=head%cols+intArrayOf(0,0,-1,1)[d];val y=head/cols+intArrayOf(-1,1,0,0)[d];if(x !in 0 until cols||y !in 0 until rows)return 0;return (0..3).count{k->val xx=x+intArrayOf(0,0,-1,1)[k];val yy=y+intArrayOf(-1,1,0,0)[k];xx in 0 until cols&&yy in 0 until rows&&(board[yy*cols+xx]==0||yy*cols+xx==body[len-1])}}
            private fun regionFast():Int{java.util.Arrays.fill(seen,false);var qs=0;var qe=0;bfs[qe++]=head;seen[head]=true;while(qs<qe){val p=bfs[qs++];val x=p%cols;val y=p/cols;for(k in 0..3){val xx=x+intArrayOf(0,0,-1,1)[k];val yy=y+intArrayOf(-1,1,0,0)[k];if(xx !in 0 until cols||yy !in 0 until rows)continue;val ni=yy*cols+xx;if(!seen[ni]&&board[ni]==0){seen[ni]=true;bfs[qe++]=ni}}};return qe}
            private fun safeMovesFast()=(0..3).count{legal(it)}
            private fun pathDistance(d:Int):Int{return -1}
            private fun tailReachableFast(d:Int)=regionAfter(d)>=max(8,len)
            private fun danger():Int{val r=regionFast();val ratio=r.toFloat()/max(1,len);val m=safeMovesFast();return when{m==0->5;ratio<1.5f->5;ratio<2.2f->4;ratio<3.4f->3;ratio<5f->2;else->1}}
            private fun state(d:Int):Int{val ls=when{len<20->0;len<40->1;len<70->2;else->3};val tail=if(tailReachableFast(direction))1 else 0;val ratio=regionFast().toFloat()/max(1,len);val sp=when{ratio<1.8f->0;ratio<3.5f->1;else->2};val foodState=if(food==head)2 else 1;val hu=if(hunger>=18)1 else 0;return (((((ls*5+(d-1).coerceIn(0,4))*2+tail)*3+sp)*3+foodState)*2+hu).coerceIn(0,719)}
            private fun learn(s:Int,a:Int,r:Float,terminal:Boolean,next:Int){val idx=s*ACTIONS+a;val visits=localN[idx];val alpha=when{visits<8->.28f;visits<30->.16f;visits<100->.085f;else->.035f};val target=if(terminal)r else r+GAMMA*maxOf(localQ[next*ACTIONS],localQ[next*ACTIONS+1],localQ[next*ACTIONS+2],localQ[next*ACTIONS+3]);localQ[idx]+=alpha*(target-localQ[idx]);localN[idx]++;learn.incrementAndGet()}

            fun mergeInto(gq:Array<FloatArray>,gn:Array<IntArray>){synchronized(gq){for(s in 0 until STATE_COUNT){for(a in 0 until ACTIONS){val idx=s*ACTIONS+a;val ln=localN[idx];if(ln<=0)continue;val old=gn[s][a];val total=old+ln;gq[s][a]=if(old==0)localQ[idx] else (gq[s][a]*old+localQ[idx]*ln)/total;gn[s][a]=total}}}}

            fun snapshotInto(v:SnakeView){
                v.trainingCurrentScore=currentScore;v.trainingCurrentLength=currentLength;v.trainingCurrentSteps=currentSteps;v.trainingCurrentScore=currentScore;v.trainingFood=foods;v.trainingStrategy=strategyName(if(forcedStrategy==4)3 else if(forcedStrategy>=0)forcedStrategy else 3)
                val copyLen=min(len,cols*rows);v.trainingSnapshot=IntArray(copyLen){body[it]};v.trainingSnapshotLength=copyLen;v.trainingSnapshotFood=food;v.trainingSnapshotHead=head;v.trainingSnapshotDir=direction
            }
            private fun pickFood():Int{var f=rng.nextInt(cols*rows);var tries=0;while(board[f]!=0&&tries++<500)f=rng.nextInt(cols*rows);return f}
        }
    }

    private fun startHeadlessTraining(){if(aiMode!=2)return;if(trainer==null)trainer=HeadlessTrainer();if(trainer?.isRunning()!=true)trainer?.start();trainingStatus="训练中"}
    private fun stopHeadlessTraining(){trainer?.stop();trainer=null;trainingStatus="已停止";refreshTrainingHud()}
    private fun refreshTrainingHud(){val t=trainer?:return;t.refreshSnapshot();trainingGames=t.games();trainingBest=t.best().toInt();trainingAvg=t.avg();trainingRecentAvg=t.recentAvg();trainingLearning=t.learning();trainingLastUiSpeed=t.speed();trainingElapsed=SystemClock.elapsedRealtime();trainingStatus=if(t.isRunning())"训练中" else "已停止";trainingUiDirty=true;invalidate()}

    // ==================== 绘制 ====================

    override fun onSizeChanged(w:Int,h:Int,oldw:Int,oldh:Int){invalidate()}

    override fun onDraw(c:Canvas){super.onDraw(c);if(aiMode==2){drawTrainingHud(c);return};val cell=min(width.toFloat()/cols,height.toFloat()/rows);val ox=(width-cols*cell)/2f;val oy=(height-rows*cell)/2f;c.drawColor(bgColor);gridPaint.color=gridColor;gridPaint.style=Paint.Style.STROKE;gridPaint.strokeWidth=1f;for(i in 0..cols)c.drawLine(ox+i*cell,oy,ox+i*cell,oy+rows*cell,gridPaint);for(i in 0..rows)c.drawLine(ox,oy+i*cell,ox+cols*cell,oy+i*cell,gridPaint);drawFood(c,cell,ox,oy);drawSnake(c,cell,ox,oy);drawParticles(c,cell,ox,oy);drawDebug(c);if(gameOver)drawGameOver(c)}

    private fun drawTrainingHud(c:Canvas){
        c.drawColor(Color.rgb(5,8,12));val pad=16f;val w=width.toFloat();val h=height.toFloat();
        text.textAlign=Paint.Align.LEFT;text.setFakeBoldText(true);text.textSize=21f;text.color=Color.CYAN;c.drawText("⚡ 强化学习 · 极速无棋盘训练",pad,32f,text);text.setFakeBoldText(false);text.textSize=12f;text.color=Color.LTGRAY;c.drawText("训练线程不参与绘制 · HUD 每 250ms 更新",pad,52f,text)
        panel.color=Color.argb(215,18,22,30);c.drawRoundRect(pad,66f,w- pad,min(h-20f,250f),18f,18f,panel);border.color=Color.CYAN;border.style=Paint.Style.STROKE;border.strokeWidth=2f;c.drawRoundRect(pad,66f,w-pad,min(h-20f,250f),18f,18f,border)
        text.textSize=14f;text.color=Color.WHITE
        val x1=pad+14;val y0=94f;val gap=24f
        c.drawText("状态：$trainingStatus",x1,y0,text);c.drawText("线程：$trainingWorkers / ${Runtime.getRuntime().availableProcessors()}",x1,y0+gap,text);c.drawText("训练总局：$trainingGames",x1,y0+gap*2,text);c.drawText("速度：${trainingLastUiSpeed} 局/秒",x1,y0+gap*3,text);c.drawText("总平均：${"%.1f".format(trainingAvg)}",x1,y0+gap*4,text);c.drawText("最近128局：${"%.1f".format(trainingRecentAvg)}",x1,y0+gap*5,text)
        val x2=w/2+10;c.drawText("最高分：$trainingBest",x2,y0,text);c.drawText("当前分：$trainingCurrentScore",x2,y0+gap,text);c.drawText("当前长度：$trainingCurrentLength",x2,y0+gap*2,text);c.drawText("当前步数：$trainingCurrentSteps",x2,y0+gap*3,text);c.drawText("当前策略：$trainingStrategy",x2,y0+gap*4,text);c.drawText("学习更新：$trainingLearning",x2,y0+gap*5,text)

        val top=270f;val boardSize=min(w-32f, h-top-24f);val bx=(w-boardSize)/2f;val by=top;val cc=boardSize/cols
        panel.color=Color.argb(220,0,0,0);c.drawRoundRect(bx-3,by-3,bx+boardSize+3,by+boardSize+3,12f,12f,panel)
        gridPaint.color=Color.rgb(45,55,65);gridPaint.strokeWidth=1f;gridPaint.style=Paint.Style.STROKE;for(i in 0..cols)c.drawLine(bx+i*cc,by,bx+i*cc,by+boardSize,gridPaint);for(i in 0..rows)c.drawLine(bx,by+i*cc,bx+boardSize,by+i*cc,gridPaint)
        val food=trainingSnapshotFood;if(food>=0){foodPaint.color=Color.RED;c.drawCircle(bx+(food%cols+.5f)*cc,by+(food/cols+.5f)*cc,cc*.22f,foodPaint)}
        if(trainingSnapshotLength>0){snakePaint.strokeWidth=max(4f,cc*.58f);snakePaint.style=Paint.Style.STROKE;snakePaint.color=bodyColor;for(i in 0 until trainingSnapshotLength-1){val a=trainingSnapshot[i];val b=trainingSnapshot[i+1];c.drawLine(bx+(a%cols+.5f)*cc,by+(a/cols+.5f)*cc,bx+(b%cols+.5f)*cc,by+(b/cols+.5f)*cc,snakePaint)};val hd=trainingSnapshotHead;if(hd>=0){headPaint.color=headColor;c.drawCircle(bx+(hd%cols+.5f)*cc,by+(hd/cols+.5f)*cc,cc*.34f,headPaint)}}
        text.textSize=11f;text.color=Color.LTGRAY;c.drawText("上图是当前训练线程的实时轨迹快照，不参与训练计算",pad,h-7,text)
    }

    private fun drawFood(c:Canvas,cell:Float,ox:Float,oy:Float){val cx=ox+(food.x+.5f)*cell;val cy=oy+(food.y+.5f)*cell;foodPaint.color=Color.RED;c.drawCircle(cx,cy,cell*.22f,foodPaint)}
    private fun drawSnake(c:Canvas,cell:Float,ox:Float,oy:Float){if(snake.isEmpty())return;snakePaint.strokeWidth=max(8f,cell*.62f);val list=snake.toList();for(i in 0 until list.size-1){val a=list[i];val b=list[i+1];snakePaint.color=if(rainbowSkin)hsv[(i*23+score)%360]else bodyColor;c.drawLine(ox+(a.x+.5f)*cell,oy+(a.y+.5f)*cell,ox+(b.x+.5f)*cell,oy+(b.y+.5f)*cell,snakePaint)};val h=snake.first();headPaint.color=headColor;c.drawCircle(ox+(h.x+.5f)*cell,oy+(h.y+.5f)*cell,cell*.36f,headPaint)}
    private fun drawParticles(c:Canvas,cell:Float,ox:Float,oy:Float){particles.forEach{paint.color=Color.argb((it.life*255).toInt().coerceIn(0,255),Color.red(it.color),Color.green(it.color),Color.blue(it.color));c.drawCircle(ox+(it.x+.5f)*cell,oy+(it.y+.5f)*cell,max(2f,cell*.05f),paint)};text.textAlign=Paint.Align.CENTER;text.textSize=cell*.3f;floats.forEach{text.color=Color.YELLOW;c.drawText(it.text,ox+(it.x+.5f)*cell,oy+(it.y+.3f)*cell,text)}}

    private fun drawDebug(c:Canvas){if(aiMode==0&&!gameOver)return;val w=min(width*.94f,520f);val h=if(gameOver)220f else 205f;val left=width-w-12f;val top=if(gameOver)height-h-12f else 12f;panel.color=Color.argb(205,0,0,0);c.drawRoundRect(left,top,left+w,top+h,18f,18f,panel);border.color=when(ai.danger){1->Color.GREEN;2->Color.rgb(150,255,80);3->Color.YELLOW;4->Color.rgb(255,150,0);else->Color.RED};border.style=Paint.Style.STROKE;border.strokeWidth=3f;c.drawRoundRect(left,top,left+w,top+h,18f,18f,border);text.textAlign=Paint.Align.LEFT;text.setFakeBoldText(true);text.textSize=16f;text.color=Color.WHITE;c.drawText("🧠 AI  ${ai.strategy}",left+12,top+24,text);text.setFakeBoldText(false);text.textSize=12f;text.color=Color.YELLOW;c.drawText("正在判断：${ai.reason}",left+12,top+43,text);text.color=Color.WHITE;c.drawText("危险 ${"●".repeat(ai.danger)}${"○".repeat(5-ai.danger)}   空间 ${ai.region}   比例 ${"%.1f".format(ai.spaceRatio)}",left+12,top+61,text);c.drawText("尾巴 ${if(ai.tailReachable)"✓ 可达" else "✗ 不可达"}   食物 ${if(ai.foodReachable)"✓ 可达" else "✗ 不可达"}   距离 ${if(ai.foodDistance<0)"∞" else ai.foodDistance}",left+12,top+78,text);c.drawText("长度 ${snake.size}   饥饿 $hunger   分数 $score   学习局数 $totalGames",left+12,top+95,text);c.drawText("搜索深度 $beamDepthUsed   节点 $beamNodes   α/攻 ${"%.2f".format(aggression)}",left+12,top+112,text);text.textSize=11f;var x=left+12f;ai.candidates.forEach{val label=when(it.d){P(0,-1)->"↑";P(0,1)->"↓";P(-1,0)->"←";else->"→"};text.color=if(it.legal)Color.WHITE else Color.GRAY;c.drawText("$label ${"%.0f".format(it.score)}",x,top+132,text);x+=w/4f};text.color=Color.CYAN;c.drawText("选择 ${arrow(ai.chosen)}     死亡统计 W$deathWall S$deathSelf T$deathTrap",left+12,top+150,text);text.color=Color.LTGRAY;c.drawText("强化学习：720局面 × 4策略 + 长期Q价值 + 多步BEAM",left+12,top+168,text);if(gameOver){text.color=Color.RED;text.setFakeBoldText(true);text.textSize=15f;c.drawText("死亡原因：$deathCause",left+12,top+190,text);text.setFakeBoldText(false)}}
    private fun drawGameOver(c:Canvas){paint.color=Color.argb(150,0,0,0);c.drawRect(0f,0f,width.toFloat(),height.toFloat(),paint);text.textAlign=Paint.Align.CENTER;text.setFakeBoldText(true);text.textSize=30f;text.color=Color.WHITE;c.drawText("GAME OVER",width/2f,height/2f-45,text);text.setFakeBoldText(false);text.textSize=15f;c.drawText("分数 $score   最高 $highScore   长度 ${snake.size}",width/2f,height/2f-15,text);text.color=Color.YELLOW;c.drawText("点击屏幕重新开始",width/2f,height/2f+20,text);text.color=Color.LTGRAY;text.textSize=11f;c.drawText(lastDeathInfo,width/2f,height/2f+48,text)}
    private fun arrow(p:P)=when(p){P(0,-1)->"↑";P(0,1)->"↓";P(-1,0)->"←";P(1,0)->"→";else->"·"}

    override fun onTouchEvent(e:MotionEvent):Boolean{if(e.action!=MotionEvent.ACTION_UP)return true;if(aiMode==2)return true;if(gameOver){reset();return true};if(aiMode!=0)return true;val cell=min(width.toFloat()/cols,height.toFloat()/rows);val ox=(width-cols*cell)/2f;val oy=(height-rows*cell)/2f;val dx=e.x-(ox+(snake.first().x+.5f)*cell);val dy=e.y-(oy+(snake.first().y+.5f)*cell);val d=if(abs(dx)>abs(dy))P(if(dx>0)1 else -1,0)else P(0,if(dy>0)1 else -1);if(!isReverse(d,dir))queue.add(d);return true}
}
