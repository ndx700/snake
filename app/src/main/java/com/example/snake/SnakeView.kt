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
import java.util.ArrayDeque
import java.util.Arrays
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.atomic.AtomicLong
import kotlin.math.abs
import kotlin.math.max
import kotlin.math.min
import kotlin.math.sqrt
import kotlin.random.Random

class SnakeView @JvmOverloads constructor(
    context: Context, attrs: AttributeSet? = null
) : View(context, attrs) {

    private val cols = 15
    private val rows = 15
    private val cells = cols * rows
    private val actions = 4
    private val stateCount = 720
    private val gamma = 0.94f

    private data class P(val x: Int, val y: Int)
    private data class Candidate(val d: P, val score: Float, val legal: Boolean, val reason: String)
    private data class Sim(val body: ArrayDeque<P>, val ate: Boolean)

    private val dirs = arrayOf(P(0, -1), P(0, 1), P(-1, 0), P(1, 0))
    private val snake = ArrayDeque<P>()
    private val inputQueue = ArrayDeque<P>()
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
    private var hunger = 0
    private var combo = 0
    private var deathCause = "无"
    private var totalGames = 0
    private var deathWall = 0
    private var deathSelf = 0
    private var deathTrap = 0
    private var aggression = 1.15f
    private var safetyMargin = 1.10f
    private var shortcutBonus = 0.90f

    private val q = Array(stateCount) { FloatArray(actions) }
    private val n = Array(stateCount) { IntArray(actions) }
    private var lastState = -1
    private var lastAction = -1
    private var learningSteps = 0L
    private var dirtyLearning = false

    var onScoreChanged: ((Int) -> Unit)? = null
    var onMoneyChanged: ((Int) -> Unit)? = null

    private val prefs = context.getSharedPreferences("snake_prefs", Context.MODE_PRIVATE)
    private val vibrator: Vibrator? = if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
        (context.getSystemService(Context.VIBRATOR_MANAGER_SERVICE) as? VibratorManager)?.defaultVibrator
    } else {
        @Suppress("DEPRECATION")
        context.getSystemService(Context.VIBRATOR_SERVICE) as? Vibrator
    }

    private var bodyColor = Color.rgb(46, 204, 113)
    private var headColor = Color.rgb(39, 174, 96)
    private var bgColor = Color.BLACK
    private var gridColor = Color.CYAN
    private var rainbowSkin = false
    private val hsv = IntArray(360) { Color.HSVToColor(floatArrayOf(it.toFloat(), 1f, 1f)) }

    private val paint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val text = Paint(Paint.ANTI_ALIAS_FLAG)
    private val panel = Paint(Paint.ANTI_ALIAS_FLAG)
    private val border = Paint(Paint.ANTI_ALIAS_FLAG)
    private val gridPaint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val snakePaint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val headPaint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val foodPaint = Paint(Paint.ANTI_ALIAS_FLAG)

    private var aiStrategy = "AUTO"
    private var aiReason = "初始化"
    private var aiDanger = 1
    private var aiRegion = 1
    private var aiTail = false
    private var aiFoodDistance = -1
    private var beamNodes = 0
    private var beamDepth = 0

    // Training HUD
    private var trainer: HeadlessTrainer? = null
    private val uiHandler = Handler(Looper.getMainLooper())
    private val trainingRunnable = object : Runnable {
        override fun run() {
            if (aiMode == 2 && running) {
                refreshTrainingHud()
                uiHandler.postDelayed(this, 300L)
            }
        }
    }
    private var trainingStatus = "未启动"
    private var trainingWorkers = 0
    private var trainingGames = 0L
    private var trainingBest = 0
    private var trainingAvg = 0.0
    private var trainingRecentAvg = 0.0
    private var trainingSpeed = 0L
    private var trainingLearning = 0L
    private var trainingCurrentScore = 0
    private var trainingCurrentLength = 1
    private var trainingCurrentSteps = 0
    @Volatile private var trainingSnapshot = IntArray(0)
    @Volatile private var trainingSnapshotLength = 0
    @Volatile private var trainingSnapshotFood = -1
    @Volatile private var trainingSnapshotHead = -1

    private val frame = object : Choreographer.FrameCallback {
        override fun doFrame(ns: Long) {
            if (!running || aiMode == 2) return
            if (lastFrame == 0L) lastFrame = ns
            val dt = ((ns - lastFrame) / 1_000_000L).coerceAtMost(100L)
            lastFrame = ns
            accumulator += dt
            while (accumulator >= gameSpeed) {
                updateGame()
                accumulator -= gameSpeed
            }
            invalidate()
            Choreographer.getInstance().postFrameCallback(this)
        }
    }

    init {
        highScore = prefs.getInt("high_score", 0)
        money = prefs.getInt("money", 0)
        aggression = prefs.getFloat("learn_aggression", 1.15f).coerceIn(.65f, 1.45f)
        safetyMargin = prefs.getFloat("learn_safety", 1.10f).coerceIn(.95f, 2.2f)
        shortcutBonus = prefs.getFloat("learn_shortcut", .90f).coerceIn(.55f, 1.30f)
        deathWall = prefs.getInt("stat_wall", 0)
        deathSelf = prefs.getInt("stat_self", 0)
        deathTrap = prefs.getInt("stat_trap", 0)
        totalGames = prefs.getInt("stat_total", 0)
        for (s in 0 until stateCount) for (a in 0 until actions) {
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
        if (aiMode == 2) stopHeadlessTraining()
        aiMode = m.coerceIn(0, 2)
        reset()
        if (aiMode == 2 && running) startHeadlessTraining()
    }

    fun startTraining() {
        aiMode = 2
        reset()
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
            "blue" -> setSnakeColors(Color.rgb(52,152,219), Color.rgb(41,128,185), false)
            "red" -> setSnakeColors(Color.rgb(231,76,60), Color.rgb(192,57,43), false)
            "purple" -> setSnakeColors(Color.rgb(155,89,182), Color.rgb(142,68,173), false)
            "gold" -> setSnakeColors(Color.rgb(241,196,15), Color.rgb(243,156,18), false)
            "rainbow" -> setSnakeColors(Color.WHITE, Color.WHITE, true)
            else -> setSnakeColors(Color.rgb(46,204,113), Color.rgb(39,174,96), false)
        }
        invalidate()
    }

    private fun setSnakeColors(body: Int, head: Int, rainbow: Boolean) {
        bodyColor = body
        headColor = head
        rainbowSkin = rainbow
        snakePaint.style = Paint.Style.STROKE
        snakePaint.strokeCap = Paint.Cap.ROUND
        snakePaint.strokeJoin = Paint.Join.ROUND
        headPaint.color = head
    }

    fun updateCurrentBoard() {
        when (prefs.getString("equipped_board", "dark")) {
            "light" -> { bgColor = Color.rgb(240,240,240); gridColor = Color.rgb(200,200,200) }
            "neon" -> { bgColor = Color.rgb(10,25,47); gridColor = Color.CYAN }
            "forest" -> { bgColor = Color.rgb(27,46,26); gridColor = Color.rgb(46,74,45) }
            "cyberpunk" -> { bgColor = Color.rgb(43,15,59); gridColor = Color.MAGENTA }
            "rainbow_board" -> { bgColor = Color.BLACK; gridColor = Color.WHITE }
            else -> { bgColor = Color.BLACK; gridColor = Color.CYAN }
        }
        invalidate()
    }

    fun reset() {
        if (aiMode == 2) {
            snake.clear()
            snake.add(P(cols / 2, rows / 2))
            dir = P(1, 0)
            score = 0
            hunger = 0
            combo = 0
            gameOver = false
            trainingStatus = "等待训练"
            invalidate()
            return
        }
        snake.clear()
        inputQueue.clear()
        snake.add(P(cols / 2, rows / 2))
        dir = P(1, 0)
        score = 0
        hunger = 0
        combo = 0
        gameOver = false
        deathCause = "无"
        gameSpeed = 150L
        accumulator = 0L
        lastFrame = 0L
        lastState = -1
        lastAction = -1
        beamNodes = 0
        beamDepth = 0
        placeFood()
        onScoreChanged?.invoke(score)
        invalidate()
    }

    fun resume() {
        if (running) return
        running = true
        lastFrame = 0L
        if (aiMode == 2) {
            startHeadlessTraining()
            uiHandler.removeCallbacks(trainingRunnable)
            uiHandler.post(trainingRunnable)
        } else {
            Choreographer.getInstance().postFrameCallback(frame)
        }
    }

    fun pause() {
        running = false
        Choreographer.getInstance().removeFrameCallback(frame)
        uiHandler.removeCallbacks(trainingRunnable)
        if (aiMode == 2) stopHeadlessTraining() else if (dirtyLearning) saveLearning()
    }

    private fun updateGame() {
        if (gameOver) return
        val requested = if (aiMode != 0) chooseMove() else if (inputQueue.isNotEmpty()) inputQueue.removeFirst() else dir
        if (!isReverse(requested, dir) && canMove(requested)) dir = requested
        val nh = P(snake.first().x + dir.x, snake.first().y + dir.y)
        if (!inside(nh)) { die("WALL"); return }
        val ate = nh == food
        if (snake.contains(nh) && !(nh == snake.last() && !ate)) { die("SELF"); return }
        snake.addFirst(nh)
        if (ate) {
            score += 10 + min(combo, 20)
            combo++
            hunger = 0
            money++
            if (score > highScore) {
                highScore = score
                prefs.edit().putInt("high_score", highScore).apply()
            }
            onScoreChanged?.invoke(score)
            onMoneyChanged?.invoke(money)
            prefs.edit().putInt("money", money).apply()
            placeFood()
            gameSpeed = max(65L, 150L - (snake.size / 8) * 5L)
        } else {
            snake.removeLast()
            hunger++
            combo = max(0, combo - 1)
        }
        learnTransition(if (ate) 2.5f else .03f, false)
    }

    private fun chooseMove(): P {
        val danger = calculateDanger(snake)
        val state = encodeState(snake, danger)
        val strategy = if (forcedStrategy >= 0) {
            if (forcedStrategy == 4) 3 else forcedStrategy.coerceIn(0, 3)
        } else selectStrategy(state, danger)
        val candidates = dirs.map { evaluate(it) }.filter { it.legal }
        if (candidates.isEmpty()) return dir
        val chosen = when (strategy) {
            0 -> candidates.maxByOrNull { bfsScore(it) }
            1 -> candidates.maxByOrNull { tailScore(it) }
            2 -> candidates.maxByOrNull { hamScore(it) }
            else -> beamBest(candidates, danger)
        } ?: candidates.first()
        aiStrategy = strategyName(strategy)
        aiReason = chosen.reason
        aiDanger = danger
        aiRegion = freeRegion(snake)
        aiTail = tailReachable(snake)
        aiFoodDistance = distance(snake.first(), food, snake)
        lastState = state
        lastAction = strategy
        return chosen.d
    }

    private fun evaluate(d: P): Candidate {
        if (!canMove(d)) return Candidate(d, -1e9f, false, "非法")
        val sim = simulate(d)
        val region = freeRegion(sim.body)
        val tail = tailReachable(sim.body)
        val mobility = countSafeMoves(sim.body)
        val fd = distance(sim.body.first(), food, sim.body)
        val ratio = region.toFloat() / max(1, sim.body.size)
        var s = region * 14f + mobility * 48f + if (tail) 260f else -360f
        if (ratio < 1.35f) s -= 700f
        if (mobility <= 1) s -= 280f
        if (fd >= 0) s += aggression * 300f / (fd + 1) else s -= 100f
        if (sim.ate) s += if (ratio >= 2.8f && tail) 800f else -350f
        return Candidate(d, s, true, when {
            sim.ate && tail -> "吃食物并保留尾巴出口"
            mobility <= 1 -> "避免单出口"
            tail && ratio >= 3f -> "扩大安全空间"
            else -> "综合空间、食物与长期价值"
        })
    }

    private fun bfsScore(c: Candidate): Float {
        val sim = simulate(c.d)
        val d = distance(sim.body.first(), food, sim.body)
        return c.score + if (d >= 0) 190f / (d + 1) else -80f
    }

    private fun tailScore(c: Candidate): Float {
        return c.score + if (tailReachable(simulate(c.d).body)) 520f else -720f
    }

    private fun hamScore(c: Candidate): Float {
        val p = simulate(c.d).body.first()
        val idx = p.y * cols + p.x
        val parity = (p.x + p.y) and 1
        return c.score + if ((idx and 1) == parity) 120f * shortcutBonus else -80f
    }

    private fun beamBest(legal: List<Candidate>, danger: Int): Candidate {
        var best = legal.maxByOrNull { it.score } ?: legal.first()
        var bestScore = -Float.MAX_VALUE
        val depth = when { danger >= 5 -> 3; danger == 4 -> 4; snake.size >= 55 -> 6; else -> 5 }
        val width = when { danger >= 5 -> 5; danger == 4 -> 7; snake.size >= 70 -> 9; else -> 8 }
        beamDepth = depth
        beamNodes = 0
        data class Node(val body: ArrayDeque<P>, val first: P, val score: Float, val direction: P)
        var layer = legal.map { Node(simulate(it.d).body, it.d, it.score, it.d) }
        repeat(depth) {
            if (layer.isEmpty()) return@repeat
            val next = ArrayList<Node>()
            for (node in layer) {
                beamNodes++
                if (node.score > bestScore) {
                    bestScore = node.score
                    best = legal.firstOrNull { it.d == node.first } ?: best
                }
                val nd = directionOf(node.body)
                for (d in dirs) {
                    if (isReverse(d, nd)) continue
                    if (!canMove(node.body, d)) continue
                    val sim = simulateOn(node.body, d)
                    val region = freeRegion(sim.body)
                    val tail = tailReachable(sim.body)
                    val mobility = countSafeMoves(sim.body)
                    val fd = distance(sim.body.first(), food, sim.body)
                    var s = node.score + region * 7f + mobility * 25f + if (tail) 130f else -180f
                    if (fd >= 0) s += 50f / (fd + 1)
                    if (sim.ate) s += if (tail && region >= sim.body.size * 2) 450f else -250f
                    next.add(Node(sim.body, node.first, s, d))
                }
            }
            layer = next.sortedByDescending { it.score }.take(width)
        }
        return best
    }

    private fun selectStrategy(state: Int, danger: Int): Int {
        val priors = floatArrayOf(
            if (snake.size < 30) .55f else .25f,
            if (danger >= 4) 1.10f else .55f,
            if (snake.size >= 45) .85f else .20f,
            if (danger <= 2 && snake.size >= 45) 1.25f else .60f
        )
        if (hunger > 18) priors[0] += .35f
        if (danger >= 4) priors[1] += .45f
        var best = 0
        var value = -Float.MAX_VALUE
        val total = n[state].sum().coerceAtLeast(0)
        val logTerm = kotlin.math.ln((total + 2).toFloat())
        for (a in 0 until actions) {
            val visits = n[state][a]
            val explore = if (visits == 0) 1.35f else .72f * sqrt(logTerm / visits)
            val v = q[state][a] + priors[a] + explore
            if (v > value) { value = v; best = a }
        }
        return best
    }

    private fun encodeState(body: ArrayDeque<P>, danger: Int): Int {
        val lengthState = when { body.size < 20 -> 0; body.size < 40 -> 1; body.size < 70 -> 2; else -> 3 }
        val d = (danger - 1).coerceIn(0, 4)
        val tail = if (tailReachable(body)) 1 else 0
        val ratio = freeRegion(body).toFloat() / max(1, body.size)
        val space = when { ratio < 1.8f -> 0; ratio < 3.5f -> 1; else -> 2 }
        val fd = distance(body.first(), food, body)
        val foodState = when { fd < 0 -> 0; fd <= 5 -> 2; else -> 1 }
        val hungry = if (hunger >= 18) 1 else 0
        return (((((lengthState * 5 + d) * 2 + tail) * 3 + space) * 3 + foodState) * 2 + hungry).coerceIn(0, stateCount - 1)
    }

    private fun learnTransition(reward: Float, terminal: Boolean) {
        if (aiMode == 0 || lastState !in 0 until stateCount || lastAction !in 0 until actions) return
        val s = lastState
        val a = lastAction
        val visits = n[s][a]
        val alpha = when { visits < 8 -> .28f; visits < 30 -> .16f; visits < 100 -> .085f; else -> .035f }
        val next = encodeState(snake, calculateDanger(snake))
        val target = if (terminal) reward else reward + gamma * (q[next].maxOrNull() ?: 0f)
        q[s][a] += alpha * (target - q[s][a])
        n[s][a]++
        learningSteps++
        dirtyLearning = true
        if (learningSteps % 1000L == 0L) saveLearning()
    }

    private fun die(cause: String) {
        gameOver = true
        deathCause = cause
        when (cause) { "WALL" -> deathWall++; "SELF" -> deathSelf++; else -> deathTrap++ }
        learnTransition(if (cause == "WALL") -10f else -12f, true)
        totalGames++
        if (cause == "TRAP") safetyMargin = min(2.2f, safetyMargin * 1.035f)
        saveLearning()
        try {
            if (Build.VERSION.SDK_INT >= 26) vibrator?.vibrate(VibrationEffect.createOneShot(40, VibrationEffect.DEFAULT_AMPLITUDE))
        } catch (_: Exception) {}
    }

    private fun strategyName(s: Int) = when (s) {
        0 -> "BFS 食物"
        1 -> "TAIL 追尾"
        2 -> "HAM 路线"
        3 -> "BEAM 前瞻"
        else -> "AUTO"
    }

    private fun simulate(d: P) = simulateOn(ArrayDeque(snake), d)

    private fun simulateOn(src: ArrayDeque<P>, d: P): Sim {
        val b = ArrayDeque(src)
        if (b.isEmpty()) return Sim(b, false)
        val nh = P(b.first().x + d.x, b.first().y + d.y)
        if (!inside(nh)) return Sim(b, false)
        val ate = nh == food
        if (b.contains(nh) && !(nh == b.last() && !ate)) return Sim(b, false)
        b.addFirst(nh)
        if (!ate) b.removeLast()
        return Sim(b, ate)
    }

    private fun canMove(d: P) = d != P(0,0) && !isReverse(d, dir) && canMove(snake, d)

    private fun canMove(body: ArrayDeque<P>, d: P): Boolean {
        if (body.isEmpty()) return false
        val h = body.first()
        val nh = P(h.x + d.x, h.y + d.y)
        if (!inside(nh)) return false
        val ate = nh == food
        return !body.contains(nh) || (nh == body.last() && !ate)
    }

    private fun isReverse(a: P, b: P) = a.x == -b.x && a.y == -b.y
    private fun directionOf(body: ArrayDeque<P>) = if (body.size < 2) dir else P(body.elementAt(0).x - body.elementAt(1).x, body.elementAt(0).y - body.elementAt(1).y)
    private fun inside(p: P) = p.x in 0 until cols && p.y in 0 until rows

    private fun freeRegion(body: ArrayDeque<P>): Int {
        if (body.isEmpty()) return 0
        val blocked = HashSet(body)
        val start = body.first()
        blocked.remove(start)
        val seen = HashSet<P>()
        val queue = ArrayDeque<P>()
        queue.add(start); seen.add(start)
        while (queue.isNotEmpty()) {
            val p = queue.removeFirst()
            for (d in dirs) {
                val np = P(p.x + d.x, p.y + d.y)
                if (inside(np) && !blocked.contains(np) && seen.add(np)) queue.add(np)
            }
        }
        return seen.size
    }

    private fun countSafeMoves(body: ArrayDeque<P>): Int {
        if (body.isEmpty()) return 0
        val bd = directionOf(body)
        return dirs.count { d -> !isReverse(d, bd) && canMove(body, d) }
    }

    private fun tailReachable(body: ArrayDeque<P>): Boolean {
        return body.isNotEmpty() && distance(body.first(), body.last(), body) >= 0
    }

    private fun distance(start: P, target: P, body: Collection<P>): Int {
        if (start == target) return 0
        val blocked = HashSet(body)
        if (body.isNotEmpty()) blocked.remove(body.last())
        blocked.remove(start)
        val seen = HashSet<P>()
        val queue = ArrayDeque<Pair<P, Int>>()
        queue.add(start to 0); seen.add(start)
        while (queue.isNotEmpty()) {
            val cur = queue.removeFirst()
            for (d in dirs) {
                val np = P(cur.first.x + d.x, cur.first.y + d.y)
                if (np == target) return cur.second + 1
                if (inside(np) && !blocked.contains(np) && seen.add(np)) queue.add(np to cur.second + 1)
            }
        }
        return -1
    }

    private fun calculateDanger(body: ArrayDeque<P>): Int {
        val region = freeRegion(body)
        val ratio = region.toFloat() / max(1, body.size)
        val mobility = countSafeMoves(body)
        return when { mobility == 0 -> 5; ratio < 1.5f -> 5; ratio < 2.2f -> 4; ratio < 3.4f -> 3; ratio < 5f -> 2; else -> 1 }
    }

    private fun placeFood() {
        val free = ArrayList<P>()
        for (x in 0 until cols) for (y in 0 until rows) {
            val p = P(x, y)
            if (!snake.contains(p)) free.add(p)
        }
        if (free.isNotEmpty()) food = free[Random.nextInt(free.size)]
    }

    // ==================== Headless RL trainer ====================
    private inner class HeadlessTrainer {
        private val runningFlag = AtomicBoolean(false)
        private val stopFlag = AtomicBoolean(false)
        private val workerCount = max(1, Runtime.getRuntime().availableProcessors())
        private var executor = Executors.newFixedThreadPool(workerCount)
        private val games = AtomicLong(0)
        private val scoreSum = AtomicLong(0)
        private val best = AtomicInteger(0)
        private val learning = AtomicLong(0)
        private val started = AtomicLong(0)
        private val recent = LongArray(128)
        private var recentPos = 0
        private var recentCount = 0
        private val recentLock = Any()
        @Volatile var forcedStrategy = this@SnakeView.forcedStrategy
        private val workers = ArrayList<Worker>()

        fun start() {
            if (!runningFlag.compareAndSet(false, true)) return
            stopFlag.set(false)
            games.set(0); scoreSum.set(0); best.set(0); learning.set(0)
            started.set(SystemClock.elapsedRealtime())
            executor.shutdownNow()
            executor = Executors.newFixedThreadPool(workerCount)
            workers.clear()
            repeat(workerCount) { id ->
                val w = Worker(id)
                workers.add(w)
                executor.execute { w.loop() }
            }
            trainingWorkers = workerCount
            trainingStatus = "训练中"
        }

        fun stop() {
            if (!runningFlag.compareAndSet(true, false)) return
            stopFlag.set(true)
            executor.shutdownNow()
            try { executor.awaitTermination(800, TimeUnit.MILLISECONDS) } catch (_: InterruptedException) {}
            mergeAll()
            if (dirtyLearning) saveLearning()
            trainingStatus = "已停止"
        }

        fun isRunning() = runningFlag.get() && !stopFlag.get()
        fun games() = games.get()
        fun best() = best.get()
        fun learning() = learning.get()
        fun avg() = if (games() == 0L) 0.0 else scoreSum.get().toDouble() / games()
        fun speed(): Long {
            val ms = max(1L, SystemClock.elapsedRealtime() - started.get())
            return games() * 1000L / ms
        }
        fun recentAvg(): Double = synchronized(recentLock) {
            if (recentCount == 0) 0.0 else recent.take(recentCount).sum().toDouble() / recentCount
        }

        fun refreshSnapshot() {
            var chosen: Worker? = null
            var metric = Long.MIN_VALUE
            for (w in workers) {
                val m = w.currentScore.toLong() * 100000L + w.currentLength * 100L + w.currentSteps.toLong()
                if (m > metric) { metric = m; chosen = w }
            }
            chosen?.snapshotInto(this@SnakeView)
        }

        private fun record(value: Int) {
            val g = games.incrementAndGet()
            scoreSum.addAndGet(value.toLong())
            while (true) {
                val old = best.get()
                if (value <= old || best.compareAndSet(old, value)) break
            }
            synchronized(recentLock) {
                recent[recentPos] = value.toLong()
                recentPos = (recentPos + 1) % recent.size
                recentCount = min(recentCount + 1, recent.size)
            }
            if (g % 4096L == 0L) {
                mergeAll()
                saveLearning()
            }
        }

        private fun mergeAll() {
            synchronized(q) {
                for (w in workers) w.mergeInto(q, n)
            }
            dirtyLearning = true
        }

        private inner class Worker(private val id: Int) {
            private val board = IntArray(cells)
            private val body = IntArray(cells)
            private val localQ = FloatArray(stateCount * actions)
            private val localN = IntArray(stateCount * actions)
            private val bfs = IntArray(cells)
            private val seen = BooleanArray(cells)
            private val dx = intArrayOf(0,0,-1,1)
            private val dy = intArrayOf(-1,1,0,0)
            private val rng = Random(System.nanoTime() xor (id.toLong() * 0x9E3779B9L))

            @Volatile var currentScore = 0
            @Volatile var currentLength = 1
            @Volatile var currentSteps = 0
            @Volatile var currentFood = -1
            @Volatile var currentHead = cells / 2
            @Volatile var currentDir = 3

            private var len = 1
            private var head = cells / 2
            private var food = 0
            private var direction = 3
            private var localScore = 0
            private var hungerLocal = 0
            private var steps = 0
            private var foods = 0
            private var episodes = 0

            init {
                synchronized(q) {
                    for (i in localQ.indices) localQ[i] = q[i / actions][i % actions]
                    for (i in localN.indices) localN[i] = n[i / actions][i % actions]
                }
            }

            fun loop() {
                try {
                    while (!stopFlag.get() && !Thread.currentThread().isInterrupted) {
                        runEpisode()
                        episodes++
                        if (episodes % 512 == 0) mergeInto(q, n)
                    }
                } finally {
                    mergeInto(q, n)
                }
            }

            private fun resetEpisode() {
                Arrays.fill(board, 0)
                len = 1
                head = cells / 2
                body[0] = head
                board[head] = 1
                direction = 3
                localScore = 0
                hungerLocal = 0
                steps = 0
                foods = 0
                food = pickFood()
                publish()
            }

            private fun publish() {
                currentScore = localScore
                currentLength = len
                currentSteps = steps
                currentFood = food
                currentHead = head
                currentDir = direction
            }

            private fun runEpisode() {
                resetEpisode()
                var dead = false
                while (!dead && !stopFlag.get() && steps < 20000) {
                    val danger = dangerFast()
                    val s = stateFast(danger)
                    val a = chooseAction(s, danger)
                    val result = move(a)
                    dead = result.second
                    val next = if (dead) 0 else stateFast(dangerFast())
                    learnLocal(s, a, result.first, dead, next)
                    steps++
                    currentSteps = steps
                    if ((steps and 63) == 0) publish()
                }
                publish()
                record(localScore)
            }

            private fun chooseAction(s: Int, danger: Int): Int {
                val forced = forcedStrategy
                if (forced >= 0) return if (forced == 4) 3 else forced.coerceIn(0, 3)
                val priors = floatArrayOf(
                    if (len < 30) .55f else .25f,
                    if (danger >= 4) 1.10f else .55f,
                    if (len >= 45) .85f else .20f,
                    if (danger <= 2 && len >= 45) 1.25f else .60f
                )
                if (hungerLocal > 18) priors[0] += .35f
                if (danger >= 4) priors[1] += .45f
                var total = 0
                for (a in 0 until actions) total += localN[s * actions + a]
                val logTerm = kotlin.math.ln((total + 2).toFloat())
                var bestA = 0
                var bestV = -Float.MAX_VALUE
                for (a in 0 until actions) {
                    val idx = s * actions + a
                    val visits = localN[idx]
                    val explore = if (visits == 0) 1.35f else .72f * sqrt(logTerm / visits)
                    val v = localQ[idx] + priors[a] + explore
                    if (v > bestV) { bestV = v; bestA = a }
                }
                return bestA
            }

            private fun move(strategy: Int): Pair<Float, Boolean> {
                var chosen = -1
                var bestValue = -Float.MAX_VALUE
                for (d in 0..3) {
                    if (!legal(d)) continue
                    val value = when (strategy) {
                        0 -> foodScore(d)
                        1 -> tailScoreFast(d)
                        2 -> hamScoreFast(d)
                        else -> beamScoreFast(d)
                    }
                    if (value > bestValue) { bestValue = value; chosen = d }
                }
                if (chosen < 0) return -15f to true
                val x = head % cols + dx[chosen]
                val y = head / cols + dy[chosen]
                if (x !in 0 until cols || y !in 0 until rows) return -12f to true
                val nh = y * cols + x
                val ate = nh == food
                val tail = body[len - 1]
                if (board[nh] != 0 && !(nh == tail && !ate)) return -12f to true
                if (!ate) board[tail] = 0
                val newLen = if (ate) min(cells, len + 1) else len
                for (i in newLen - 1 downTo 1) body[i] = body[i - 1]
                body[0] = nh
                len = newLen
                head = nh
                board[nh] = 1
                direction = chosen
                var reward = .025f
                if (ate) {
                    localScore += 10 + min(foods, 20)
                    foods++
                    hungerLocal = 0
                    food = pickFood()
                    reward = 2.5f + min(foods, 20) * .05f
                } else hungerLocal++
                val region = regionFast()
                val ratio = region.toFloat() / max(1, len)
                if (ratio < 1.4f) reward -= .15f
                if (safeMovesFast() <= 1) reward -= .25f
                currentFood = food
                currentHead = head
                currentDir = direction
                return reward to false
            }

            private fun legal(d: Int): Boolean {
                val reverse = (direction == 0 && d == 1) || (direction == 1 && d == 0) || (direction == 2 && d == 3) || (direction == 3 && d == 2)
                if (reverse) return false
                val x = head % cols + dx[d]
                val y = head / cols + dy[d]
                if (x !in 0 until cols || y !in 0 until rows) return false
                val nh = y * cols + x
                return board[nh] == 0 || nh == body[len - 1]
            }

            private fun commonScore(d: Int): Float {
                val region = regionAfter(d)
                val moves = safeMovesAfter(d)
                var value = region * 12f + moves * 38f
                if (region < max(8, len)) value -= 350f
                if (moves <= 1) value -= 250f
                return value
            }

            private fun foodScore(d: Int): Float {
                val pd = pathDistance(d)
                return commonScore(d) + if (pd >= 0) 220f / (pd + 1) else -150f
            }

            private fun tailScoreFast(d: Int): Float {
                return commonScore(d) + if (tailReachableFast(d)) 420f else -520f
            }

            private fun hamScoreFast(d: Int): Float {
                val x = head % cols + dx[d]
                val y = head / cols + dy[d]
                if (x !in 0 until cols || y !in 0 until rows) return -100000f
                val idx = y * cols + x
                var value = commonScore(d)
                if ((idx and 1) == ((x + y) and 1)) value += 80f * shortcutBonus
                if (len >= 45) value += regionAfter(d) * 2f
                return value
            }

            private fun beamScoreFast(d: Int): Float {
                var value = commonScore(d) + regionAfter(d) * 5f
                val x = head % cols + dx[d]
                val y = head / cols + dy[d]
                if (x in 0 until cols && y in 0 until rows && y * cols + x == food) value += 400f
                return value
            }

            private fun regionAfter(d: Int): Int {
                val x = head % cols + dx[d]
                val y = head / cols + dy[d]
                if (x !in 0 until cols || y !in 0 until rows) return 0
                val start = y * cols + x
                Arrays.fill(seen, false)
                var qs = 0
                var qe = 0
                bfs[qe++] = start
                seen[start] = true
                while (qs < qe) {
                    val p = bfs[qs++]
                    val px = p % cols
                    val py = p / cols
                    for (k in 0..3) {
                        val xx = px + dx[k]
                        val yy = py + dy[k]
                        if (xx !in 0 until cols || yy !in 0 until rows) continue
                        val ni = yy * cols + xx
                        if (!seen[ni] && (board[ni] == 0 || ni == body[len - 1] || ni == start)) {
                            seen[ni] = true
                            bfs[qe++] = ni
                        }
                    }
                }
                return qe
            }

            private fun safeMovesAfter(d: Int): Int {
                val x = head % cols + dx[d]
                val y = head / cols + dy[d]
                if (x !in 0 until cols || y !in 0 until rows) return 0
                return (0..3).count { k ->
                    val xx = x + dx[k]
                    val yy = y + dy[k]
                    if (xx !in 0 until cols || yy !in 0 until rows) false
                    else {
                        val idx = yy * cols + xx
                        board[idx] == 0 || idx == body[len - 1]
                    }
                }
            }

            private fun regionFast(): Int {
                Arrays.fill(seen, false)
                var qs = 0
                var qe = 0
                bfs[qe++] = head
                seen[head] = true
                while (qs < qe) {
                    val p = bfs[qs++]
                    val x = p % cols
                    val y = p / cols
                    for (k in 0..3) {
                        val xx = x + dx[k]
                        val yy = y + dy[k]
                        if (xx !in 0 until cols || yy !in 0 until rows) continue
                        val ni = yy * cols + xx
                        if (!seen[ni] && board[ni] == 0) { seen[ni] = true; bfs[qe++] = ni }
                    }
                }
                return qe
            }

            private fun safeMovesFast() = (0..3).count { legal(it) }

            private fun pathDistance(d: Int): Int {
                val sx = head % cols + dx[d]
                val sy = head / cols + dy[d]
                if (sx !in 0 until cols || sy !in 0 until rows) return -1
                val start = sy * cols + sx
                if (start == food) return 0
                Arrays.fill(seen, false)
                var qs = 0
                var qe = 0
                bfs[qe++] = start
                seen[start] = true
                val dist = IntArray(cells)
                dist[start] = 0
                while (qs < qe) {
                    val p = bfs[qs++]
                    val px = p % cols
                    val py = p / cols
                    for (k in 0..3) {
                        val xx = px + dx[k]
                        val yy = py + dy[k]
                        if (xx !in 0 until cols || yy !in 0 until rows) continue
                        val ni = yy * cols + xx
                        if (seen[ni]) continue
                        if (board[ni] != 0 && ni != body[len - 1] && ni != food) continue
                        if (ni == food) return dist[p] + 1
                        seen[ni] = true
                        dist[ni] = dist[p] + 1
                        bfs[qe++] = ni
                    }
                }
                return -1
            }

            private fun tailReachableFast(d: Int): Boolean = regionAfter(d) >= max(8, len)

            private fun dangerFast(): Int {
                val region = regionFast()
                val ratio = region.toFloat() / max(1, len)
                val moves = safeMovesFast()
                return when { moves == 0 -> 5; ratio < 1.5f -> 5; ratio < 2.2f -> 4; ratio < 3.4f -> 3; ratio < 5f -> 2; else -> 1 }
            }

            private fun stateFast(danger: Int): Int {
                val ls = when { len < 20 -> 0; len < 40 -> 1; len < 70 -> 2; else -> 3 }
                val tail = if (tailReachableFast(direction)) 1 else 0
                val ratio = regionFast().toFloat() / max(1, len)
                val space = when { ratio < 1.8f -> 0; ratio < 3.5f -> 1; else -> 2 }
                val pd = pathDistance(direction)
                val foodState = when { pd < 0 -> 0; pd <= 5 -> 2; else -> 1 }
                val hungry = if (hungerLocal >= 18) 1 else 0
                return (((((ls * 5 + (danger - 1).coerceIn(0, 4)) * 2 + tail) * 3 + space) * 3 + foodState) * 2 + hungry).coerceIn(0, stateCount - 1)
            }

            private fun learnLocal(s: Int, a: Int, reward: Float, terminal: Boolean, next: Int) {
                val idx = s * actions + a
                val visits = localN[idx]
                val alpha = when { visits < 8 -> .28f; visits < 30 -> .16f; visits < 100 -> .085f; else -> .035f }
                val target = if (terminal) reward else reward + gamma * maxOf(localQ[next * actions], localQ[next * actions + 1], localQ[next * actions + 2], localQ[next * actions + 3])
                localQ[idx] += alpha * (target - localQ[idx])
                localN[idx]++
                learning.incrementAndGet()
            }

            fun mergeInto(globalQ: Array<FloatArray>, globalN: Array<IntArray>) {
                synchronized(q) {
                    for (s in 0 until stateCount) for (a in 0 until actions) {
                        val idx = s * actions + a
                        val ln = localN[idx]
                        if (ln <= 0) continue
                        val old = globalN[s][a]
                        val total = old + ln
                        globalQ[s][a] = if (old == 0) localQ[idx] else (globalQ[s][a] * old + localQ[idx] * ln) / total
                        globalN[s][a] = total
                    }
                }
            }

            fun snapshotInto(v: SnakeView) {
                v.trainingCurrentScore = currentScore
                v.trainingCurrentLength = currentLength
                v.trainingCurrentSteps = currentSteps
                v.trainingSnapshotFood = currentFood
                v.trainingSnapshotHead = currentHead
                val copyLen = min(len, cells)
                v.trainingSnapshot = IntArray(copyLen) { body[it] }
                v.trainingSnapshotLength = copyLen
            }

            private fun pickFood(): Int {
                var f = rng.nextInt(cells)
                var tries = 0
                while (board[f] != 0 && tries++ < 500) f = rng.nextInt(cells)
                return f
            }
        }
    }

    private fun startHeadlessTraining() {
        if (aiMode != 2) return
        if (trainer == null) trainer = HeadlessTrainer()
        if (trainer?.isRunning() != true) trainer?.start()
        trainingStatus = "训练中"
    }

    private fun stopHeadlessTraining() {
        trainer?.stop()
        trainer = null
        trainingStatus = "已停止"
        refreshTrainingHud()
    }

    private fun refreshTrainingHud() {
        val t = trainer ?: return
        t.refreshSnapshot()
        trainingGames = t.games()
        trainingBest = t.best()
        trainingAvg = t.avg()
        trainingRecentAvg = t.recentAvg()
        trainingSpeed = t.speed()
        trainingLearning = t.learning()
        trainingStatus = if (t.isRunning()) "训练中" else "已停止"
        invalidate()
    }

    private fun saveLearning() {
        val e = prefs.edit()
            .putFloat("learn_aggression", aggression)
            .putFloat("learn_safety", safetyMargin)
            .putFloat("learn_shortcut", shortcutBonus)
            .putInt("stat_wall", deathWall)
            .putInt("stat_self", deathSelf)
            .putInt("stat_trap", deathTrap)
            .putInt("stat_total", totalGames)
            .putInt("money", money)
        for (s in 0 until stateCount) for (a in 0 until actions) {
            e.putFloat("q2_${s}_$a", q[s][a])
            e.putInt("n2_${s}_$a", n[s][a])
        }
        e.apply()
        dirtyLearning = false
    }

    override fun onDraw(c: Canvas) {
        super.onDraw(c)
        if (aiMode == 2) {
            drawTrainingHud(c)
            return
        }
        val cell = min(width.toFloat() / cols, height.toFloat() / rows)
        val ox = (width - cols * cell) / 2f
        val oy = (height - rows * cell) / 2f
        c.drawColor(bgColor)
        gridPaint.color = gridColor
        gridPaint.style = Paint.Style.STROKE
        gridPaint.strokeWidth = 1f
        for (i in 0..cols) c.drawLine(ox + i * cell, oy, ox + i * cell, oy + rows * cell, gridPaint)
        for (i in 0..rows) c.drawLine(ox, oy + i * cell, ox + cols * cell, oy + i * cell, gridPaint)
        drawFood(c, cell, ox, oy)
        drawSnake(c, cell, ox, oy)
        if (gameOver) drawGameOver(c)
        if (aiMode == 1) drawDebug(c)
    }

    private fun drawTrainingHud(c: Canvas) {
        c.drawColor(Color.rgb(5, 8, 12))
        val pad = 16f
        val w = width.toFloat()
        val h = height.toFloat()
        text.textAlign = Paint.Align.LEFT
        text.setFakeBoldText(true)
        text.textSize = 20f
        text.color = Color.CYAN
        c.drawText("⚡ 强化学习 · 极速训练", pad, 31f, text)
        text.setFakeBoldText(false)
        text.textSize = 11f
        text.color = Color.LTGRAY
        c.drawText("多线程无棋盘计算 · UI 仅低频显示", pad, 50f, text)

        val panelBottom = min(h - 20f, 245f)
        panel.color = Color.argb(220, 18, 22, 30)
        c.drawRoundRect(pad, 64f, w - pad, panelBottom, 18f, 18f, panel)
        border.color = Color.CYAN
        border.style = Paint.Style.STROKE
        border.strokeWidth = 2f
        c.drawRoundRect(pad, 64f, w - pad, panelBottom, 18f, 18f, border)

        text.textSize = 13f
        text.color = Color.WHITE
        val left = pad + 13f
        val right = w / 2f + 8f
        val y = 91f
        val gap = 23f
        c.drawText("状态：$trainingStatus", left, y, text)
        c.drawText("线程：$trainingWorkers / ${Runtime.getRuntime().availableProcessors()}", left, y + gap, text)
        c.drawText("总局数：$trainingGames", left, y + gap * 2, text)
        c.drawText("速度：$trainingSpeed 局/秒", left, y + gap * 3, text)
        c.drawText("总平均：${"%.1f".format(trainingAvg)}", left, y + gap * 4, text)
        c.drawText("近128局：${"%.1f".format(trainingRecentAvg)}", left, y + gap * 5, text)
        c.drawText("最高分：$trainingBest", right, y, text)
        c.drawText("当前分：$trainingCurrentScore", right, y + gap, text)
        c.drawText("当前长度：$trainingCurrentLength", right, y + gap * 2, text)
        c.drawText("当前步数：$trainingCurrentSteps", right, y + gap * 3, text)
        c.drawText("策略：$aiStrategy", right, y + gap * 4, text)
        c.drawText("学习更新：$trainingLearning", right, y + gap * 5, text)

        val top = 265f
        val boardSize = min(w - 32f, max(120f, h - top - 28f))
        val bx = (w - boardSize) / 2f
        val by = top
        val cc = boardSize / cols
        panel.color = Color.BLACK
        c.drawRoundRect(bx - 3f, by - 3f, bx + boardSize + 3f, by + boardSize + 3f, 12f, 12f, panel)
        gridPaint.color = Color.rgb(45, 55, 65)
        gridPaint.style = Paint.Style.STROKE
        for (i in 0..cols) c.drawLine(bx + i * cc, by, bx + i * cc, by + boardSize, gridPaint)
        for (i in 0..rows) c.drawLine(bx, by + i * cc, bx + boardSize, by + i * cc, gridPaint)

        val f = trainingSnapshotFood
        if (f >= 0) {
            foodPaint.color = Color.RED
            c.drawCircle(bx + (f % cols + .5f) * cc, by + (f / cols + .5f) * cc, cc * .22f, foodPaint)
        }
        if (trainingSnapshotLength > 0) {
            snakePaint.strokeWidth = max(4f, cc * .58f)
            snakePaint.color = bodyColor
            for (i in 0 until trainingSnapshotLength - 1) {
                val a = trainingSnapshot[i]
                val b = trainingSnapshot[i + 1]
                c.drawLine(
                    bx + (a % cols + .5f) * cc, by + (a / cols + .5f) * cc,
                    bx + (b % cols + .5f) * cc, by + (b / cols + .5f) * cc, snakePaint
                )
            }
            val hd = trainingSnapshotHead
            if (hd >= 0) {
                headPaint.color = headColor
                c.drawCircle(bx + (hd % cols + .5f) * cc, by + (hd / cols + .5f) * cc, cc * .34f, headPaint)
            }
        }
        text.textSize = 10f
        text.color = Color.LTGRAY
        c.drawText("实时训练轨迹快照（仅显示，不参与训练）", pad, h - 7f, text)
    }

    private fun drawFood(c: Canvas, cell: Float, ox: Float, oy: Float) {
        foodPaint.color = Color.RED
        c.drawCircle(ox + (food.x + .5f) * cell, oy + (food.y + .5f) * cell, cell * .22f, foodPaint)
    }

    private fun drawSnake(c: Canvas, cell: Float, ox: Float, oy: Float) {
        if (snake.isEmpty()) return
        snakePaint.strokeWidth = max(8f, cell * .62f)
        val list = snake.toList()
        for (i in 0 until list.size - 1) {
            val a = list[i]
            val b = list[i + 1]
            snakePaint.color = if (rainbowSkin) hsv[(i * 23 + score) % 360] else bodyColor
            c.drawLine(ox + (a.x + .5f) * cell, oy + (a.y + .5f) * cell, ox + (b.x + .5f) * cell, oy + (b.y + .5f) * cell, snakePaint)
        }
        val head = snake.first()
        headPaint.color = headColor
        c.drawCircle(ox + (head.x + .5f) * cell, oy + (head.y + .5f) * cell, cell * .36f, headPaint)
    }

    private fun drawDebug(c: Canvas) {
        val w = min(width * .94f, 520f)
        val left = width - w - 12f
        val top = 12f
        val bottom = min(height - 12f, top + 174f)
        panel.color = Color.argb(205, 0, 0, 0)
        c.drawRoundRect(left, top, left + w, bottom, 18f, 18f, panel)
        border.color = when (aiDanger) { 1 -> Color.GREEN; 2 -> Color.rgb(150,255,80); 3 -> Color.YELLOW; 4 -> Color.rgb(255,150,0); else -> Color.RED }
        border.style = Paint.Style.STROKE
        border.strokeWidth = 3f
        c.drawRoundRect(left, top, left + w, bottom, 18f, 18f, border)
        text.textAlign = Paint.Align.LEFT
        text.setFakeBoldText(true)
        text.textSize = 16f
        text.color = Color.WHITE
        c.drawText("🧠 AI  $aiStrategy", left + 12f, top + 24f, text)
        text.setFakeBoldText(false)
        text.textSize = 12f
        text.color = Color.YELLOW
        c.drawText(aiReason, left + 12f, top + 43f, text)
        text.color = Color.WHITE
        c.drawText("危险 $aiDanger/5   空间 $aiRegion   尾巴 ${if (aiTail) "可达" else "不可达"}", left + 12f, top + 62f, text)
        c.drawText("食物距离 ${if (aiFoodDistance < 0) "∞" else aiFoodDistance}   长度 ${snake.size}   饥饿 $hunger", left + 12f, top + 81f, text)
        c.drawText("分数 $score   学习局数 $totalGames   搜索 $beamDepth 层 / $beamNodes 节点", left + 12f, top + 100f, text)
        c.drawText("W$deathWall  S$deathSelf  T$deathTrap", left + 12f, top + 119f, text)
        text.color = Color.CYAN
        c.drawText("强化学习：720 状态 × 4 策略", left + 12f, top + 140f, text)
    }

    private fun drawGameOver(c: Canvas) {
        paint.color = Color.argb(150, 0, 0, 0)
        c.drawRect(0f, 0f, width.toFloat(), height.toFloat(), paint)
        text.textAlign = Paint.Align.CENTER
        text.setFakeBoldText(true)
        text.textSize = 30f
        text.color = Color.WHITE
        c.drawText("GAME OVER", width / 2f, height / 2f - 45f, text)
        text.setFakeBoldText(false)
        text.textSize = 15f
        c.drawText("分数 $score   最高 $highScore   长度 ${snake.size}", width / 2f, height / 2f - 15f, text)
        text.color = Color.YELLOW
        c.drawText("点击屏幕重新开始", width / 2f, height / 2f + 20f, text)
    }

    override fun onTouchEvent(e: MotionEvent): Boolean {
        if (e.action != MotionEvent.ACTION_UP) return true
        if (aiMode == 2) return true
        if (gameOver) { reset(); return true }
        if (aiMode != 0) return true
        val cell = min(width.toFloat() / cols, height.toFloat() / rows)
        val ox = (width - cols * cell) / 2f
        val oy = (height - rows * cell) / 2f
        val dxTouch = e.x - (ox + (snake.first().x + .5f) * cell)
        val dyTouch = e.y - (oy + (snake.first().y + .5f) * cell)
        val d = if (abs(dxTouch) > abs(dyTouch)) P(if (dxTouch > 0) 1 else -1, 0) else P(0, if (dyTouch > 0) 1 else -1)
        if (!isReverse(d, dir)) inputQueue.add(d)
        return true
    }
}
