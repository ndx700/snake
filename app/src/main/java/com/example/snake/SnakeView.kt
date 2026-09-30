package com.example.snake

import android.content.Context
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Paint
import android.graphics.Path
import android.graphics.RectF
import android.os.Build
import android.os.VibrationEffect
import android.os.Vibrator
import android.os.VibratorManager
import android.util.AttributeSet
import android.view.Choreographer
import android.view.MotionEvent
import android.view.View
import java.util.ArrayDeque
import java.util.Arrays
import java.util.concurrent.ThreadLocalRandom
import kotlin.math.abs
import kotlin.math.max
import kotlin.math.min
import kotlin.random.Random

/**
 * SnakeView V2
 *
 * V2 keeps the public API used by MainActivity, but replaces the old 100x4
 * strategy Q-table with an action-level RL learner:
 *  - bounded 65,536-state representation
 *  - real TD Q-learning with bootstrapping
 *  - epsilon-greedy exploration with decay
 *  - replay memory
 *  - 8 independent training workers sharing the same learner
 *  - the visible game and reinforcement workers use the same policy
 *  - a deterministic safety shield prevents obviously suicidal moves
 */
class SnakeView @JvmOverloads constructor(
    context: Context,
    attrs: AttributeSet? = null
) : View(context, attrs) {

    private data class P(val x: Int, val y: Int)
    private data class Candidate(
        val d: P,
        val action: Int,
        val q: Float,
        val heuristic: Float,
        val total: Float,
        val legal: Boolean,
        val safe: Boolean,
        val region: Int,
        val mobility: Int,
        val tailOk: Boolean,
        val foodDist: Int,
        val ate: Boolean
    )
    private data class Transition(
        val state: Int,
        val action: Int,
        val reward: Float,
        val nextState: Int,
        val done: Boolean
    )
    private data class Decision(
        val state: Int,
        val action: Int,
        val direction: P,
        val candidates: List<Candidate>,
        val danger: Int,
        val region: Int,
        val tailOk: Boolean,
        val foodDist: Int,
        val strategy: String
    )
    private data class SimResult(val body: ArrayDeque<P>, val ate: Boolean)
    private data class TrainSnapshot(
        val body: ArrayDeque<P>,
        val dir: P,
        val food: P,
        val hunger: Int
    )

    private val cols = 15
    private val rows = 15
    private val total = cols * rows

    private val snake = ArrayDeque<P>()
    private val queue = ArrayDeque<P>()
    private val dirs = listOf(P(0, -1), P(0, 1), P(-1, 0), P(1, 0))
    private var dir = P(1, 0)
    private var food = P(5, 5)

    private var cell = 0f
    private var ox = 0f
    private var oy = 0f

    private var score = 0
    private var highScore = 0
    private var money = 0
    private var gameOver = false
    private var running = false
    private var aiMode = 1
    private var forcedStrategy = -1
    private var hunger = 0
    private var combo = 0
    private var deathCause = "无"
    private var lastDeathInfo = ""
    private var gameSpeed = 220L
    private var accumulator = 0L
    private var lastFrame = 0L

    private var trainingMode = false
    @Volatile private var reinforceTraining = false
    @Volatile private var trainActive = false
    private val trainThreads = mutableListOf<Thread>()
    private val TRAIN_THREADS = 8

    private val prefs = context.getSharedPreferences("snake_prefs", Context.MODE_PRIVATE)
    private val vibrator: Vibrator? = if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
        (context.getSystemService(Context.VIBRATOR_MANAGER_SERVICE) as? VibratorManager)?.defaultVibrator
    } else {
        @Suppress("DEPRECATION")
        context.getSystemService(Context.VIBRATOR_SERVICE) as? Vibrator
    }

    var onScoreChanged: ((Int) -> Unit)? = null
    var onMoneyChanged: ((Int) -> Unit)? = null

    // ---------- V2 learner ----------
    // 4 food directions * 16 danger masks * 4 mobility * 4 region buckets
    // * 5 hunger buckets * 8 length buckets * 2 tail states * 4 heading states.
    private val STATE_COUNT = 65536
    private val ACTIONS = 4
    private val q = FloatArray(STATE_COUNT * ACTIONS)
    private val visits = IntArray(STATE_COUNT * ACTIONS)
    private val qLocks = Array(64) { Any() }
    private val replayLock = Any()
    private val replay = ArrayDeque<Transition>()
    private val replayCapacity = 20000

    @Volatile private var epsilon = 0.18f
    private val epsilonMin = 0.025f
    private val epsilonDecay = 0.999985f
    private val gamma = 0.965f
    private val baseAlpha = 0.055f
    private var episodes = 0L
    private var learnedSteps = 0L
    private var learnedFoods = 0L
    private var bestTrainingScore = 0
    private var lastState = -1
    private var lastAction = -1
    private var lastDecision: Decision? = null
    private var replayUpdates = 0L

    private var totalGames = 0
    private var deathWall = 0
    private var deathSelf = 0
    private var deathTrap = 0
    private val recentScores = ArrayDeque<Int>()

    private val bfsVisited = ThreadLocal.withInitial { BooleanArray(total) }
    private val bfsQueue = ThreadLocal.withInitial { IntArray(total + 4) }

    // Rendering / HUD.
    private val paint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val text = Paint(Paint.ANTI_ALIAS_FLAG)
    private val panel = Paint(Paint.ANTI_ALIAS_FLAG)
    private val border = Paint(Paint.ANTI_ALIAS_FLAG)
    private val gridPaint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val snakePaint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val headPaint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val foodPaint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val barPaint = Paint(Paint.ANTI_ALIAS_FLAG)

    private var bodyColor = Color.rgb(46, 204, 113)
    private var headColor = Color.rgb(39, 174, 96)
    private var bgColor = Color.BLACK
    private var gridColor = Color.CYAN
    private var rainbowSkin = false
    private val hsv = IntArray(360) { Color.HSVToColor(floatArrayOf(it.toFloat(), 1f, 1f)) }

    private val particles = mutableListOf<Particle>()
    private val floats = mutableListOf<FloatText>()
    private data class Particle(var x: Float, var y: Float, var vx: Float, var vy: Float, var life: Float, val color: Int)
    private data class FloatText(var x: Float, var y: Float, var life: Float, val value: String)

    private var flash = 0f
    private val restartCountdown = 0L
    private val hungerKillLimit = 500
    private var renderSkipCounter = 0
    private val reinforceButtonRect = RectF()
    private var lastReinforceTap = 0L

    private var aiStepStartNs = 0L
    private var aiStepBudgetNs = 12_000_000L

    init {
        highScore = prefs.getInt("high_score", 0)
        money = prefs.getInt("money", 0)
        trainingMode = prefs.getBoolean("training_mode", false)
        episodes = prefs.getLong("v2_episodes", 0L)
        learnedSteps = prefs.getLong("v2_steps", 0L)
        learnedFoods = prefs.getLong("v2_foods", 0L)
        bestTrainingScore = prefs.getInt("v2_best", 0)
        epsilon = prefs.getFloat("v2_epsilon", 0.18f).coerceIn(epsilonMin, 0.18f)
        updateCurrentSkin()
        updateCurrentBoard()
        reset()
    }

    fun getAIMode(): Int = aiMode
    fun setAIMode(m: Int) { aiMode = m; invalidate() }

    fun setTrainingMode(b: Boolean) {
        trainingMode = b
        if (b) {
            aiMode = 1
            reset()
        } else {
            stopParallelTraining()
            reset()
        }
        invalidate()
    }

    fun setReinforceTraining(enable: Boolean) {
        if (enable) startParallelTraining() else stopParallelTraining()
        invalidate()
    }

    fun isReinforceTraining(): Boolean = reinforceTraining
    fun isTrainingMode(): Boolean = trainingMode
    fun setForcedStrategy(s: Int) { forcedStrategy = s; invalidate() }

    fun updateCurrentSkin(id: String? = null) {
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
        bodyColor = body
        headColor = head
        rainbowSkin = rainbow
        snakePaint.color = body
        snakePaint.style = Paint.Style.FILL
        headPaint.color = head
    }

    fun updateCurrentBoard(id: String? = null) {
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
        snake.clear()
        queue.clear()
        snake.add(P(cols / 2, rows / 2))
        dir = P(1, 0)
        score = 0
        hunger = 0
        combo = 0
        gameOver = false
        deathCause = "无"
        lastDeathInfo = ""
        gameSpeed = if (trainingMode && !reinforceTraining) 2L else 220L
        accumulator = 0L
        lastFrame = 0L
        particles.clear()
        floats.clear()
        lastState = -1
        lastAction = -1
        lastDecision = null
        placeFood()
        onScoreChanged?.invoke(0)
        onMoneyChanged?.invoke(money)
        invalidate()
    }

    fun resume() {
        if (running) return
        running = true
        lastFrame = 0L
        Choreographer.getInstance().postFrameCallback(frame)
    }

    fun pause() {
        running = false
        Choreographer.getInstance().removeFrameCallback(frame)
    }

    private val frame = object : Choreographer.FrameCallback {
        override fun doFrame(ns: Long) {
            if (!running) return
            if (lastFrame == 0L) lastFrame = ns
            val dt = ((ns - lastFrame) / 1_000_000L).coerceAtMost(100L)
            lastFrame = ns
            if (reinforceTraining) {
                if ((++renderSkipCounter % 15) == 0) invalidate()
                Choreographer.getInstance().postFrameCallback(this)
                return
            }
            if (!gameOver) {
                accumulator += dt
                val maxSteps = if (trainingMode) 20 else Int.MAX_VALUE
                var count = 0
                while (accumulator >= gameSpeed && count < maxSteps) {
                    updateGame()
                    accumulator -= gameSpeed
                    count++
                    if (gameOver) break
                }
                if (count >= maxSteps) accumulator = 0L
            }
            updateEffects(dt / 16f)
            val draw = if (trainingMode) (++renderSkipCounter % 4 == 0) else true
            if (draw) invalidate()
            Choreographer.getInstance().postFrameCallback(this)
        }
    }

    // ---------- Game ----------
    private fun updateGame() {
        if (gameOver) return
        if (hunger >= hungerKillLimit) {
            die("HUNGER")
            return
        }

        val decision = if (aiMode != 0) chooseMove(snake, dir, food, hunger, training = trainingMode) else null
        if (decision != null) {
            lastState = decision.state
            lastAction = decision.action
            queue.clear()
            queue.add(decision.direction)
        }
        if (queue.isNotEmpty()) {
            val requested = queue.removeFirst()
            if (!isReverse(requested, dir) && legalDirection(requested, snake, food)) dir = requested
        }

        val previousState = lastState
        val previousAction = lastAction
        val nh = P(snake.first().x + dir.x, snake.first().y + dir.y)
        if (!inside(nh)) {
            learnFromTransition(previousState, previousAction, -8f, stateKey(snake, dir, food, hunger), true)
            die("WALL")
            return
        }

        val ate = nh == food
        if (snake.contains(nh) && !(nh == snake.last() && !ate)) {
            learnFromTransition(previousState, previousAction, -8f, stateKey(snake, dir, food, hunger), true)
            die(if (freeRegionAfterMove(dir, ate) < max(2, snake.size * 0.9f).toInt()) "TRAP" else "SELF")
            return
        }

        snake.addFirst(nh)
        if (ate) {
            val gain = 10 + min(combo, 30) * 3 + snake.size
            score += gain
            combo++
            hunger = 0
            money += gain * 3 + 30
            highScore = max(highScore, score)
            onScoreChanged?.invoke(score)
            onMoneyChanged?.invoke(money)
            prefs.edit().putInt("money", money).putInt("high_score", highScore).apply()
            gameSpeed = max(45L, 220L - snake.size * 2L)
            vibrateEat()
            spawnFoodEffect(nh)
            placeFood()
            val ns = stateKey(snake, dir, food, hunger)
            learnFromTransition(previousState, previousAction, 3.5f + combo * 0.06f, ns, false)
            learnedFoods++
        } else {
            snake.removeLast()
            hunger++
            combo = max(0, combo - 1)
            val ns = stateKey(snake, dir, food, hunger)
            val tail = tailReachable(snake)
            val mobility = countSafeMoves(snake, dir, food)
            val reward = 0.015f + if (tail) 0.03f else -0.12f + mobility * 0.01f
            learnFromTransition(previousState, previousAction, reward, ns, false)
        }
        learnedSteps++
        if ((learnedSteps and 127L) == 0L) replayTrain(8)
    }

    private fun chooseMove(body: ArrayDeque<P>, heading: P, target: P, h: Int, training: Boolean): Decision? {
        if (body.isEmpty()) return null
        aiStepStartNs = System.nanoTime()
        aiStepBudgetNs = if (training) 3_000_000L else 15_000_000L

        val state = stateKey(body, heading, target, h)
        val legal = mutableListOf<Candidate>()
        val all = mutableListOf<Candidate>()
        for (a in 0 until 4) {
            val d = dirs[a]
            if (isReverse(d, heading)) continue
            if (!legalDirection(d, body, target)) continue
            val sim = simulate(body, d, target)
            val region = freeRegion(sim.body)
            val tail = tailReachable(sim.body)
            val mobility = countSafeMoves(sim.body, d, target)
            val fd = distance(sim.body.first(), target, sim.body, true)
            val safe = isSafeCandidate(sim.body, sim.ate, tail, region, mobility)
            val qv = qValue(state, a)
            val heuristic = actionHeuristic(sim.body, sim.ate, tail, region, mobility, fd, h)
            val c = Candidate(d, a, qv, heuristic, qv * 180f + heuristic, true, safe, region, mobility, tail, fd, sim.ate)
            all.add(c)
            if (safe) legal.add(c)
        }
        if (all.isEmpty()) return null
        val pool = if (legal.isNotEmpty()) legal else all
        val chosen = selectCandidate(pool, training)
        val danger = dangerLevel(body, heading, target)
        val strategy = when {
            chosen.ate && chosen.safe -> "V2-SAFE-FOOD"
            chosen.tailOk && chosen.safe -> "V2-TAIL-SAFE"
            training -> "V2-EXPLORE"
            else -> "V2-Q"
        }
        lastDecision = Decision(state, chosen.action, chosen.d, all, danger, freeRegion(body), tailReachable(body), distance(body.first(), target, body, true), strategy)
        return lastDecision
    }

    private fun selectCandidate(pool: List<Candidate>, training: Boolean): Candidate {
        if (pool.size == 1) return pool[0]
        val e = if (training || reinforceTraining) epsilon else 0.008f
        if (ThreadLocalRandom.current().nextFloat() < e) return pool[ThreadLocalRandom.current().nextInt(pool.size)]
        var best = pool[0]
        var bestScore = -Float.MAX_VALUE
        for (c in pool) {
            var s = c.total
            if (c.ate && c.tailOk) s += 900f
            if (c.tailOk) s += 300f
            if (c.region >= snake.size * 1.4f) s += 120f
            if (c.mobility >= 2) s += 80f
            if (c.d == dir) s += 5f
            if (forcedStrategy >= 1 && forcedStrategy == c.action) s += 1000f
            if (s > bestScore) { bestScore = s; best = c }
        }
        return best
    }

    private fun actionHeuristic(body: ArrayDeque<P>, ate: Boolean, tail: Boolean, region: Int, mobility: Int, foodDist: Int, h: Int): Float {
        if (body.isEmpty()) return -100000f
        val ratio = region.toFloat() / max(1, body.size)
        var s = 0f
        s += min(region, 100) * 18f
        s += mobility * 115f
        s += if (tail) 950f else -2200f
        s += when {
            ratio >= 2.0f -> 1100f
            ratio >= 1.5f -> 700f
            ratio >= 1.1f -> 250f
            ratio >= 0.85f -> -500f
            else -> -3000f
        }
        if (foodDist >= 0) {
            val urgency = if (h > 40) 2.2f else if (h > 20) 1.2f else 0.45f
            s += urgency * (260f / (foodDist + 1))
        }
        if (ate) s += if (tail && ratio >= 1.25f) 2800f else -1800f
        val head = body.first()
        val edge = min(min(head.x, cols - 1 - head.x), min(head.y, rows - 1 - head.y))
        if (body.size > 30) s -= max(0, 2 - edge) * 250f
        return s
    }

    private fun isSafeCandidate(body: ArrayDeque<P>, ate: Boolean, tail: Boolean, region: Int, mobility: Int): Boolean {
        if (body.isEmpty()) return false
        val ratio = region.toFloat() / max(1, body.size)
        if (ate && !tail) return false
        if (!tail && body.size >= 18) return false
        if (ratio < 0.78f) return false
        if (mobility <= 0) return false
        if (body.size >= 80 && ratio < 1.0f) return false
        if (body.size >= 130 && ratio < 1.15f) return false
        return true
    }

    // ---------- RL ----------
    private fun qIndex(state: Int, action: Int): Int = state * ACTIONS + action
    private fun qValue(state: Int, action: Int): Float = q[qIndex(state, action)]

    private fun learnFromTransition(state: Int, action: Int, reward: Float, nextState: Int, done: Boolean) {
        if (state !in 0 until STATE_COUNT || action !in 0..3) return
        val t = Transition(state, action, reward.coerceIn(-10f, 10f), nextState.coerceIn(0, STATE_COUNT - 1), done)
        tdUpdate(t)
        synchronized(replayLock) {
            if (replay.size >= replayCapacity) replay.removeFirst()
            replay.addLast(t)
        }
        if ((++replayUpdates and 15L) == 0L) replayTrain(16)
        epsilon = max(epsilonMin, epsilon * epsilonDecay)
    }

    private fun tdUpdate(t: Transition) {
        val idx = qIndex(t.state, t.action)
        val lock = qLocks[t.state and 63]
        synchronized(lock) {
            val old = q[idx]
            var nextMax = 0f
            if (!t.done) {
                nextMax = -Float.MAX_VALUE
                val base = t.nextState * ACTIONS
                for (a in 0 until ACTIONS) nextMax = max(nextMax, q[base + a])
                if (nextMax == -Float.MAX_VALUE) nextMax = 0f
            }
            val v = visits[idx] + 1
            visits[idx] = v
            val alpha = max(0.008f, baseAlpha / (1f + 0.018f * min(v, 250)))
            val target = t.reward + if (t.done) 0f else gamma * nextMax
            q[idx] = old + alpha * (target - old)
        }
    }

    private fun replayTrain(batch: Int) {
        val local = ArrayList<Transition>(batch)
        synchronized(replayLock) {
            if (replay.isEmpty()) return
            val n = min(batch, replay.size)
            repeat(n) {
                val idx = ThreadLocalRandom.current().nextInt(replay.size)
                local.add(replay.elementAt(idx))
            }
        }
        for (t in local) tdUpdate(t)
    }

    private fun stateKey(body: ArrayDeque<P>, heading: P, target: P, h: Int): Int {
        val head = body.firstOrNull() ?: P(0, 0)
        val dx = target.x - head.x
        val dy = target.y - head.y
        val foodDir = if (abs(dx) >= abs(dy)) {
            if (dx >= 0) 3 else 2
        } else {
            if (dy >= 0) 1 else 0
        }
        val danger = dangerMask(body, heading, target)
        val mobility = countSafeMoves(body, heading, target).coerceIn(0, 3)
        val region = (freeRegion(body) * 4 / max(1, total - body.size)).coerceIn(0, 3)
        val hungerBucket = when {
            h < 10 -> 0
            h < 25 -> 1
            h < 50 -> 2
            h < 100 -> 3
            else -> 4
        }
        val lenBucket = when {
            body.size < 5 -> 0
            body.size < 12 -> 1
            body.size < 25 -> 2
            body.size < 45 -> 3
            body.size < 70 -> 4
            body.size < 100 -> 5
            body.size < 150 -> 6
            else -> 7
        }
        val tail = if (tailReachable(body)) 1 else 0
        val headDir = dirs.indexOf(heading).coerceIn(0, 3)
        var k = foodDir
        k = k * 16 + danger
        k = k * 4 + mobility
        k = k * 4 + region
        k = k * 5 + hungerBucket
        k = k * 8 + lenBucket
        k = k * 2 + tail
        k = k * 4 + headDir
        return k.coerceIn(0, STATE_COUNT - 1)
    }

    private fun dangerMask(body: ArrayDeque<P>, heading: P, target: P): Int {
        var mask = 0
        for (a in 0 until 4) {
            val d = dirs[a]
            if (isReverse(d, heading) || !legalDirection(d, body, target)) mask = mask or (1 shl a)
        }
        return mask
    }

    // ---------- Simulation / safety ----------
    private fun simulate(body: ArrayDeque<P>, d: P, target: P): SimResult {
        val b = ArrayDeque(body)
        if (b.isEmpty()) return SimResult(b, false)
        val nh = P(b.first().x + d.x, b.first().y + d.y)
        if (!inside(nh)) return SimResult(ArrayDeque(), false)
        val ate = nh == target
        if (b.contains(nh) && !(nh == b.last() && !ate)) return SimResult(ArrayDeque(), ate)
        b.addFirst(nh)
        if (!ate) b.removeLast()
        return SimResult(b, ate)
    }

    private fun freeRegion(body: Collection<P>): Int {
        if (body.isEmpty()) return 0
        val blocked = BooleanArray(total)
        for (p in body) if (inside(p)) blocked[p.y * cols + p.x] = true
        val start = body.first()
        val si = start.y * cols + start.x
        blocked[si] = false
        val visited = bfsVisited.get()
        val que = bfsQueue.get()
        Arrays.fill(visited, false)
        var head = 0
        var tail = 0
        que[tail++] = si
        visited[si] = true
        var count = 0
        while (head < tail) {
            val cur = que[head++]
            count++
            val x = cur % cols
            val y = cur / cols
            if (x > 0) { val ni = cur - 1; if (!blocked[ni] && !visited[ni]) { visited[ni] = true; que[tail++] = ni } }
            if (x < cols - 1) { val ni = cur + 1; if (!blocked[ni] && !visited[ni]) { visited[ni] = true; que[tail++] = ni } }
            if (y > 0) { val ni = cur - cols; if (!blocked[ni] && !visited[ni]) { visited[ni] = true; que[tail++] = ni } }
            if (y < rows - 1) { val ni = cur + cols; if (!blocked[ni] && !visited[ni]) { visited[ni] = true; que[tail++] = ni } }
        }
        return count
    }

    private fun tailReachable(body: Collection<P>): Boolean {
        if (body.isEmpty()) return false
        val head = body.first()
        val tail = body.last()
        if (head == tail) return true
        return pathDistance(head, tail, body, allowTail = true) >= 0
    }

    private fun countSafeMoves(body: Collection<P>, heading: P, target: P): Int {
        if (body.isEmpty()) return 0
        return dirs.count { d ->
            !isReverse(d, heading) && legalDirection(d, body, target)
        }
    }

    private fun pathDistance(start: P, target: P, body: Collection<P>, allowTail: Boolean): Int {
        if (!inside(start) || !inside(target)) return -1
        if (start == target) return 0
        val blocked = BooleanArray(total)
        for (p in body) if (inside(p)) blocked[p.y * cols + p.x] = true
        if (allowTail && body.isNotEmpty()) blocked[body.last().y * cols + body.last().x] = false
        blocked[start.y * cols + start.x] = false
        val visited = bfsVisited.get()
        val que = bfsQueue.get()
        Arrays.fill(visited, false)
        var head = 0
        var tail = 0
        val si = start.y * cols + start.x
        val ti = target.y * cols + target.x
        que[tail++] = si
        visited[si] = true
        val dist = IntArray(total) { -1 }
        dist[si] = 0
        while (head < tail) {
            val cur = que[head++]
            val cd = dist[cur]
            val x = cur % cols
            val y = cur / cols
            if (cur == ti) return cd
            fun add(ni: Int) {
                if (!blocked[ni] && !visited[ni]) {
                    visited[ni] = true
                    dist[ni] = cd + 1
                    que[tail++] = ni
                }
            }
            if (x > 0) add(cur - 1)
            if (x < cols - 1) add(cur + 1)
            if (y > 0) add(cur - cols)
            if (y < rows - 1) add(cur + cols)
        }
        return -1
    }

    private fun legalDirection(d: P, body: Collection<P>, target: P): Boolean {
        if (body.isEmpty() || isReverse(d, dirForBody(body))) return false
        val h = body.first()
        val nh = P(h.x + d.x, h.y + d.y)
        if (!inside(nh)) return false
        val ate = nh == target
        return !body.contains(nh) || (nh == body.last() && !ate)
    }

    private fun dirForBody(body: Collection<P>): P {
        if (body.size < 2) return dir
        val a = body.elementAt(0)
        val b = body.elementAt(1)
        return P(a.x - b.x, a.y - b.y)
    }

    private fun isReverse(a: P, b: P): Boolean = a.x == -b.x && a.y == -b.y
    private fun inside(p: P): Boolean = p.x in 0 until cols && p.y in 0 until rows

    private fun distance(a: P, b: P, body: Collection<P>, avoid: Boolean): Int {
        return if (avoid) pathDistance(a, b, body, true) else abs(a.x - b.x) + abs(a.y - b.y)
    }

    private fun freeRegionAfterMove(d: P, ate: Boolean): Int = freeRegion(simulate(snake, d, food).body)

    private fun dangerLevel(body: Collection<P>, heading: P, target: P): Int {
        val m = dangerMask(body, heading, target)
        val blocked = Integer.bitCount(m)
        return when {
            blocked >= 3 -> 5
            blocked == 2 -> 4
            blocked == 1 -> 3
            else -> 1
        }
    }

    private fun placeFood() {
        val free = ArrayList<P>(total - snake.size)
        val occupied = snake.toHashSet()
        for (y in 0 until rows) for (x in 0 until cols) {
            val p = P(x, y)
            if (!occupied.contains(p)) free.add(p)
        }
        if (free.isNotEmpty()) food = free[ThreadLocalRandom.current().nextInt(free.size)]
    }

    // ---------- Death / persistence ----------
    private fun die(cause: String) {
        if (gameOver) return
        gameOver = true
        deathCause = cause
        when (cause) {
            "WALL" -> deathWall++
            "SELF" -> deathSelf++
            "TRAP", "HUNGER" -> deathTrap++
        }
        totalGames++
        recentScores.addLast(score)
        while (recentScores.size > 30) recentScores.removeFirst()
        bestTrainingScore = max(bestTrainingScore, score)
        lastDeathInfo = "$cause · 长度 ${snake.size} · 分数 $score"
        if (lastState >= 0 && lastAction >= 0) {
            val s = stateKey(snake, dir, food, hunger)
            learnFromTransition(lastState, lastAction, -8f, s, true)
        }
        try {
            if (Build.VERSION.SDK_INT >= 26) vibrator?.vibrate(VibrationEffect.createOneShot(100, VibrationEffect.DEFAULT_AMPLITUDE))
        } catch (_: Throwable) {}
        saveLearning()
        if (trainingMode && !reinforceTraining) {
            reset()
        }
    }

    private fun saveLearning() {
        prefs.edit()
            .putLong("v2_episodes", episodes)
            .putLong("v2_steps", learnedSteps)
            .putLong("v2_foods", learnedFoods)
            .putInt("v2_best", bestTrainingScore)
            .putFloat("v2_epsilon", epsilon)
            .putInt("stat_wall", deathWall)
            .putInt("stat_self", deathSelf)
            .putInt("stat_trap", deathTrap)
            .putInt("stat_total", totalGames)
            .apply()
    }

    // ---------- Reinforcement training ----------
    private fun startParallelTraining() {
        if (trainActive) return
        reinforceTraining = true
        trainingMode = true
        aiMode = 1
        trainActive = true
        trainThreads.clear()
        repeat(TRAIN_THREADS) { i ->
            val t = Thread({
                val game = TrainGame(System.nanoTime() xor (i.toLong() * -7046029254386353131L))
                while (trainActive) {
                    game.playOneGame()
                }
            }, "snake-train-$i")
            t.isDaemon = true
            t.priority = Thread.MAX_PRIORITY
            t.start()
            trainThreads.add(t)
        }
    }

    private fun stopParallelTraining() {
        if (!trainActive) {
            reinforceTraining = false
            return
        }
        trainActive = false
        reinforceTraining = false
        val deadline = System.currentTimeMillis() + 1800
        for (t in trainThreads) {
            try {
                val left = deadline - System.currentTimeMillis()
                if (left > 0) t.join(left)
            } catch (_: Throwable) {}
        }
        trainThreads.clear()
        saveLearning()
        reset()
    }

    private inner class TrainGame(seed: Long) {
        private val rng = Random(seed)
        private val body = ArrayDeque<P>()
        private var heading = P(1, 0)
        private var target = P(7, 7)
        private var h = 0
        private var s = 0
        private var localSteps = 0

        fun playOneGame() {
            body.clear()
            body.add(P(7, 7))
            heading = P(1, 0)
            h = 0
            s = 0
            localSteps = 0
            randomFood()
            var over = false
            while (!over && trainActive && localSteps < 30000) {
                val state = stateKey(body, heading, target, h)
                val decision = chooseMove(body, heading, target, h, training = true)
                if (decision == null) break
                val action = decision.action
                val d = decision.direction
                val nh = P(body.first().x + d.x, body.first().y + d.y)
                if (!inside(nh)) {
                    learnFromTransition(state, action, -8f, state, true)
                    over = true
                    continue
                }
                val ate = nh == target
                if (body.contains(nh) && !(nh == body.last() && !ate)) {
                    learnFromTransition(state, action, -8f, state, true)
                    over = true
                    continue
                }
                body.addFirst(nh)
                var reward = 0.02f
                if (ate) {
                    s += 10 + body.size
                    h = 0
                    learnedFoods++
                    reward += 3.5f + min(body.size, 150) * 0.01f
                    randomFood()
                } else {
                    body.removeLast()
                    h++
                    if (h > 500) {
                        learnFromTransition(state, action, -7f, state, true)
                        over = true
                        continue
                    }
                    val r = freeRegion(body)
                    reward += if (tailReachable(body)) 0.04f else -0.10f
                    reward += min(0.08f, countSafeMoves(body, heading, target) * 0.015f)
                    if (r < body.size * 0.8f) reward -= 0.25f
                }
                val next = stateKey(body, heading, target, h)
                learnFromTransition(state, action, reward, next, false)
                learnedSteps++
                localSteps++
                if ((localSteps and 31) == 0) replayTrain(8)
                if (ate) bestTrainingScore = max(bestTrainingScore, s)
                // The same policy is used; update heading only after the transition.
                heading = d
            }
            episodes++
            if ((episodes and 31L) == 0L) saveLearning()
        }

        private fun randomFood() {
            val free = ArrayList<P>()
            val occupied = body.toHashSet()
            for (y in 0 until rows) for (x in 0 until cols) {
                val p = P(x, y)
                if (!occupied.contains(p)) free.add(p)
            }
            if (free.isNotEmpty()) target = free[rng.nextInt(free.size)]
        }
    }

    // ---------- Drawing ----------
    override fun onDraw(c: Canvas) {
        super.onDraw(c)
        c.drawColor(bgColor)
        val usableW = width.toFloat()
        val usableH = height.toFloat()
        cell = min(usableW / cols, usableH / rows)
        ox = (usableW - cell * cols) / 2f
        oy = (usableH - cell * rows) / 2f

        gridPaint.style = Paint.Style.STROKE
        gridPaint.strokeWidth = 1f
        gridPaint.color = gridColor
        gridPaint.alpha = 55
        for (x in 0..cols) c.drawLine(ox + x * cell, oy, ox + x * cell, oy + rows * cell, gridPaint)
        for (y in 0..rows) c.drawLine(ox, oy + y * cell, ox + cols * cell, oy + y * cell, gridPaint)
        gridPaint.alpha = 255

        drawFood(c)
        drawSnake(c)
        drawEffects(c)
        drawDebug(c)
    }

    private fun drawFood(c: Canvas) {
        val cx = ox + (food.x + 0.5f) * cell
        val cy = oy + (food.y + 0.5f) * cell
        foodPaint.color = Color.rgb(231, 76, 60)
        foodPaint.style = Paint.Style.FILL
        c.drawCircle(cx, cy, cell * 0.32f, foodPaint)
        foodPaint.color = Color.WHITE
        c.drawCircle(cx - cell * 0.10f, cy - cell * 0.10f, cell * 0.06f, foodPaint)
    }

    private fun drawSnake(c: Canvas) {
        val size = cell * 0.72f
        snake.forEachIndexed { i, p ->
            val color = if (rainbowSkin) hsv[(i * 13 + (System.currentTimeMillis() / 10).toInt()) % 360] else if (i == 0) headColor else bodyColor
            snakePaint.color = color
            val l = ox + p.x * cell + (cell - size) / 2f
            val t = oy + p.y * cell + (cell - size) / 2f
            c.drawRoundRect(l, t, l + size, t + size, cell * 0.16f, cell * 0.16f, snakePaint)
        }
        if (snake.isNotEmpty()) {
            val p = snake.first()
            headPaint.color = if (rainbowSkin) Color.WHITE else headColor
            val cx = ox + (p.x + 0.5f) * cell
            val cy = oy + (p.y + 0.5f) * cell
            val ex = cx + dir.x * cell * 0.18f
            val ey = cy + dir.y * cell * 0.18f
            headPaint.style = Paint.Style.FILL
            c.drawCircle(ex - dir.y * cell * 0.13f, ey + dir.x * cell * 0.13f, cell * 0.055f, headPaint)
            c.drawCircle(ex + dir.y * cell * 0.13f, ey - dir.x * cell * 0.13f, cell * 0.055f, headPaint)
        }
    }

    private fun drawEffects(c: Canvas) {
        for (p in particles) {
            paint.color = p.color
            paint.alpha = (255f * p.life.coerceIn(0f, 1f)).toInt()
            c.drawCircle(ox + p.x * cell, oy + p.y * cell, cell * 0.08f, paint)
        }
        paint.alpha = 255
    }

    private fun drawDebug(c: Canvas) {
        if (aiMode == 0 && !reinforceTraining) return
        // Keep the original HUD geometry: centered, 97%/720dp wide, 760 high,
        // anchored to the bottom with a 12px margin.
        val w = min(width * 0.97f, 720f)
        val h = 760f
        val left = (width - w) / 2f
        val top = max(12f, height - h - 12f)

        panel.color = Color.argb(232, 0, 0, 0)
        c.drawRoundRect(left, top, left + w, top + h, 22f, 22f, panel)
        border.style = Paint.Style.STROKE
        border.strokeWidth = 5f
        val d = lastDecision
        border.color = when (d?.danger ?: 1) {
            1 -> Color.GREEN
            2 -> Color.rgb(150, 255, 80)
            3 -> Color.YELLOW
            4 -> Color.rgb(255, 150, 0)
            else -> Color.RED
        }
        c.drawRoundRect(left, top, left + w, top + h, 22f, 22f, border)

        text.isFakeBoldText = true
        text.textSize = 20f
        text.color = Color.WHITE
        c.drawText(if (reinforceTraining) "强化训练 · V2" else "AI · V2", left + 18f, top + 34f, text)
        text.isFakeBoldText = false
        text.textSize = 13f
        text.color = Color.LTGRAY
        c.drawText("策略: ${d?.strategy ?: "等待决策"}", left + 18f, top + 58f, text)
        c.drawText("ε ${"%.4f".format(epsilon)}   Q学习步 ${learnedSteps}   回合 $episodes", left + 18f, top + 80f, text)
        c.drawText("食物 $learnedFoods   最佳 $bestTrainingScore   最近均分 ${recentAverage()}", left + 18f, top + 102f, text)
        c.drawText("分数 $score   长度 ${snake.size}   饥饿 $hunger   危险 ${d?.danger ?: 1}", left + 18f, top + 124f, text)

        val chartTop = top + 150f
        text.color = Color.rgb(120, 255, 180)
        text.textSize = 14f
        text.isFakeBoldText = true
        c.drawText("V2 Q / 安全候选", left + 16f, chartTop, text)
        text.isFakeBoldText = false

        val candidates = d?.candidates ?: emptyList()
        var y = chartTop + 20f
        for (cand in candidates) {
            val barW = w - 34f
            val normalized = ((cand.total / 5000f) + 0.5f).coerceIn(0f, 1f)
            barPaint.color = Color.rgb(38, 38, 38)
            c.drawRoundRect(left + 16f, y, left + 16f + barW, y + 25f, 4f, 4f, barPaint)
            barPaint.color = when {
                !cand.safe -> Color.rgb(100, 55, 55)
                cand.ate -> Color.rgb(46, 204, 113)
                cand.tailOk -> Color.rgb(241, 196, 15)
                else -> Color.rgb(230, 126, 34)
            }
            c.drawRoundRect(left + 16f, y, left + 16f + barW * normalized, y + 25f, 4f, 4f, barPaint)
            text.textSize = 12f
            text.color = Color.WHITE
            c.drawText("${actionName(cand.action)}  Q ${"%.2f".format(cand.q)}  空${cand.region}  尾${if (cand.tailOk) "Y" else "N"}  食${if (cand.foodDist < 0) "∞" else cand.foodDist}", left + 23f, y + 18f, text)
            y += 29f
        }

        val graphTop = top + 320f
        text.textSize = 14f
        text.color = Color.rgb(120, 255, 180)
        text.isFakeBoldText = true
        c.drawText("历史分数", left + 16f, graphTop, text)
        text.isFakeBoldText = false
        drawLearningCurve(c, left + 16f, graphTop + 8f, w * 0.56f, 85f)

        text.color = Color.WHITE
        text.textSize = 13f
        c.drawText("死亡统计", left + w * 0.60f, graphTop, text)
        c.drawText("墙 $deathWall", left + w * 0.60f, graphTop + 24f, text)
        c.drawText("身 $deathSelf", left + w * 0.60f, graphTop + 44f, text)
        c.drawText("陷阱/饥饿 $deathTrap", left + w * 0.60f, graphTop + 64f, text)
        c.drawText("总回合 $totalGames", left + w * 0.60f, graphTop + 84f, text)

        val buttonTop = top + h - 58f
        reinforceButtonRect.set(left + w - 150f, buttonTop, left + w - 16f, buttonTop + 40f)
        barPaint.color = if (reinforceTraining) Color.rgb(192, 57, 43) else Color.rgb(39, 174, 96)
        c.drawRoundRect(reinforceButtonRect, 8f, 8f, barPaint)
        text.color = Color.WHITE
        text.textSize = 14f
        text.isFakeBoldText = true
        c.drawText(if (reinforceTraining) "停止强化" else "强化", reinforceButtonRect.left + 30f, reinforceButtonRect.top + 26f, text)
        text.isFakeBoldText = false
    }

    private fun drawLearningCurve(c: Canvas, left: Float, top: Float, w: Float, h: Float) {
        if (recentScores.size < 2) {
            text.textSize = 11f
            text.color = Color.DKGRAY
            c.drawText("等待训练数据…", left + 5f, top + 20f, text)
            return
        }
        val values = recentScores.toList()
        val maxScore = max(1, values.max())
        val step = w / (values.size - 1).coerceAtLeast(1)
        val path = Path()
        values.forEachIndexed { i, v ->
            val x = left + i * step
            val y = top + h - h * v / maxScore.toFloat()
            if (i == 0) path.moveTo(x, y) else path.lineTo(x, y)
        }
        barPaint.style = Paint.Style.STROKE
        barPaint.strokeWidth = 3f
        barPaint.color = Color.rgb(120, 255, 180)
        c.drawPath(path, barPaint)
        barPaint.style = Paint.Style.FILL
    }

    private fun recentAverage(): Int = if (recentScores.isEmpty()) 0 else recentScores.sum() / recentScores.size
    private fun actionName(a: Int): String = when (a) { 0 -> "↑"; 1 -> "↓"; 2 -> "←"; else -> "→" }

    private fun spawnFoodEffect(p: P) {
        repeat(12) {
            val angle = ThreadLocalRandom.current().nextDouble(0.0, Math.PI * 2.0)
            val speed = ThreadLocalRandom.current().nextDouble(0.04, 0.15)
            particles.add(Particle(p.x + 0.5f, p.y + 0.5f, (kotlin.math.cos(angle) * speed).toFloat(), (kotlin.math.sin(angle) * speed).toFloat(), 1f, Color.rgb(241, 196, 15)))
        }
    }

    private fun updateEffects(dt: Float) {
        val it = particles.iterator()
        while (it.hasNext()) {
            val p = it.next()
            p.x += p.vx * dt
            p.y += p.vy * dt
            p.life -= 0.045f * dt
            if (p.life <= 0f) it.remove()
        }
        flash = max(0f, flash - 0.06f * dt)
    }

    // ---------- Touch ----------
    private var touchStartX = 0f
    private var touchStartY = 0f

    override fun onTouchEvent(e: MotionEvent): Boolean {
        when (e.actionMasked) {
            MotionEvent.ACTION_DOWN -> {
                touchStartX = e.x
                touchStartY = e.y
                return true
            }
            MotionEvent.ACTION_UP -> {
                if (reinforceButtonRect.contains(e.x, e.y)) {
                    if (System.currentTimeMillis() - lastReinforceTap > 350L) {
                        lastReinforceTap = System.currentTimeMillis()
                        setReinforceTraining(!reinforceTraining)
                    }
                    return true
                }
                if (reinforceTraining) return true
                if (gameOver) {
                    reset()
                    return true
                }
                if (aiMode != 0 || snake.isEmpty()) return true
                val dx = e.x - touchStartX
                val dy = e.y - touchStartY
                val d = if (abs(dx) > abs(dy)) P(if (dx > 0) 1 else -1, 0) else P(0, if (dy > 0) 1 else -1)
                if (!isReverse(d, dir)) { queue.clear(); queue.add(d) }
                return true
            }
        }
        return true
    }

    override fun onDetachedFromWindow() {
        super.onDetachedFromWindow()
        trainActive = false
        reinforceTraining = false
        try { Choreographer.getInstance().removeFrameCallback(frame) } catch (_: Throwable) {}
    }
}
