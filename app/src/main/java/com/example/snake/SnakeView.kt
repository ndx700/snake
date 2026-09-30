package com.example.snake

import android.content.Context
import android.graphics.*
import android.media.AudioAttributes
import android.media.AudioFormat
import android.media.AudioManager
import android.media.AudioTrack
import android.media.ToneGenerator
import android.os.Build
import android.os.VibrationEffect
import android.os.Vibrator
import android.os.VibratorManager
import android.util.AttributeSet
import android.view.Choreographer
import android.view.MotionEvent
import android.view.View
import java.util.ArrayDeque
import java.util.concurrent.Callable
import java.util.concurrent.ExecutorService
import java.util.concurrent.Executors
import java.util.concurrent.Future
import kotlin.math.abs
import kotlin.math.max
import kotlin.math.min
import kotlin.random.Random

class SnakeView @JvmOverloads constructor(
    context: Context,
    attrs: AttributeSet? = null
) : View(context, attrs) {

    private val cols = 15
    private val rows = 15
    private var cell = 0f
    private var ox = 0f
    private var oy = 0f

    private data class P(val x: Int, val y: Int)

    private data class Candidate(
        val d: P, val score: Float, val reason: String, val legal: Boolean,
        val regionScore: Float = 0f, val mobilityScore: Float = 0f,
        val tailScore: Float = 0f, val foodScore: Float = 0f,
        val edgeScore: Float = 0f, val spaceScore: Float = 0f,
        val region: Int = 0, val mobility: Int = 0,
        val tailOk: Boolean = false, val foodDist: Int = -1, val ate: Boolean = false
    )

    private data class Snapshot(
        var strategy: String = "AUTO", var reason: String = "初始化",
        var danger: Int = 1, var region: Int = 1, var spaceRatio: Float = 1f,
        var tailReachable: Boolean = false, var foodReachable: Boolean = false,
        var foodDistance: Int = -1, var hunger: Int = 0, var chosen: P = P(0, 0),
        var candidates: List<Candidate> = emptyList(), var depth: Int = 0, var nodes: Int = 0,
        var hungerFactor: Float = 1f, var regionWeight: Float = 11f,
        var strategyId: Int = -1, var qValue: Float = 0f, var nVisits: Int = 0,
        var forceEatActive: Boolean = false, var forceEatSafe: Boolean = false,
        var safeFollowMode: Boolean = false
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

    private var gameSpeed = 220L
    private val gameSpeedMin = 45L
    private val gameSpeedStart = 220L
    private var accumulator = 0L
    private var lastFrame = 0L

    private var combo = 0
    private var hunger = 0
    private var deathCause = "无"
    private var lastDeathInfo = ""
    private var ai = Snapshot()

    private var wRegion = 11f
    private var wMobility = 35f
    private var wTailGood = 180f
    private var wTailBad = -250f
    private var wFoodNear = 300f
    private var wFoodAte = 850f
    private var wEdge = 55f
    private var wSpace = 30f

    private val wRegion0 = 11f
    private val wMobility0 = 35f
    private val wTailGood0 = 180f
    private val wTailBad0 = -250f
    private val wFoodNear0 = 300f
    private val wFoodAte0 = 850f
    private val wEdge0 = 55f
    private val wSpace0 = 30f

    private var aggression = 1.15f
    private var safetyMargin = 1.08f
    private var shortcutBonus = 0.90f

    private var deathWall = 0
    private var deathSelf = 0
    private var deathTrap = 0
    private var totalGames = 0

    private var lastLearnAction = "初始化（暂无死亡）"

    private val safeFollowLength = 32

    private val recentScores = ArrayDeque<Int>()
    private var bestRecentScore = 0

    private val q = Array(100) { FloatArray(4) }
    private val n = Array(100) { IntArray(4) }

    private var lastState = -1
    private var lastAction = -1
    private var steps = 0

    var onScoreChanged: ((Int) -> Unit)? = null
    var onMoneyChanged: ((Int) -> Unit)? = null

    private val prefs = context.getSharedPreferences("snake_prefs", Context.MODE_PRIVATE)

    private val vibrator: Vibrator? =
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
            (context.getSystemService(Context.VIBRATOR_MANAGER_SERVICE) as? VibratorManager)?.defaultVibrator
        } else {
            @Suppress("DEPRECATION")
            context.getSystemService(Context.VIBRATOR_SERVICE) as? Vibrator
        }

    private val toneGen: ToneGenerator? = try {
        ToneGenerator(AudioManager.STREAM_MUSIC, 85)
    } catch (_: Throwable) { null }

    private var bgm: BgmPlayer? = null

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
    private val barPaint = Paint(Paint.ANTI_ALIAS_FLAG)

    private var flash = 0f

    private val autoBeamHunger = 120
    private val hungerKillLimit = 500
    private var beamNodes = 0
    private var restartCountdown = 0L

    private var trainingMode = false
    private var reinforceTraining = false
    private var renderSkipCounter = 0
    private var trainStepsPerFrame = 10
    private var renderEveryN = 5
    private val reinforceButtonRect = RectF()
    private var lastReinforceTap = 0L

    private val aiPool: ExecutorService = run {
        val cores = Runtime.getRuntime().availableProcessors().coerceIn(4, 8)
        Executors.newFixedThreadPool(cores) { r ->
            Thread(r, "snake-ai").apply {
                isDaemon = true
                priority = Thread.MAX_PRIORITY
            }
        }
    }

    private val tlVisited: ThreadLocal<BooleanArray> =
        ThreadLocal.withInitial { BooleanArray(cols * rows) }
    private val tlQueue: ThreadLocal<IntArray> =
        ThreadLocal.withInitial { IntArray(cols * rows) }

    private var aiStepStartNs = 0L
    private var aiStepBudgetNs = 15_000_000L

    private fun timeLeft(): Boolean =
        (System.nanoTime() - aiStepStartNs) < aiStepBudgetNs

    private fun budgetFor(speedMs: Long): Long = when {
        speedMs >= 150L -> 35_000_000L
        speedMs >= 80L  -> 18_000_000L
        speedMs >= 55L  -> 12_000_000L
        else            -> 8_000_000L
    }

    private fun hungerForceEat(): Int = when {
        snake.size < 20 -> 50
        snake.size < 35 -> 70
        snake.size < 55 -> 100
        snake.size < 80 -> 140
        else -> 200
    }

    private fun vibrateEat() {
        vibrator?.let {
            try {
                if (Build.VERSION.SDK_INT >= 26) {
                    it.vibrate(VibrationEffect.createWaveform(longArrayOf(0, 12, 25, 12), -1))
                } else {
                    @Suppress("DEPRECATION")
                    it.vibrate(longArrayOf(0, 12, 25, 12), -1)
                }
            } catch (_: Throwable) {}
        }
    }

    private fun vibrateDeath() {
        vibrator?.let {
            try {
                if (Build.VERSION.SDK_INT >= 26) {
                    it.vibrate(VibrationEffect.createOneShot(120, VibrationEffect.DEFAULT_AMPLITUDE))
                } else {
                    @Suppress("DEPRECATION")
                    it.vibrate(120)
                }
            } catch (_: Throwable) {}
        }
    }

    private fun playEatSound() {
        try { toneGen?.startTone(ToneGenerator.TONE_PROP_BEEP, 55) } catch (_: Throwable) {}
    }

    private val frame = object : Choreographer.FrameCallback {
        override fun doFrame(ns: Long) {
            if (!running) return
            if (lastFrame == 0L) lastFrame = ns
            val dt = ((ns - lastFrame) / 1_000_000L).coerceAtMost(100L)
            lastFrame = ns

            if (gameOver) {
                restartCountdown = 0L
            } else if (reinforceTraining) {
                var stepCount = 0
                while (stepCount < trainStepsPerFrame) {
                    updateGame()
                    stepCount++
                }
                accumulator = 0L
            } else {
                accumulator += dt
                var stepCount = 0
                val maxSteps = if (trainingMode) trainStepsPerFrame else Int.MAX_VALUE
                while (accumulator >= gameSpeed && stepCount < maxSteps) {
                    updateGame()
                    if (gameOver && !trainingMode) break
                    accumulator -= gameSpeed
                    stepCount++
                }
                if (stepCount >= maxSteps) accumulator = 0L
            }

            if (!reinforceTraining) updateEffects(dt / 16f)

            val shouldRender = if (reinforceTraining) {
                (++renderSkipCounter % renderEveryN == 0)
            } else if (trainingMode) {
                (++renderSkipCounter % renderEveryN == 0)
            } else true
            if (shouldRender) invalidate()
            Choreographer.getInstance().postFrameCallback(this)
        }
    }

    init {
        highScore = prefs.getInt("high_score", 0)
        money = prefs.getInt("money", 0)
        trainingMode = prefs.getBoolean("training_mode", false)
        aggression = prefs.getFloat("learn_aggression", 1.15f)
        safetyMargin = prefs.getFloat("learn_safety", 1.08f)
        shortcutBonus = prefs.getFloat("learn_shortcut", 0.90f)
        wRegion = prefs.getFloat("w_region", wRegion0)
        wMobility = prefs.getFloat("w_mobility", wMobility0)
        wTailGood = prefs.getFloat("w_tail_good", wTailGood0)
        wTailBad = prefs.getFloat("w_tail_bad", wTailBad0)
        wFoodNear = prefs.getFloat("w_food_near", wFoodNear0)
        wFoodAte = prefs.getFloat("w_food_ate", wFoodAte0)
        wEdge = prefs.getFloat("w_edge", wEdge0)
        wSpace = prefs.getFloat("w_space", wSpace0)

        // ★ 收紧权重上限，防止学炸
        fun fixW(v: Float, base: Float) = v.coerceIn(base * 0.65f, base * 1.6f)
        wRegion = fixW(wRegion, wRegion0)
        wMobility = fixW(wMobility, wMobility0)
        wTailGood = fixW(wTailGood, wTailGood0)
        wFoodNear = fixW(wFoodNear, wFoodNear0)
        wFoodAte = fixW(wFoodAte, wFoodAte0)
        wEdge = fixW(wEdge, wEdge0)
        wSpace = fixW(wSpace, wSpace0)
        wTailBad = wTailBad.coerceIn(wTailBad0 * 1.5f, wTailBad0 * 0.6f)
        aggression = aggression.coerceIn(0.85f, 1.50f)
        safetyMargin = safetyMargin.coerceIn(1.0f, 1.25f)

        lastLearnAction = prefs.getString("last_learn_action", "初始化（暂无死亡）") ?: "初始化"
        deathWall = prefs.getInt("stat_wall", 0)
        deathSelf = prefs.getInt("stat_self", 0)
        deathTrap = prefs.getInt("stat_trap", 0)
        totalGames = prefs.getInt("stat_total", 0)
        for (s in 0 until 100) for (a in 0 until 4) {
            q[s][a] = prefs.getFloat("q_${s}_$a", 0f)
            n[s][a] = prefs.getInt("n_${s}_$a", 0)
        }
        bgm = BgmPlayer()
        updateCurrentSkin()
        updateCurrentBoard()
        reset()
    }

    fun getAIMode(): Int = aiMode

    fun setAIMode(m: Int) {
        aiMode = m
        invalidate()
    }

    fun setTrainingMode(b: Boolean) {
        trainingMode = b
        if (b) {
            aiMode = 1
            bgm?.stop()
            trainStepsPerFrame = 10
            renderEveryN = 5
            reset()
        } else {
            reinforceTraining = false
            trainStepsPerFrame = 10
            renderEveryN = 5
            if (running) bgm?.start()
            reset()
        }
        invalidate()
    }

    fun setReinforceTraining(enable: Boolean) {
        reinforceTraining = enable
        if (enable) {
            trainingMode = true
            aiMode = 1
            trainStepsPerFrame = 2000
            renderEveryN = 180
            gameSpeed = 1L
            bgm?.stop()
            if (!running) resume()
        } else {
            trainStepsPerFrame = 10
            renderEveryN = 5
            if (trainingMode) gameSpeed = 2L
        }
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
        bodyColor = body; headColor = head; rainbowSkin = rainbow
        snakePaint.color = body
        snakePaint.style = Paint.Style.STROKE
        snakePaint.strokeCap = Paint.Cap.ROUND
        snakePaint.strokeJoin = Paint.Join.ROUND
        snakePaint.strokeWidth = 0f
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
        snake.clear(); queue.clear()
        if (aiMode == 2) { snake.add(P(0, 0)); dir = P(0, 1) }
        else { snake.add(P(cols / 2, rows / 2)); dir = P(1, 0) }
        score = 0; combo = 0; hunger = 0
        gameOver = false; deathCause = "无"; lastDeathInfo = ""
        gameSpeed = if (trainingMode) 2L else gameSpeedStart
        accumulator = 0L; lastFrame = 0L
        particles.clear(); floats.clear(); flash = 0f; restartCountdown = 0L
        ai = Snapshot(chosen = dir)
        placeFood()
        onScoreChanged?.invoke(score)
        invalidate()
    }

    fun resume() {
        if (running) return
        running = true; lastFrame = 0L
        if (!trainingMode) bgm?.start()
        Choreographer.getInstance().postFrameCallback(frame)
    }

    fun pause() {
        running = false
        bgm?.stop()
        Choreographer.getInstance().removeFrameCallback(frame)
    }

    private fun updateGame() {
        if (gameOver) return

        if (reinforceTraining) gameSpeed = 1L
        else if (trainingMode) gameSpeed = 2L

        if (hunger >= hungerKillLimit) { die("HUNGER"); return }
        if (aiMode != 0) { queue.clear(); queue.add(chooseMove()) }
        if (queue.isNotEmpty()) {
            val requested = queue.removeFirst()
            if (!isReverse(requested, dir) && legalDirection(requested)) dir = requested
        }
        if (dir == P(0, 0)) return
        val nh = P(snake.first().x + dir.x, snake.first().y + dir.y)
        if (!inside(nh)) { die("WALL"); return }
        val ate = nh == food
        val body = snake.toList()
        val hitIndex = body.indexOf(nh)
        val tail = snake.last()
        if (hitIndex >= 0 && !(nh == tail && !ate)) {
            val sim = simulateOn(ArrayDeque(snake), dir)
            val region = freeRegion(sim.body)
            if (region < max(2, (snake.size * safetyMargin).toInt())) die("TRAP")
            else die("SELF")
            return
        }
        snake.addFirst(nh)
        if (ate) {
            val comboBonus = min(combo, 30) * 3
            val lenBonus = snake.size
            val gain = 10 + comboBonus + lenBonus
            score += gain
            combo++
            hunger = 0
            money += gain * 3 + 30

            if (score > highScore) highScore = score
            if (!reinforceTraining) {
                onScoreChanged?.invoke(score)
                onMoneyChanged?.invoke(money)
            }

            if (!trainingMode) {
                prefs.edit()
                    .putInt("money", money)
                    .putInt("high_score", highScore)
                    .apply()
                gameSpeed = max(gameSpeedMin, gameSpeedStart - snake.size * 2L)
                vibrateEat()
                playEatSound()
                spawnFoodEffect(nh)
            }

            placeFood()
            learn(2.5f + combo * 0.05f)
            if (!reinforceTraining) rewardEatStep()
        } else {
            snake.removeLast(); hunger++; combo = max(0, combo - 1)
            if (!reinforceTraining) learn(0.025f)
        }
        steps++
    }

    private fun safeFollowScore(cand: Candidate): Float {
        val sim = simulate(snake.first(), cand.d)
        val body = sim.body
        if (body.isEmpty()) return -1e9f
        val region = freeRegion(body)
        val tailOk = tailReachable(body)
        val ratio = region.toFloat() / max(1, snake.size)
        val mobility = countSafeMoves(body)
        var s = 0f
        if (!tailOk) s -= 9000f else s += 1800f
        s += when {
            ratio >= 2.0f -> 1400f
            ratio >= 1.5f -> 900f
            ratio >= 1.2f -> 450f
            ratio >= 1.0f -> 80f
            ratio >= 0.8f -> -1000f
            else -> -3500f
        }
        s += region * 20f
        s += mobility * 280f
        val edge = min(
            min(body.first().x, cols - 1 - body.first().x),
            min(body.first().y, rows - 1 - body.first().y)
        )
        s -= max(0, 3 - edge) * 450f
        val foodDist = distance(body.first(), food, body, true)
        if (foodDist >= 0 && ratio >= 1.6f && foodDist < snake.size / 3) {
            s += 200f / (foodDist + 1)
        }
        if (sim.ate && ratio >= 1.5f && tailOk) s += 700f
        return s
    }

    private fun chooseMove(): P {
        aiStepStartNs = System.nanoTime()
        // ★ 加大思考预算，保证 BFS 跑完
        aiStepBudgetNs = when {
            reinforceTraining -> 3_000_000L
            trainingMode -> 4_000_000L
            else -> budgetFor(gameSpeed)
        }

        val candidates: List<Candidate>
        val legal: List<Candidate>
        if (reinforceTraining) {
            val quick = ArrayList<Candidate>(4)
            for (d in dirs) {
                if (legalDirection(d)) {
                    quick.add(Candidate(d, 0f, "", true))
                } else {
                    quick.add(Candidate(d, -1e9f, "非法", false))
                }
            }
            candidates = quick
            legal = quick.filter { it.legal }
        } else {
            val futures: List<Future<Candidate>> = dirs.map { d ->
                aiPool.submit(Callable { evaluate(d) })
            }
            candidates = futures.map { it.get() }
            legal = candidates.filter { it.legal }
        }

        if (legal.isEmpty()) {
            ai = Snapshot(strategy = "NO MOVE", reason = "四个方向都无法安全前进", danger = 5, chosen = dir, candidates = candidates)
            return dir
        }

        val danger = calculateDanger()
        val state = learnState(snake.size, danger)
        val hungerFactor = when {
            hunger >= 60 -> 4f
            hunger >= 30 -> 2.5f
            hunger >= 15 -> 1.6f
            else -> 1f
        }
        val regionNow = freeRegion(snake)
        val foodDistNow = distance(snake.first(), food, snake, true)

        // ① 安全寻食
        val safeFood = findSafeFoodStep()
        if (safeFood != null) {
            val action = dirs.indexOfFirst { it == safeFood }.coerceAtLeast(0)
            lastState = state; lastAction = action
            ai = Snapshot(
                strategy = "SAFE_FOOD 安全寻食",
                reason = "存在安全路径到食物，吃完后尾巴仍可达",
                danger = danger, region = regionNow,
                spaceRatio = regionNow.toFloat() / max(1, snake.size),
                tailReachable = tailReachable(snake),
                foodReachable = true, foodDistance = foodDistNow,
                hunger = hunger, chosen = safeFood, candidates = candidates,
                depth = 2, nodes = legal.size,
                hungerFactor = hungerFactor, regionWeight = wRegion,
                strategyId = 0, qValue = q[state][action], nVisits = n[state][action],
                forceEatActive = false, forceEatSafe = true, safeFollowMode = false
            )
            return safeFood
        }

        // ② 追尾
        val tailStep = followTailStep(legal)
        if (tailStep != null) {
            val action = dirs.indexOfFirst { it == tailStep }.coerceAtLeast(0)
            lastState = state; lastAction = action
            ai = Snapshot(
                strategy = "FOLLOW_TAIL 追尾",
                reason = "无安全食物，沿最短路径追自己的尾巴",
                danger = danger, region = regionNow,
                spaceRatio = regionNow.toFloat() / max(1, snake.size),
                tailReachable = true,
                foodReachable = foodDistNow >= 0, foodDistance = foodDistNow,
                hunger = hunger, chosen = tailStep, candidates = candidates,
                depth = 1, nodes = legal.size,
                hungerFactor = hungerFactor, regionWeight = wRegion,
                strategyId = 1, qValue = q[state][action], nVisits = n[state][action],
                forceEatActive = false, forceEatSafe = false, safeFollowMode = true
            )
            return tailStep
        }

        // ③ 饥饿强制
        val forceEatThreshold = hungerForceEat()
        if (hunger >= forceEatThreshold && foodDistNow >= 0) {
            var best: Candidate? = null
            var bestScore = -1e30f
            for (cand in legal) {
                val sim = simulate(snake.first(), cand.d)
                if (!tailReachable(sim.body)) continue
                val fd = distance(sim.body.first(), food, sim.body, true)
                if (fd < 0) continue
                val r = freeRegion(sim.body)
                var sc = -fd * 20f + r * 5f
                if (sim.ate) sc += 1000f
                if (sc > bestScore) { bestScore = sc; best = cand }
            }
            if (best != null) {
                val action = dirs.indexOfFirst { it == best.d }.coerceAtLeast(0)
                lastState = state; lastAction = action
                ai = Snapshot(
                    strategy = "饥饿强制",
                    reason = "饥饿高压，在保尾前提下靠近食物",
                    danger = 3, region = regionNow,
                    spaceRatio = regionNow.toFloat() / max(1, snake.size),
                    tailReachable = true,
                    foodReachable = true, foodDistance = foodDistNow,
                    hunger = hunger, chosen = best.d, candidates = candidates,
                    depth = 1, nodes = legal.size,
                    hungerFactor = hungerFactor, regionWeight = wRegion,
                    strategyId = 0, qValue = q[state][action], nVisits = n[state][action],
                    forceEatActive = true, forceEatSafe = true, safeFollowMode = false
                )
                return best.d
            }
        }

        // ④ 兜底
        val survival = bestSurvivalStep(legal)
        val action = dirs.indexOfFirst { it == survival.d }.coerceAtLeast(0)
        lastState = state; lastAction = action
        ai = Snapshot(
            strategy = "SURVIVE 兜底",
            reason = "追尾路径不可用，选连通最大的合法步",
            danger = danger, region = regionNow,
            spaceRatio = regionNow.toFloat() / max(1, snake.size),
            tailReachable = tailReachable(snake),
            foodReachable = foodDistNow >= 0, foodDistance = foodDistNow,
            hunger = hunger, chosen = survival.d, candidates = candidates,
            depth = 1, nodes = legal.size,
            hungerFactor = hungerFactor, regionWeight = wRegion,
            strategyId = 1, qValue = q[state][action], nVisits = n[state][action],
            forceEatActive = false, forceEatSafe = false, safeFollowMode = false
        )
        return survival.d
    }

    private fun followTailStep(legal: List<Candidate>): P? {
        if (snake.size < 2) return null
        val path = shortestPath(snake.first(), snake.last(), snake, allowTail = true) ?: return null
        if (path.isEmpty()) return null
        val step = path.first()
        if (legal.none { it.d == step }) return null
        val sim = simulate(snake.first(), step)
        if (sim.body.isEmpty()) return null
        if (!tailReachable(sim.body)) return null
        val r = freeRegion(sim.body)
        if (r < 3 && snake.size < cols * rows - 5) return null
        return step
    }

    private fun findSafeFoodStep(): P? {
        val path = shortestPath(snake.first(), food, snake, allowTail = true) ?: return null
        if (path.isEmpty()) return null

        val simBody = ArrayDeque(snake)
        var ate = false
        for (step in path) {
            val nh = P(simBody.first().x + step.x, simBody.first().y + step.y)
            if (!inside(nh)) return null
            val willEat = nh == food
            if (simBody.contains(nh) && !(nh == simBody.last() && !willEat)) return null
            simBody.addFirst(nh)
            if (!willEat) simBody.removeLast()
            else ate = true
        }
        if (!ate) return null

        if (!tailReachable(simBody)) return null

        // ★ 后期按蛇长分级限制剩余空间，防止长蛇锁死
        val len = simBody.size
        val freeLeft = cols * rows - len
        if (len > 180 && freeLeft < 8) return null
        if (len > 150 && freeLeft < 12) return null
        if (len > 120 && freeLeft < 18) return null
        if (len > 90 && freeLeft < 25) return null
        if (len > 60 && freeLeft < 35) return null

        // 前期防切碎
        if (len <= 60 && freeLeft >= 20) {
            val r = freeRegion(simBody)
            if (r < max(4, freeLeft / 3)) return null
        }
        return path.first()
    }

    private fun shortestPath(start: P, target: P, body: Collection<P>, allowTail: Boolean): List<P>? {
        if (start == target) return emptyList()
        if (start.x !in 0 until cols || start.y !in 0 until rows) return null
        if (target.x !in 0 until cols || target.y !in 0 until rows) return null
        val total = cols * rows
        val visited = tlVisited.get()
        val queue = tlQueue.get()
        val parent = IntArray(total) { -1 }
        val parentDir = arrayOfNulls<P>(total)
        java.util.Arrays.fill(visited, 0, total, false)
        for (p in body) {
            if (p.x !in 0 until cols || p.y !in 0 until rows) continue
            val index = p.y * cols + p.x
            if (index in 0 until total) visited[index] = true
        }
        if (allowTail && body.isNotEmpty()) {
            val last = body.last()
            if (last.x in 0 until cols && last.y in 0 until rows) {
                val lastIndex = last.y * cols + last.x
                if (lastIndex in 0 until total) visited[lastIndex] = false
            }
        }
        val startIndex = start.y * cols + start.x
        val targetIndex = target.y * cols + target.x
        if (startIndex !in 0 until total || targetIndex !in 0 until total) return null
        visited[startIndex] = true
        var head = 0; var tail = 0
        queue[tail++] = startIndex
        var found = false
        while (head < tail) {
            val curr = queue[head++]
            if (curr == targetIndex) { found = true; break }
            val cx = curr % cols; val cy = curr / cols
            val tryDirs = arrayOf(
                P(0, -1) to (if (cy > 0) curr - cols else -1),
                P(0, 1) to (if (cy < rows - 1) curr + cols else -1),
                P(-1, 0) to (if (cx > 0) curr - 1 else -1),
                P(1, 0) to (if (cx < cols - 1) curr + 1 else -1)
            )
            for ((d, ni) in tryDirs) {
                if (ni < 0 || ni >= total) continue
                if (visited[ni]) continue
                visited[ni] = true
                parent[ni] = curr
                parentDir[ni] = d
                if (tail < total) queue[tail++] = ni
            }
        }
        if (!found) return null
        val steps = ArrayList<P>()
        var cur = targetIndex
        while (cur != startIndex) {
            val d = parentDir[cur] ?: return null
            steps.add(d)
            cur = parent[cur]
            if (cur < 0) return null
        }
        steps.reverse()
        return steps
    }

    private fun bestSurvivalStep(legal: List<Candidate>): Candidate {
        var best = legal.first()
        var bestScore = -1e30f
        val len = snake.size
        val tailPos = snake.last()
        val bodySet = snake.toHashSet()

        val tailW = (wTailGood / wTailGood0).coerceIn(0.8f, 1.3f)
        val spaceW = (wSpace / wSpace0).coerceIn(0.8f, 1.3f)
        val foodW = (wFoodNear / wFoodNear0).coerceIn(0.8f, 1.3f)

        for (cand in legal) {
            val sim = simulate(snake.first(), cand.d)
            if (sim.body.isEmpty()) continue
            val nh = sim.body.first()
            val r = freeRegion(sim.body)
            val t = tailReachable(sim.body)
            val mob = countSafeMoves(sim.body)
            val freeLeft = cols * rows - sim.body.size
            var sc = 0f

            if (t) sc += 100000f * tailW else {
                sc -= 200000f
                if (sc > bestScore) { bestScore = sc; best = cand }
                continue
            }

            sc += r * 150f * spaceW
            if (freeLeft > 0) sc += (r.toFloat() / freeLeft) * 12000f * spaceW
            sc += mob * 400f

            var bodyAdj = 0
            for (d in dirs) {
                val p = P(nh.x + d.x, nh.y + d.y)
                if (bodySet.contains(p) || sim.body.contains(p)) bodyAdj++
            }
            sc += bodyAdj * 800f

            val dToTail = distance(nh, tailPos, sim.body, true)
            if (dToTail >= 0) {
                sc += 12000f / (dToTail + 1)
                if (dToTail > 6) sc -= (dToTail - 6) * 200f
            }

            val fd = distance(nh, food, sim.body, true)
            if (fd >= 0) sc += (120f * foodW) / (fd + 1)

            if (len >= 100) sc += r * 200f

            // ★ 边缘惩罚加强
            val nx = sim.body.first().x
            val ny = sim.body.first().y
            val edge = min(min(nx, cols - 1 - nx), min(ny, rows - 1 - ny))
            sc -= max(0, 3 - edge) * 800f

            val hx0 = snake.first().x
            val hy0 = snake.first().y
            val atEdgeNow = hx0 == 0 || hx0 == cols - 1 || hy0 == 0 || hy0 == rows - 1
            if (!atEdgeNow && edge == 0 && snake.size > 20) sc -= 6000f
            if (nx == 0 || nx == cols - 1 || ny == 0 || ny == rows - 1) sc -= 500f

            if (sim.ate) sc += 3000f

            if (sc > bestScore) { bestScore = sc; best = cand }
        }
        return best
    }

    private fun evaluate(d: P): Candidate {
        if (!legalDirection(d)) return Candidate(d, -1e9f, "撞墙/身体", false)
        val sim = simulate(snake.first(), d)
        val region = freeRegion(sim.body)
        val tail = tailReachable(sim.body)
        val foodDist = distance(sim.body.first(), food, sim.body, true)
        val ate = sim.ate
        val mobility = countSafeMoves(sim.body)
        val hungerFactor = when {
            hunger >= 60 -> 4f
            hunger >= 30 -> 2.5f
            hunger >= 15 -> 1.6f
            else -> 1f
        }
        val lenBoost = if (snake.size >= safeFollowLength) (snake.size.toFloat() / safeFollowLength).coerceIn(1f, 3f) else 1f
        val effRegionW = wRegion * lenBoost
        val effTailGood = wTailGood * lenBoost
        val effTailBad = wTailBad * lenBoost
        val regionScoreVal = region * effRegionW
        val mobilityScoreVal = mobility * wMobility
        val tailScoreVal = if (tail) effTailGood else effTailBad
        var foodScoreVal = if (foodDist >= 0) hungerFactor * aggression * (wFoodNear / (foodDist + 1)) else -450f * hungerFactor
        if (ate) foodScoreVal += wFoodAte * aggression

        var eatPenalty = 0f
        if (ate) {
            val afterSize = sim.body.size
            val needSpace = (afterSize * safetyMargin).toInt() + 2
            if (!tail || region < needSpace) {
                eatPenalty = -2500f - snake.size * 35f
            } else {
                val after = ArrayDeque(sim.body)
                val dx = after.last().x - after.first().x
                val dy = after.last().y - after.first().y
                val follow = when {
                    abs(dx) >= abs(dy) && dx != 0 -> P(if (dx > 0) 1 else -1, 0)
                    dy != 0 -> P(0, if (dy > 0) 1 else -1)
                    else -> null
                }
                if (follow != null && canSim(after, follow)) {
                    val next = simulateOn(after, follow)
                    val r2 = freeRegion(next.body)
                    val t2 = tailReachable(next.body)
                    if (!t2 || r2 < (afterSize * 0.85f).toInt()) {
                        eatPenalty = -1500f - snake.size * 25f
                    }
                }
            }
        }

        val edge = min(min(sim.body.first().x, cols - 1 - sim.body.first().x), min(sim.body.first().y, rows - 1 - sim.body.first().y))
        val edgeScoreVal = -max(0, 2 - edge) * wEdge
        val spacePenalty = max(0f, snake.size * safetyMargin - region.toFloat())
        val spaceScoreVal = -spacePenalty * wSpace
        val total = regionScoreVal + mobilityScoreVal + tailScoreVal + foodScoreVal +
                edgeScoreVal + spaceScoreVal + eatPenalty
        val reason = when {
            ate && eatPenalty < 0 -> "吃完会困死，避开"
            ate -> "马上吃到食物"
            tail -> "保持尾巴可达"
            else -> "扩大可用空间"
        }
        return Candidate(
            d = d, score = total, reason = reason, legal = true,
            regionScore = regionScoreVal, mobilityScore = mobilityScoreVal,
            tailScore = tailScoreVal, foodScore = foodScoreVal,
            edgeScore = edgeScoreVal, spaceScore = spaceScoreVal,
            region = region, mobility = mobility, tailOk = tail,
            foodDist = foodDist, ate = ate
        )
    }

    private fun bfsScore(c: Candidate): Float = c.score + if (c.d == dir) 15f else 0f
    private fun tailScore(c: Candidate): Float = c.score + if (tailReachable(simulate(snake.first(), c.d).body)) 350f else -500f
    private fun hamScore(c: Candidate): Float {
        val idx = hamIndex(c.d)
        return c.score + if (idx >= 0) 140f * shortcutBonus else -80f
    }

    private fun beamBest(legal: List<Candidate>): Candidate {
        var best = legal.maxByOrNull { it.score } ?: legal.first()
        var bestScore = -1e30f
        beamNodes = 0

        data class Node(val body: ArrayDeque<P>, val first: P, val score: Float, val depth: Int)

        var layer = legal.map { Node(simulate(snake.first(), it.d).body, it.d, it.score, 1) }

        val beamDepth = if (snake.size >= safeFollowLength) 20 else 8
        val beamWidth = if (snake.size >= safeFollowLength) 40 else 16

        repeat(beamDepth) {
            if (!timeLeft()) return best

            val futures: List<Future<List<Node>>> = layer.map { nod ->
                aiPool.submit(Callable {
                    val children = ArrayList<Node>(4)
                    for (d in dirs) {
                        if (isReverse(d, directionOfFirst(nod.body))) continue
                        if (!canSim(nod.body, d)) continue
                        val sm = simulateOn(nod.body, d)
                        val r = freeRegion(sm.body)
                        val t = tailReachable(sm.body)
                        val ratio = r.toFloat() / max(1, sm.body.size)
                        if (!t && ratio < 1.15f) continue
                        val fd = distance(sm.body.first(), food, sm.body, true)
                        var sc = nod.score + r * (wRegion * 0.55f) +
                                if (t) wTailGood * 0.5f else wTailBad * 0.55f
                        if (fd >= 0) sc += wFoodNear * 0.33f / (fd + 1)
                        if (sm.ate) sc += wFoodAte * 0.6f
                        children.add(Node(sm.body, nod.first, sc, nod.depth + 1))
                    }
                    children
                })
            }

            val next = ArrayList<Node>()
            for (f in futures) {
                next.addAll(f.get())
                if (!timeLeft()) break
            }
            if (next.isEmpty()) return best

            for (n in next) {
                beamNodes++
                if (n.score > bestScore) {
                    bestScore = n.score
                    best = legal.firstOrNull { it.d == n.first } ?: best
                }
            }
            layer = next.sortedByDescending { it.score }.take(beamWidth)
        }
        return best
    }

    private fun learnState(len: Int, danger: Int): Int {
        val lenStage = when { len < 15 -> 0; len < 30 -> 1; len < 50 -> 2; len < 75 -> 3; else -> 4 }
        val dStage = (danger - 1).coerceIn(0, 4)
        val spaceStage = when { len < 20 -> 0; len < 40 -> 1; len < 60 -> 2; else -> 3 }
        return ((lenStage * 5 + dStage) * 4 + spaceStage).coerceIn(0, 99)
    }

    private fun clampW(v: Float, lo: Float, hi: Float): Float = v.coerceIn(lo, hi)

    private fun rewardEatStep() {
        wFoodAte = clampW(wFoodAte * 1.008f, 300f, 3000f)
        wTailGood = clampW(wTailGood * 1.004f, 60f, 1200f)
        wFoodNear = clampW(wFoodNear * 1.002f, 100f, 2500f)
    }

    private fun adjustWeights(cause: String) {
        val beforeEdge = wEdge
        val beforeTail = wTailGood
        val beforeSpace = wSpace
        val beforeFood = wFoodNear
        val beforeAgg = aggression
        val beforeSafety = safetyMargin

        when (cause) {
            "WALL" -> {
                wEdge = clampW(wEdge * 1.08f, wEdge0 * 0.6f, wEdge0 * 1.5f)
                aggression = clampW(aggression * 0.98f, 0.85f, 1.5f)
            }
            "SELF" -> {
                wTailGood = clampW(wTailGood * 1.08f, wTailGood0 * 0.6f, wTailGood0 * 1.5f)
                wTailBad = clampW(wTailBad * 1.05f, wTailBad0 * 1.5f, wTailBad0 * 0.6f)
                safetyMargin = clampW(safetyMargin * 1.02f, 1.0f, 1.25f)
            }
            "TRAP" -> {
                wSpace = clampW(wSpace * 1.10f, wSpace0 * 0.6f, wSpace0 * 1.5f)
                wRegion = clampW(wRegion * 1.05f, wRegion0 * 0.6f, wRegion0 * 1.5f)
                safetyMargin = clampW(safetyMargin * 1.03f, 1.0f, 1.25f)
                aggression = clampW(aggression * 0.97f, 0.85f, 1.5f)
            }
            "HUNGER" -> {
                wFoodNear = clampW(wFoodNear * 1.10f, wFoodNear0 * 0.6f, wFoodNear0 * 1.5f)
                wFoodAte = clampW(wFoodAte * 1.06f, wFoodAte0 * 0.6f, wFoodAte0 * 1.5f)
                aggression = clampW(aggression * 1.05f, 0.85f, 1.5f)
                wSpace = clampW(wSpace * 0.97f, wSpace0 * 0.6f, wSpace0 * 1.5f)
            }
        }

        // 缓慢拉回默认
        wRegion = wRegion * 0.995f + wRegion0 * 0.005f
        wMobility = wMobility * 0.995f + wMobility0 * 0.005f
        wEdge = wEdge * 0.997f + wEdge0 * 0.003f
        wSpace = wSpace * 0.997f + wSpace0 * 0.003f
        wFoodNear = wFoodNear * 0.997f + wFoodNear0 * 0.003f
        wTailGood = wTailGood * 0.997f + wTailGood0 * 0.003f

        lastLearnAction = when (cause) {
            "WALL" -> "边界${"%.0f→%.0f".format(beforeEdge, wEdge)} 攻${"%.2f→%.2f".format(beforeAgg, aggression)}"
            "SELF" -> "尾+${"%.0f→%.0f".format(beforeTail, wTailGood)} 安全${"%.2f→%.2f".format(beforeSafety, safetyMargin)}"
            "TRAP" -> "空间${"%.0f→%.0f".format(beforeSpace, wSpace)} 安全${"%.2f→%.2f".format(beforeSafety, safetyMargin)}"
            "HUNGER" -> "食近${"%.0f→%.0f".format(beforeFood, wFoodNear)} 攻${"%.2f→%.2f".format(beforeAgg, aggression)}"
            else -> "微调"
        }
    }

    private fun selectStrategy(state: Int, danger: Int): Int {
        if (forcedStrategy >= 0) return forcedStrategy.coerceIn(0, 4).let { if (it == 4) 3 else it }
        val hungerBias = if (hunger > 18) 1.5f else 0f
        val dangerBias = if (danger >= 4) 2.5f else 0f
        val prior = floatArrayOf(
            if (snake.size < 35) 1.2f + hungerBias else 0.5f,
            1f + dangerBias,
            if (snake.size >= 35) 1.8f else 0.4f,
            if (snake.size < 100) 1.3f else 0.7f,
            0f
        )
        var best = 0; var value = -1e9f
        for (a in 0..3) {
            val bonus = if (n[state][a] == 0) 0.8f else q[state][a]
            val ucb = bonus + prior[a]
            if (ucb > value) { value = ucb; best = a }
        }
        return best
    }

    private fun learn(reward: Float) {
        if (lastState < 0 || lastAction < 0) return
        val s = lastState; val a = lastAction
        val alpha = when {
            n[s][a] < 10 -> 0.20f
            n[s][a] < 50 -> 0.10f
            else -> 0.04f
        }
        q[s][a] += alpha * (reward - q[s][a])
        n[s][a]++
    }

    private fun saveLearning() {
        val e = prefs.edit()
            .putFloat("learn_aggression", aggression)
            .putFloat("learn_safety", safetyMargin)
            .putFloat("learn_shortcut", shortcutBonus)
            .putFloat("w_region", wRegion).putFloat("w_mobility", wMobility)
            .putFloat("w_tail_good", wTailGood).putFloat("w_tail_bad", wTailBad)
            .putFloat("w_food_near", wFoodNear).putFloat("w_food_ate", wFoodAte)
            .putFloat("w_edge", wEdge).putFloat("w_space", wSpace)
            .putString("last_learn_action", lastLearnAction)
            .putInt("stat_wall", deathWall).putInt("stat_self", deathSelf)
            .putInt("stat_trap", deathTrap).putInt("stat_total", totalGames)
            .putInt("money", money).putInt("high_score", highScore)
        for (s in 0 until 100) for (a in 0 until 4) {
            e.putFloat("q_${s}_$a", q[s][a]); e.putInt("n_${s}_$a", n[s][a])
        }
        e.apply()
    }

    private fun die(cause: String) {
        gameOver = true; deathCause = cause
        when (cause) {
            "WALL" -> { deathWall++; learn(-6f) }
            "SELF" -> { deathSelf++; learn(-7f) }
            "HUNGER" -> { deathTrap++; learn(-40f) }
            else -> { deathTrap++; learn(-12f) }
        }
        adjustWeights(cause)
        totalGames++
        recentScores.addLast(score)
        while (recentScores.size > 50) recentScores.removeFirst()
        if (score > bestRecentScore) bestRecentScore = score

        // ★ 死因自适应 + 每局向默认回归 3%，防止参数卡死
        aggression = when (cause) {
            "WALL" -> max(0.5f, aggression * 0.98f)
            "SELF" -> max(0.5f, aggression * 0.99f)
            "HUNGER" -> min(2f, aggression * 1.10f)
            else -> max(0.5f, aggression * 0.96f)
        }
        if (cause == "TRAP") safetyMargin = min(1.30f, safetyMargin * 1.03f)
        if (cause == "HUNGER") safetyMargin = max(1.0f, safetyMargin * 0.97f)
        if (cause == "WALL") safetyMargin = max(1.0f, safetyMargin * 0.99f)
        safetyMargin = safetyMargin * 0.97f + 1.08f * 0.03f
        aggression = aggression * 0.97f + 1.15f * 0.03f
        safetyMargin = safetyMargin.coerceIn(1.0f, 1.25f)
        aggression = aggression.coerceIn(0.85f, 1.50f)

        lastDeathInfo = "死因=$cause 长度=${snake.size} 分=$score " +
                "空间=${ai.region} 需求=${(snake.size * safetyMargin).toInt()}"

        val shouldSave = when {
            reinforceTraining -> totalGames % 300 == 0
            trainingMode -> totalGames % 50 == 0
            else -> true
        }
        if (shouldSave) saveLearning()

        if (trainingMode || reinforceTraining) {
            reset()
            return
        }

        flash = 1f
        vibrateDeath()
        restartCountdown = 0L
        invalidate()
    }

    private fun reasonFor(c: Candidate, strategy: Int, danger: Int): String = when {
        !c.legal -> "此方向不合法"
        c.d == dir && danger >= 4 -> "危险较高，保持可控路线"
        c.reason == "马上吃到食物" -> "食物可安全取得，收益高"
        c.reason == "吃完会困死，避开" -> "吃完会困死，避开该方向"
        c.reason == "保持尾巴可达" -> "优先保持尾巴出口，避免困死"
        else -> "综合空间、食物、尾巴与边界风险"
    }

    private fun strategyName(s: Int): String = when (s) {
        0 -> "BFS 食物"; 1 -> "TAIL 追尾"; 2 -> "HAM 路线"
        3 -> "BEAM 前瞻"; 4 -> "BEAM 前瞻"; else -> "AUTO"
    }

    private fun simulate(head: P, d: P): Sim = simulateOn(ArrayDeque(snake), d)

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

    private fun canSim(body: ArrayDeque<P>, d: P): Boolean {
        if (body.isEmpty()) return false
        val h = body.first()
        val nh = P(h.x + d.x, h.y + d.y)
        if (!inside(nh)) return false
        val ate = nh == food
        return !body.contains(nh) || (nh == body.last() && !ate)
    }

    private fun legalDirection(d: P): Boolean = d != P(0, 0) && !isReverse(d, dir) && canSim(snake, d)
    private fun isReverse(a: P, b: P): Boolean = a.x == -b.x && a.y == -b.y

    private fun directionOfFirst(body: ArrayDeque<P>): P {
        if (body.size < 2) return dir
        return P(body.elementAt(0).x - body.elementAt(1).x, body.elementAt(0).y - body.elementAt(1).y)
    }

    private fun inside(p: P): Boolean = p.x in 0 until cols && p.y in 0 until rows

    private fun freeRegion(body: ArrayDeque<P>): Int {
        if (body.isEmpty()) return 0
        val total = cols * rows
        val visited = tlVisited.get()
        val queue = tlQueue.get()
        java.util.Arrays.fill(visited, 0, total, false)
        for (p in body) {
            if (p.x !in 0 until cols || p.y !in 0 until rows) continue
            val index = p.y * cols + p.x
            if (index in 0 until total) visited[index] = true
        }
        val start = body.first()
        if (start.x !in 0 until cols || start.y !in 0 until rows) return 0
        val startIndex = start.y * cols + start.x
        if (startIndex !in 0 until total) return 0
        visited[startIndex] = true
        var head = 0; var tail = 0
        queue[tail++] = startIndex
        var count = 0
        while (head < tail) {
            val curr = queue[head++]
            if (curr !in 0 until total) continue
            val cx = curr % cols; val cy = curr / cols
            count++
            if (cx > 0) {
                val ni = curr - 1
                if (!visited[ni]) { visited[ni] = true; if (tail < total) queue[tail++] = ni }
            }
            if (cx < cols - 1) {
                val ni = curr + 1
                if (!visited[ni]) { visited[ni] = true; if (tail < total) queue[tail++] = ni }
            }
            if (cy > 0) {
                val ni = curr - cols
                if (!visited[ni]) { visited[ni] = true; if (tail < total) queue[tail++] = ni }
            }
            if (cy < rows - 1) {
                val ni = curr + cols
                if (!visited[ni]) { visited[ni] = true; if (tail < total) queue[tail++] = ni }
            }
        }
        return count
    }

    private fun distance(start: P, target: P, body: Collection<P>, allowTail: Boolean): Int {
        if (start.x !in 0 until cols || start.y !in 0 until rows ||
            target.x !in 0 until cols || target.y !in 0 until rows) return -1
        if (start == target) return 0
        val total = cols * rows
        val visited = tlVisited.get()
        val queue = tlQueue.get()
        java.util.Arrays.fill(visited, 0, total, false)
        for (p in body) {
            if (p.x !in 0 until cols || p.y !in 0 until rows) continue
            val index = p.y * cols + p.x
            if (index in 0 until total) visited[index] = true
        }
        if (allowTail && body.isNotEmpty()) {
            val last = body.last()
            if (last.x in 0 until cols && last.y in 0 until rows) {
                val lastIndex = last.y * cols + last.x
                if (lastIndex in 0 until total) visited[lastIndex] = false
            }
        }
        val startIndex = start.y * cols + start.x
        if (startIndex !in 0 until total) return -1
        visited[startIndex] = true
        var head = 0; var tail = 0
        queue[tail++] = startIndex
        var dist = 0
        while (head < tail) {
            val layerSize = tail - head
            var i = 0
            while (i < layerSize) {
                i++
                if (head >= tail) break
                val curr = queue[head++]
                if (curr !in 0 until total) continue
                val cx = curr % cols; val cy = curr / cols
                if (cx == target.x && cy == target.y) return dist
                if (cx > 0) {
                    val ni = curr - 1
                    if (!visited[ni]) { visited[ni] = true; if (tail < total) queue[tail++] = ni }
                }
                if (cx < cols - 1) {
                    val ni = curr + 1
                    if (!visited[ni]) { visited[ni] = true; if (tail < total) queue[tail++] = ni }
                }
                if (cy > 0) {
                    val ni = curr - cols
                    if (!visited[ni]) { visited[ni] = true; if (tail < total) queue[tail++] = ni }
                }
                if (cy < rows - 1) {
                    val ni = curr + cols
                    if (!visited[ni]) { visited[ni] = true; if (tail < total) queue[tail++] = ni }
                }
            }
            dist++
        }
        return -1
    }

    private fun countSafeMoves(body: ArrayDeque<P>): Int {
        if (body.isEmpty()) return 0
        val h = body.first()
        return dirs.count { d ->
            val nh = P(h.x + d.x, h.y + d.y)
            inside(nh) && (!body.contains(nh) || (nh == body.last() && nh != food)) &&
                !isReverse(d, directionOfFirst(body))
        }
    }

    private fun tailReachable(body: ArrayDeque<P>): Boolean =
        if (body.isEmpty()) false
        else distance(body.first(), body.last(), body, true) >= 0

    private fun calculateDanger(): Int {
        val region = freeRegion(snake)
        val ratio = region.toFloat() / max(1, snake.size)
        val mobility = countSafeMoves(snake)
        return when {
            mobility <= 0 -> 5
            ratio < 1.5f -> 5
            ratio < 2.2f -> 4
            ratio < 3.5f -> 3
            ratio < 5f -> 2
            else -> 1
        }
    }

    private fun hamIndex(d: P): Int {
        val h = snake.first()
        val next = P(h.x + d.x, h.y + d.y)
        if (!inside(next)) return -1
        return next.x * rows + next.y
    }

    private fun placeFood() {
        val free = ArrayList<P>()
        for (x in 0 until cols) for (y in 0 until rows) {
            val p = P(x, y)
            if (!snake.contains(p)) free.add(p)
        }
        if (free.isNotEmpty()) food = free[Random.nextInt(free.size)]
    }

    private fun spawnFoodEffect(p: P) {
        repeat(14) {
            particles.add(Particle(p.x.toFloat(), p.y.toFloat(), Random.nextFloat() - 0.5f, Random.nextFloat() - 0.5f, 1f, Color.YELLOW))
        }
        floats.add(FloatText(p.x.toFloat(), p.y.toFloat(), 1f, "+10"))
    }

    private fun updateEffects(dt: Float) {
        flash = max(0f, flash - dt * 0.035f)
        particles.forEach { it.x += it.vx * dt; it.y += it.vy * dt; it.life -= dt * 0.035f }
        particles.removeAll { it.life <= 0f }
        floats.forEach { it.y -= dt * 0.04f; it.life -= dt * 0.025f }
        floats.removeAll { it.life <= 0f }
    }

    override fun onSizeChanged(w: Int, h: Int, oldw: Int, oldh: Int) {
        val hudReserve = 760f + 24f
        val availTop = 12f
        val availBottom = (h - hudReserve)
            .coerceAtLeast(availTop + h * 0.30f)
        val availH = availBottom - availTop

        cell = min(w.toFloat() / cols, availH / rows)
        ox = (w - cols * cell) / 2f

        val baseOy = availTop + (availH - rows * cell) / 2f
        val moveDown = cell * 2.5f
        val maxOy = availBottom - rows * cell
        oy = (baseOy + moveDown).coerceAtMost(maxOy)
    }

    override fun onDraw(c: Canvas) {
        super.onDraw(c)
        c.drawColor(bgColor)

        if (reinforceTraining) {
            text.textAlign = Paint.Align.CENTER
            text.isFakeBoldText = true
            text.textSize = 36f
            text.color = Color.rgb(46, 204, 113)
            c.drawText("强化训练中", width / 2f, height * 0.28f, text)
            text.isFakeBoldText = false
            text.textSize = 18f
            text.color = Color.LTGRAY
            c.drawText("棋盘已隐藏 · 全速计算中", width / 2f, height * 0.28f + 40f, text)
            text.textSize = 16f
            text.color = Color.WHITE
            c.drawText(
                "局数 $totalGames  均分 ${
                    if (recentScores.isEmpty()) "—" else "%.0f".format(recentScores.average())
                }  最佳 $bestRecentScore",
                width / 2f, height * 0.28f + 72f, text
            )
            text.textAlign = Paint.Align.LEFT
            drawDebug(c)
            return
        }

        gridPaint.color = gridColor
        gridPaint.style = Paint.Style.STROKE
        gridPaint.strokeWidth = 1f
        for (i in 0..cols) c.drawLine(ox + i * cell, oy, ox + i * cell, oy + rows * cell, gridPaint)
        for (i in 0..rows) c.drawLine(ox, oy + i * cell, ox + cols * cell, oy + i * cell, gridPaint)
        drawFood(c); drawSnake(c); drawParticles(c); drawDebug(c)
        if (gameOver) drawGameOver(c)
    }

    private fun drawFood(c: Canvas) {
        val cx = ox + (food.x + 0.5f) * cell
        val cy = oy + (food.y + 0.5f) * cell
        foodPaint.color = Color.argb(90, 255, 80, 80)
        c.drawCircle(cx, cy, cell * 0.38f, foodPaint)
        foodPaint.color = Color.RED
        c.drawCircle(cx, cy, cell * 0.22f, foodPaint)
        foodPaint.color = Color.WHITE
        c.drawCircle(cx, cy, cell * 0.07f, foodPaint)
    }

    private fun drawSnake(c: Canvas) {
        if (snake.isEmpty()) return
        snakePaint.strokeWidth = max(8f, cell * 0.62f)
        val list = snake.toList()
        for (i in 0 until list.size - 1) {
            val a = list[i]; val b = list[i + 1]
            snakePaint.color = if (rainbowSkin) hsv[(i * 23 + score) % 360] else bodyColor
            c.drawLine(ox + (a.x + 0.5f) * cell, oy + (a.y + 0.5f) * cell,
                       ox + (b.x + 0.5f) * cell, oy + (b.y + 0.5f) * cell, snakePaint)
        }
        val h = snake.first()
        headPaint.color = headColor
        c.drawCircle(ox + (h.x + 0.5f) * cell, oy + (h.y + 0.5f) * cell, cell * 0.36f, headPaint)
        val ex = when { dir.x > 0 -> 0.12f; dir.x < 0 -> -0.12f; else -> 0f }
        val ey = when { dir.y > 0 -> 0.12f; dir.y < 0 -> -0.12f; else -> 0f }
        paint.color = Color.WHITE
        c.drawCircle(ox + (h.x + 0.5f) * cell + cell * (0.13f + ex),
                     oy + (h.y + 0.5f) * cell + cell * (0.13f + ey),
                     cell * 0.075f, paint)
        c.drawCircle(ox + (h.x + 0.5f) * cell - cell * (0.13f - ex),
                     oy + (h.y + 0.5f) * cell - cell * (0.13f - ey),
                     cell * 0.075f, paint)
    }

    private fun drawParticles(c: Canvas) {
        particles.forEach {
            paint.color = Color.argb((it.life * 255).toInt().coerceIn(0, 255),
                Color.red(it.color), Color.green(it.color), Color.blue(it.color))
            c.drawCircle(ox + (it.x + 0.5f) * cell, oy + (it.y + 0.5f) * cell,
                         max(2f, cell * 0.05f), paint)
        }
        text.textAlign = Paint.Align.CENTER
        text.textSize = cell * 0.3f
        floats.forEach {
            text.color = Color.argb((it.life * 255).toInt().coerceIn(0, 255), 255, 215, 0)
            c.drawText(it.text, ox + (it.x + 0.5f) * cell, oy + (it.y + 0.3f) * cell, text)
        }
    }

    private fun drawDangerGauge(c: Canvas, cx: Float, cy: Float, r: Float, danger: Int) {
        val arcPaint = Paint(Paint.ANTI_ALIAS_FLAG)
        arcPaint.style = Paint.Style.STROKE
        arcPaint.strokeWidth = 13f
        arcPaint.strokeCap = Paint.Cap.ROUND
        val oval = RectF(cx - r, cy - r, cx + r, cy + r)
        arcPaint.color = Color.rgb(50, 50, 50)
        c.drawArc(oval, -90f, 360f, false, arcPaint)
        arcPaint.color = when (danger) {
            1 -> Color.GREEN
            2 -> Color.rgb(150, 255, 80)
            3 -> Color.YELLOW
            4 -> Color.rgb(255, 150, 0)
            else -> Color.RED
        }
        val sweep = 360f * (danger.coerceIn(1, 5) / 5f)
        c.drawArc(oval, -90f, sweep, false, arcPaint)
    }

    private fun drawWeightBars(c: Canvas, left: Float, top: Float, w: Float, h: Float) {
        val names = listOf("区域", "机动", "尾+", "尾-", "食近", "食吃", "边界", "空间")
        val values = floatArrayOf(
            wRegion / wRegion0, wMobility / wMobility0,
            wTailGood / wTailGood0, wTailBad / wTailBad0,
            wFoodNear / wFoodNear0, wFoodAte / wFoodAte0,
            wEdge / wEdge0, wSpace / wSpace0
        )
        val barW = w / names.size
        val maxRatio = 2.0f
        names.forEachIndexed { i, name ->
            val x = left + i * barW
            val ratio = values[i].coerceIn(0f, maxRatio)
            val barH = h * (ratio / maxRatio)
            barPaint.style = Paint.Style.FILL
            barPaint.color = Color.rgb(40, 40, 40)
            c.drawRect(x + 3f, top, x + barW - 8f, top + h, barPaint)
            barPaint.color = Color.rgb(100, 100, 100)
            val baseY = top + h - h * (1f / maxRatio)
            c.drawLine(x + 3f, baseY, x + barW - 8f, baseY, barPaint)
            barPaint.color = when {
                ratio > 1.3f -> Color.rgb(231, 76, 60)
                ratio > 1.1f -> Color.rgb(241, 196, 15)
                ratio < 0.8f -> Color.rgb(52, 152, 219)
                else -> Color.rgb(46, 204, 113)
            }
            c.drawRect(x + 3f, top + h - barH, x + barW - 8f, top + h, barPaint)
            text.textAlign = Paint.Align.CENTER
            text.textSize = 12f
            text.color = Color.LTGRAY
            c.drawText(name, x + (barW - 5f) / 2f, top + h + 15f, text)
            text.textSize = 12f
            text.color = Color.WHITE
            val pct = (values[i] * 100f).toInt()
            c.drawText("$pct%", x + (barW - 5f) / 2f, top + h + 30f, text)
        }
        text.textAlign = Paint.Align.LEFT
    }

    private fun drawLearningCurve(c: Canvas, left: Float, top: Float, w: Float, h: Float) {
        barPaint.style = Paint.Style.FILL
        barPaint.color = Color.rgb(25, 25, 25)
        c.drawRect(left, top, left + w, top + h, barPaint)
        if (recentScores.size < 2) {
            text.textAlign = Paint.Align.CENTER
            text.textSize = 13f
            text.color = Color.GRAY
            c.drawText("数据不足", left + w / 2f, top + h / 2f, text)
            text.textAlign = Paint.Align.LEFT
            return
        }
        val scores = recentScores.toList()
        val maxScore = scores.max().coerceAtLeast(1)
        val stepX = w / (scores.size - 1).coerceAtLeast(1)
        val areaPath = Path()
        areaPath.moveTo(left, top + h)
        scores.forEachIndexed { i, s ->
            val x = left + i * stepX
            val y = top + h - h * (s.toFloat() / maxScore)
            areaPath.lineTo(x, y)
        }
        areaPath.lineTo(left + w, top + h)
        areaPath.close()
        barPaint.color = Color.argb(60, 120, 255, 180)
        c.drawPath(areaPath, barPaint)
        val linePath = Path()
        scores.forEachIndexed { i, s ->
            val x = left + i * stepX
            val y = top + h - h * (s.toFloat() / maxScore)
            if (i == 0) linePath.moveTo(x, y) else linePath.lineTo(x, y)
        }
        val curvePaint = Paint(Paint.ANTI_ALIAS_FLAG)
        curvePaint.style = Paint.Style.STROKE
        curvePaint.strokeWidth = 3f
        curvePaint.color = Color.rgb(120, 255, 180)
        c.drawPath(linePath, curvePaint)
        text.textSize = 12f
        text.color = Color.LTGRAY
        c.drawText("max $maxScore", left + 5f, top + 14f, text)
    }

    private fun drawDeathPie(c: Canvas, cx: Float, cy: Float, r: Float) {
        val total = deathWall + deathSelf + deathTrap
        barPaint.style = Paint.Style.FILL
        if (total == 0) {
            barPaint.color = Color.rgb(60, 60, 60)
            c.drawCircle(cx, cy, r, barPaint)
            return
        }
        val oval = RectF(cx - r, cy - r, cx + r, cy + r)
        var start = -90f
        val sweepW = 360f * deathWall / total
        if (sweepW > 0f) {
            barPaint.color = Color.rgb(255, 100, 100)
            c.drawArc(oval, start, sweepW, true, barPaint)
            start += sweepW
        }
        val sweepS = 360f * deathSelf / total
        if (sweepS > 0f) {
            barPaint.color = Color.rgb(100, 150, 255)
            c.drawArc(oval, start, sweepS, true, barPaint)
            start += sweepS
        }
        val sweepT = 360f * deathTrap / total
        if (sweepT > 0f) {
            barPaint.color = Color.rgb(255, 200, 100)
            c.drawArc(oval, start, sweepT, true, barPaint)
        }
    }

    private fun drawQHeatmap(c: Canvas, left: Float, top: Float, w: Float, h: Float) {
        val cellW = w / 10f
        val cellH = h / 10f
        var maxAbs = 0.001f
        for (s in 0 until 100) for (a in 0 until 4) {
            val abs = kotlin.math.abs(q[s][a])
            if (abs > maxAbs) maxAbs = abs
        }
        barPaint.style = Paint.Style.FILL
        for (i in 0 until 100) {
            val col = i % 10
            val row = i / 10
            val x = left + col * cellW
            val y = top + row * cellH
            var maxQ = -1e9f
            var visited = false
            for (a in 0 until 4) {
                if (n[i][a] > 0) {
                    visited = true
                    if (q[i][a] > maxQ) maxQ = q[i][a]
                }
            }
            val color = if (!visited) {
                Color.rgb(35, 35, 35)
            } else {
                val t = (maxQ / maxAbs).coerceIn(-1f, 1f)
                if (t >= 0) {
                    Color.rgb(
                        (60 * (1 - t)).toInt().coerceIn(0, 255),
                        (60 + 195 * t).toInt().coerceIn(0, 255),
                        (60 * (1 - t)).toInt().coerceIn(0, 255)
                    )
                } else {
                    val nt = -t
                    Color.rgb(
                        (60 + 195 * nt).toInt().coerceIn(0, 255),
                        (60 * (1 - nt)).toInt().coerceIn(0, 255),
                        (60 * (1 - nt)).toInt().coerceIn(0, 255)
                    )
                }
            }
            barPaint.color = color
            c.drawRect(x, y, x + cellW - 1f, y + cellH - 1f, barPaint)
        }
    }

    private fun drawDebug(c: Canvas) {
        if (aiMode == 0) return

        val w = min(width * 0.97f, 720f)
        val h = 760f
        val left = (width - w) / 2f
        val top = max(12f, height - h - 12f)

        panel.color = Color.argb(232, 0, 0, 0)
        c.drawRoundRect(left, top, left + w, top + h, 22f, 22f, panel)

        border.color = when (ai.danger) {
            1 -> Color.GREEN
            2 -> Color.rgb(150, 255, 80)
            3 -> Color.YELLOW
            4 -> Color.rgb(255, 150, 0)
            else -> Color.RED
        }
        border.style = Paint.Style.STROKE
        border.strokeWidth = 5f
        c.drawRoundRect(left, top, left + w, top + h, 22f, 22f, border)

        text.textAlign = Paint.Align.LEFT

        text.isFakeBoldText = true
        text.textSize = 26f
        text.color = Color.WHITE
        c.drawText("${ai.strategy}", left + 16f, top + 36f, text)

        text.isFakeBoldText = false
        text.textSize = 14f
        text.color = Color.YELLOW
        c.drawText(ai.reason, left + 16f, top + 58f, text)

        val gaugeCX = left + 58f
        val gaugeCY = top + 116f
        val gaugeR = 42f
        drawDangerGauge(c, gaugeCX, gaugeCY, gaugeR, ai.danger)

        text.textAlign = Paint.Align.CENTER
        text.isFakeBoldText = true
        text.textSize = 26f
        text.color = Color.WHITE
        c.drawText("${ai.danger}", gaugeCX, gaugeCY + 9f, text)
        text.isFakeBoldText = false
        text.textSize = 12f
        text.color = Color.LTGRAY
        c.drawText("危险", gaugeCX, gaugeCY + 28f, text)

        text.textAlign = Paint.Align.LEFT
        text.textSize = 16f
        text.color = Color.WHITE
        c.drawText(
            "空间 ${ai.region}   比例 ${"%.1f".format(ai.spaceRatio)}",
            left + 118f, top + 86f, text
        )
        c.drawText(
            "尾巴 ${if (ai.tailReachable) "Y" else "N"}   " +
                "食物 ${if (ai.foodReachable) "Y" else "N"}   " +
                "距离 ${if (ai.foodDistance < 0) "∞" else ai.foodDistance}",
            left + 118f, top + 110f, text
        )
        val modeTag = when {
            reinforceTraining -> "   [强化训练]"
            trainingMode -> "   [训练中]"
            else -> ""
        }
        val speedText = "速度 ${(1000f / max(1L, gameSpeed)).toInt()}步/秒   深度 ${ai.depth}$modeTag"
        c.drawText(speedText, left + 118f, top + 134f, text)

        val wbY = top + 175f
        text.textAlign = Paint.Align.LEFT
        text.isFakeBoldText = true
        text.textSize = 14f
        text.color = Color.rgb(255, 200, 100)
        c.drawText("【权重柱状图】", left + 16f, wbY, text)
        text.isFakeBoldText = false
        drawWeightBars(c, left + 16f, wbY + 8f, w - 32f, 66f)

        val learnY = top + 290f
        text.textSize = 14f
        text.isFakeBoldText = true
        text.color = Color.rgb(255, 150, 255)
        c.drawText("【上次学习】", left + 16f, learnY, text)
        text.isFakeBoldText = false
        text.color = Color.WHITE
        c.drawText("$deathCause -> $lastLearnAction", left + 118f, learnY, text)

        val barStartX = left + 118f
        val barEndX = left + w - 16f
        val barW = barEndX - barStartX
        var barY = top + 318f

        text.isFakeBoldText = true
        text.textSize = 14f
        text.color = Color.rgb(255, 200, 100)
        c.drawText("【四方向安全】", left + 16f, barY, text)
        text.isFakeBoldText = false
        barY += 10f

        val dirNames = listOf("UP", "DN", "LF", "RT")
        ai.candidates.forEachIndexed { idx, cand ->
            text.textSize = 18f
            text.color = if (!cand.legal) Color.GRAY
                        else if (cand.d == ai.chosen) Color.CYAN
                        else Color.WHITE
            c.drawText(dirNames[idx], left + 16f, barY + 19f, text)

            if (!cand.legal) {
                text.textSize = 14f
                text.color = Color.GRAY
                c.drawText("非法（撞墙/身体）", barStartX, barY + 19f, text)
            } else {
                val regionRatio = if (snake.size > 0) cand.region.toFloat() / snake.size else 0f
                val safeScore = when {
                    cand.tailOk && regionRatio >= 1.5f -> 1.0f
                    cand.tailOk && regionRatio >= 1.0f -> 0.75f
                    regionRatio >= 1.0f -> 0.5f
                    regionRatio >= 0.6f -> 0.3f
                    else -> 0.15f
                }
                barPaint.color = Color.rgb(40, 40, 40)
                barPaint.style = Paint.Style.FILL
                c.drawRoundRect(barStartX, barY, barEndX, barY + 24f, 4f, 4f, barPaint)

                val barColor = when {
                    safeScore >= 0.9f -> Color.rgb(46, 204, 113)
                    safeScore >= 0.7f -> Color.rgb(241, 196, 15)
                    safeScore >= 0.5f -> Color.rgb(230, 126, 34)
                    else -> Color.rgb(231, 76, 60)
                }
                barPaint.color = barColor
                c.drawRoundRect(barStartX, barY, barStartX + barW * safeScore, barY + 24f, 4f, 4f, barPaint)

                text.textSize = 13f
                text.color = Color.WHITE
                c.drawText(
                    "空间${cand.region} 尾${if (cand.tailOk) "Y" else "N"} " +
                        "食${if (cand.foodDist < 0) "∞" else cand.foodDist} " +
                        "分${"%.0f".format(cand.score)}",
                    barStartX + 8f, barY + 18f, text
                )
            }
            barY += 28f
        }

        val hungerY = barY + 8f
        text.isFakeBoldText = true
        text.textSize = 14f
        text.color = Color.rgb(255, 200, 100)
        c.drawText("【饥饿】", left + 16f, hungerY + 17f, text)
        text.isFakeBoldText = false

        val hForce = hungerForceEat()
        val hRatio = (hunger.toFloat() / hungerKillLimit).coerceIn(0f, 1f)

        barPaint.color = Color.rgb(40, 40, 40)
        c.drawRoundRect(barStartX, hungerY, barEndX, hungerY + 24f, 4f, 4f, barPaint)
        val hColor = when {
            hunger >= hungerKillLimit -> Color.RED
            hunger >= autoBeamHunger -> Color.rgb(255, 100, 50)
            hunger >= hForce -> Color.rgb(241, 196, 15)
            hunger >= 30 -> Color.rgb(230, 200, 100)
            else -> Color.rgb(100, 200, 100)
        }
        barPaint.color = hColor
        c.drawRoundRect(barStartX, hungerY, barStartX + barW * hRatio, hungerY + 24f, 4f, 4f, barPaint)

        val forcePos = barStartX + barW * (hForce.toFloat() / hungerKillLimit)
        val beamPos = barStartX + barW * (autoBeamHunger.toFloat() / hungerKillLimit)
        barPaint.color = Color.WHITE
        c.drawLine(forcePos, hungerY, forcePos, hungerY + 24f, barPaint)
        c.drawLine(beamPos, hungerY, beamPos, hungerY + 24f, barPaint)

        text.textSize = 13f
        text.color = Color.WHITE
        c.drawText(
            "$hunger/$hungerKillLimit  强制${hForce}  BEAM${autoBeamHunger}",
            barStartX + 8f, hungerY + 18f, text
        )

        val chartY = hungerY + 40f
        val chartH = 72f

        val curveX = left + 16f
        val curveW = (w - 32f) * 0.55f

        text.isFakeBoldText = true
        text.textSize = 14f
        text.color = Color.rgb(120, 255, 180)
        c.drawText("【历史分数】", curveX, chartY, text)
        text.isFakeBoldText = false
        drawLearningCurve(c, curveX, chartY + 8f, curveW, chartH)

        val pieCX = left + w - 130f
        val pieCY = chartY + chartH / 2f + 14f
        val pieR = 34f

        text.isFakeBoldText = true
        text.textSize = 14f
        text.color = Color.rgb(255, 150, 150)
        c.drawText("【死亡统计】", pieCX - 52f, chartY, text)
        text.isFakeBoldText = false
        drawDeathPie(c, pieCX, pieCY, pieR)

        text.textAlign = Paint.Align.LEFT
        text.textSize = 13f
        text.color = Color.rgb(255, 100, 100)
        c.drawText("W $deathWall", pieCX + 42f, pieCY - 16f, text)
        text.color = Color.rgb(100, 150, 255)
        c.drawText("S $deathSelf", pieCX + 42f, pieCY + 4f, text)
        text.color = Color.rgb(255, 200, 100)
        c.drawText("T $deathTrap", pieCX + 42f, pieCY + 24f, text)

        val heatY = chartY + chartH + 30f
        text.textAlign = Paint.Align.LEFT
        text.isFakeBoldText = true
        text.textSize = 14f
        text.color = Color.rgb(200, 180, 255)
        c.drawText("【Q表热度 10x10=100状态】", left + 16f, heatY, text)
        text.isFakeBoldText = false
        drawQHeatmap(c, left + 16f, heatY + 8f, w - 32f, 66f)

        val infoY = heatY + 8f + 66f + 22f
        val avg = if (recentScores.isEmpty()) 0f else recentScores.average().toFloat()

        var nonZero = 0; var sumQ = 0f; var cntQ = 0
        for (s in 0 until 100) for (a in 0 until 4) {
            if (n[s][a] > 0) { nonZero++; sumQ += q[s][a]; cntQ++ }
        }
        val avgQ = if (cntQ > 0) sumQ / cntQ else 0f

        text.textSize = 14f
        text.color = Color.WHITE
        text.textAlign = Paint.Align.LEFT
        c.drawText(
            "局数 $totalGames   近50均分 ${"%.1f".format(avg)}   最佳 $bestRecentScore   " +
                "Q非零 $nonZero/400   平均Q ${"%+.3f".format(avgQ)}",
            left + 16f, infoY, text
        )
        c.drawText(
            "蛇长 ${snake.size}  分数 $score  饥饿 $hunger  最高 $highScore  金币 $money  " +
                "攻击x${"%.2f".format(aggression)}  安全x${"%.2f".format(safetyMargin)}",
            left + 16f, infoY + 20f, text
        )

        if (gameOver) {
            text.color = Color.RED
            text.isFakeBoldText = true
            text.textSize = 16f
            c.drawText("死亡原因：$deathCause", left + 16f, infoY + 42f, text)
            text.isFakeBoldText = false
        }

        val btnW = 160f
        val btnH = 42f
        val btnLeft = left + w - btnW - 16f
        val btnTop = infoY + 48f
        reinforceButtonRect.set(btnLeft, btnTop, btnLeft + btnW, btnTop + btnH)

        val btnColor = if (reinforceTraining) Color.rgb(231, 76, 60) else Color.rgb(46, 204, 113)
        panel.color = btnColor
        c.drawRoundRect(reinforceButtonRect, 12f, 12f, panel)

        text.textAlign = Paint.Align.CENTER
        text.isFakeBoldText = true
        text.textSize = 18f
        text.color = Color.WHITE
        c.drawText(
            if (reinforceTraining) "停止强化" else "强化训练",
            reinforceButtonRect.centerX(),
            reinforceButtonRect.centerY() + 7f,
            text
        )
        text.isFakeBoldText = false
        text.textAlign = Paint.Align.LEFT
    }

    private fun drawGameOver(c: Canvas) {
        paint.color = Color.argb(150, 0, 0, 0)
        c.drawRect(0f, 0f, width.toFloat(), height.toFloat(), paint)

        text.textAlign = Paint.Align.CENTER
        text.isFakeBoldText = true
        text.textSize = 30f
        text.color = Color.WHITE
        c.drawText("GAME OVER", width / 2f, height / 2f - 45, text)

        text.textSize = 15f
        text.isFakeBoldText = false
        c.drawText("分数 $score   最高 $highScore   长度 ${snake.size}",
                   width / 2f, height / 2f - 15, text)

        text.color = Color.YELLOW
        c.drawText("点击屏幕重新开始", width / 2f, height / 2f + 20, text)

        text.color = Color.LTGRAY
        text.textSize = 11f
        c.drawText(lastDeathInfo, width / 2f, height / 2f + 48, text)
    }

    private var touchStartX = 0f
    private var touchStartY = 0f

    override fun onTouchEvent(e: MotionEvent): Boolean {
        when (e.action) {
            MotionEvent.ACTION_DOWN -> {
                touchStartX = e.x
                touchStartY = e.y
                return true
            }
            MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> {
                if (aiMode != 0 && reinforceButtonRect.contains(e.x, e.y)) {
                    val now = System.currentTimeMillis()
                    if (now - lastReinforceTap > 400L) {
                        lastReinforceTap = now
                        setReinforceTraining(!reinforceTraining)
                    }
                    return true
                }

                if (gameOver) {
                    reset()
                    return true
                }

                if (aiMode != 0) return true
                if (snake.isEmpty()) return true

                val dx = e.x - touchStartX
                val dy = e.y - touchStartY
                val useSwipe = abs(dx) > 24f || abs(dy) > 24f
                val d = if (useSwipe) {
                    if (abs(dx) > abs(dy)) P(if (dx > 0) 1 else -1, 0)
                    else P(0, if (dy > 0) 1 else -1)
                } else {
                    val hx = ox + (snake.first().x + 0.5f) * cell
                    val hy = oy + (snake.first().y + 0.5f) * cell
                    val rdx = e.x - hx
                    val rdy = e.y - hy
                    if (abs(rdx) > abs(rdy)) P(if (rdx > 0) 1 else -1, 0)
                    else P(0, if (rdy > 0) 1 else -1)
                }

                if (!isReverse(d, dir)) {
                    queue.clear()
                    queue.add(d)
                }
                return true
            }
            else -> return true
        }
    }

    override fun onDetachedFromWindow() {
        super.onDetachedFromWindow()
        bgm?.stop()
        try { toneGen?.release() } catch (_: Throwable) {}
        try { aiPool.shutdownNow() } catch (_: Throwable) {}
    }

    private class BgmPlayer {
        private var audioTrack: AudioTrack? = null
        @Volatile private var playing = false
        private var thread: Thread? = null

        fun start() {
            if (playing) return
            playing = true
            thread = Thread {
                try {
                    val sampleRate = 22050
                    val pcm = generateMelody(sampleRate)
                    val track = AudioTrack.Builder()
                        .setAudioAttributes(
                            AudioAttributes.Builder()
                                .setUsage(AudioAttributes.USAGE_GAME)
                                .setContentType(AudioAttributes.CONTENT_TYPE_MUSIC)
                                .build()
                        )
                        .setAudioFormat(
                            AudioFormat.Builder()
                                .setEncoding(AudioFormat.ENCODING_PCM_16BIT)
                                .setSampleRate(sampleRate)
                                .setChannelMask(AudioFormat.CHANNEL_OUT_MONO)
                                .build()
                        )
                        .setBufferSizeInBytes(pcm.size * 2)
                        .setTransferMode(AudioTrack.MODE_STATIC)
                        .build()

                    track.write(pcm, 0, pcm.size)
                    if (Build.VERSION.SDK_INT >= 23) {
                        track.setLoopPoints(0, pcm.size, -1)
                    }
                    audioTrack = track
                    if (playing) track.play()
                } catch (_: Throwable) {}
            }.also { it.start() }
        }

        fun stop() {
            playing = false
            try { audioTrack?.pause() } catch (_: Throwable) {}
            try { audioTrack?.flush() } catch (_: Throwable) {}
            try { audioTrack?.release() } catch (_: Throwable) {}
            audioTrack = null
            thread = null
        }

        private fun generateMelody(sampleRate: Int): ShortArray {
            val N = 0f
            val E5 = 659.25f; val G5 = 783.99f; val C6 = 1046.50f
            val D5 = 587.33f; val F5 = 698.46f; val A5 = 880.00f
            val C5 = 523.25f; val E4 = 329.63f; val G4 = 392.00f
            val B4 = 493.88f; val A4 = 440.00f

            val notes = listOf(
                E5 to 180, G5 to 180, C6 to 180, G5 to 180,
                E5 to 180, G5 to 180, C6 to 260, N to 100,
                D5 to 180, F5 to 180, A5 to 180, F5 to 180,
                D5 to 180, F5 to 180, A5 to 260, N to 100,
                E5 to 180, G5 to 180, C6 to 180, G5 to 180,
                E5 to 180, G5 to 180, C6 to 180, E4 to 180,
                F5 to 180, A5 to 180, C6 to 180, A5 to 180,
                G5 to 260, D5 to 260, C5 to 420, N to 260,
                C5 to 180, E5 to 180, G5 to 180, E5 to 180,
                A4 to 180, C5 to 180, E5 to 180, C5 to 180,
                G4 to 180, B4 to 180, D5 to 180, G5 to 180,
                E5 to 220, D5 to 220, C5 to 420, N to 260,
                E5 to 180, D5 to 180, C5 to 180, D5 to 180,
                E5 to 260, G5 to 260,
                C6 to 400, N to 200
            )

            val out = ArrayList<Short>()
            for ((freq, durMs) in notes) {
                val n = durMs * sampleRate / 1000
                if (freq == N || freq <= 0f) {
                    for (i in 0 until n) out.add(0)
                } else {
                    val period = (sampleRate / freq).toInt().coerceAtLeast(1)
                    for (i in 0 until n) {
                        val phase = (i % period) / period.toFloat()
                        val t = i.toFloat() / n
                        val env = when {
                            t < 0.05f -> t / 0.05f
                            t > 0.70f -> (1f - t) / 0.30f
                            else -> 1f
                        }.coerceIn(0f, 1f)
                        val v = (if (phase < 0.5f) 1f else -1f) * env * 0.06f
                        out.add((v * Short.MAX_VALUE).toInt().coerceIn(
                            Short.MIN_VALUE.toInt(), Short.MAX_VALUE.toInt()
                        ).toShort())
                    }
                }
            }
            return out.toShortArray()
        }
    }
}
