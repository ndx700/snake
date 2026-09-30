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
    private var safetyMargin = 1.10f
    private var shortcutBonus = 0.90f

    private var deathWall = 0
    private var deathSelf = 0
    private var deathTrap = 0
    private var totalGames = 0

    private var lastLearnAction = "初始化（暂无死亡）"

    private val safeFollowLength = 40

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

    // ============================================================
    // 训练模式
    // ============================================================
    private var trainingMode = false
    private var renderSkipCounter = 0

    // ============================================================
    // AI 并行线程池（骁龙 8 Gen 2）
    // ============================================================
    private val aiPool: ExecutorService = Executors.newFixedThreadPool(4) { r ->
        Thread(r, "snake-ai").apply { isDaemon = true }
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
            } else {
                accumulator += dt
                var stepCount = 0
                val maxSteps = if (trainingMode) 10 else Int.MAX_VALUE
                while (accumulator >= gameSpeed && stepCount < maxSteps) {
                    updateGame()
                    if (gameOver && !trainingMode) break
                    accumulator -= gameSpeed
                    stepCount++
                }
                if (stepCount >= maxSteps) accumulator = 0L
            }

            updateEffects(dt / 16f)

            if (!trainingMode || (++renderSkipCounter % 5 == 0)) {
                invalidate()
            }
            Choreographer.getInstance().postFrameCallback(this)
        }
    }

    init {
        highScore = prefs.getInt("high_score", 0)
        money = prefs.getInt("money", 0)
        trainingMode = prefs.getBoolean("training_mode", false)
        aggression = prefs.getFloat("learn_aggression", 1.15f)
        safetyMargin = prefs.getFloat("learn_safety", 1.10f)
        shortcutBonus = prefs.getFloat("learn_shortcut", 0.90f)
        wRegion = prefs.getFloat("w_region", wRegion0)
        wMobility = prefs.getFloat("w_mobility", wMobility0)
        wTailGood = prefs.getFloat("w_tail_good", wTailGood0)
        wTailBad = prefs.getFloat("w_tail_bad", wTailBad0)
        wFoodNear = prefs.getFloat("w_food_near", wFoodNear0)
        wFoodAte = prefs.getFloat("w_food_ate", wFoodAte0)
        wEdge = prefs.getFloat("w_edge", wEdge0)
        wSpace = prefs.getFloat("w_space", wSpace0)
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
            reset()
        } else {
            if (running) bgm?.start()
            reset()
        }
        invalidate()
    }

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

        if (trainingMode) gameSpeed = 2L

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
            onScoreChanged?.invoke(score)
            onMoneyChanged?.invoke(money)

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
            rewardEatStep()
        } else {
            snake.removeLast(); hunger++; combo = max(0, combo - 1)
            learn(0.025f)
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
        var s = 0f
        if (!tailOk) s -= 5000f else s += 800f
        s += region * 15f
        s += when {
            ratio >= 2.0f -> 1000f
            ratio >= 1.5f -> 700f
            ratio >= 1.2f -> 400f
            ratio >= 1.0f -> 100f
            ratio >= 0.8f -> -300f
            else -> -1500f
        }
        val mobility = countSafeMoves(body)
        s += mobility * 200f
        val edge = min(min(body.first().x, cols - 1 - body.first().x), min(body.first().y, rows - 1 - body.first().y))
        s -= max(0, 2 - edge) * 300f
        val foodDist = distance(body.first(), food, body, true)
        if (foodDist >= 0 && ratio >= 1.3f && foodDist < snake.size / 2) s += 250f / (foodDist + 1)
        if (sim.ate) s += 500f
        return s
    }

    private fun chooseMove(): P {
        aiStepStartNs = System.nanoTime()
        aiStepBudgetNs = if (trainingMode) 3_000_000L else budgetFor(gameSpeed)

        val futures: List<Future<Candidate>> = dirs.map { d ->
            aiPool.submit(Callable { evaluate(d) })
        }
        val candidates = futures.map { it.get() }
        val legal = candidates.filter { it.legal }

        if (legal.isEmpty()) {
            ai = Snapshot(strategy = "NO MOVE", reason = "四个方向都无法安全前进", danger = 5, chosen = dir, candidates = candidates)
            return dir
        }
        val danger = calculateDanger()
        val state = learnState(snake.size, danger)
        val strategy = selectStrategy(state, danger)
        val hungerFactor = when {
            hunger >= 60 -> 4f
            hunger >= 30 -> 2.5f
            hunger >= 15 -> 1.6f
            else -> 1f
        }
        val forceEatThreshold = hungerForceEat()
        val forceEat = hunger >= forceEatThreshold

        if (forceEat) {
            var bestSafe: Candidate? = null; var bestSafeDist = Int.MAX_VALUE
            var bestAny: Candidate? = null; var bestAnyDist = Int.MAX_VALUE
            for (cand in legal) {
                val sim = simulate(snake.first(), cand.d)
                val fd = distance(sim.body.first(), food, sim.body, true)
                if (fd in 0 until bestAnyDist) { bestAnyDist = fd; bestAny = cand }
                val tailOk = tailReachable(sim.body)
                val region = freeRegion(sim.body)
                val need = (snake.size * 0.8f).toInt()
                if (tailOk && region >= need && fd in 0 until bestSafeDist) { bestSafeDist = fd; bestSafe = cand }
            }
            val chosenForce = bestSafe ?: bestAny
            if (chosenForce != null) {
                lastState = state
                lastAction = dirs.indexOfFirst { it == chosenForce.d }.coerceAtLeast(0)
                val usingSafe = bestSafe != null
                ai = Snapshot(
                    strategy = if (usingSafe) "饥饿强制(安全)" else "饥饿强制(兜底)",
                    reason = if (usingSafe) "饥饿 $hunger ≥ $forceEatThreshold，安全方向内追食物"
                             else "饥饿 $hunger ≥ $forceEatThreshold，无安全方向，冲最近的食物",
                    danger = if (usingSafe) 2 else 4,
                    region = freeRegion(snake),
                    tailReachable = tailReachable(snake),
                    foodReachable = (if (usingSafe) bestSafeDist else bestAnyDist) != Int.MAX_VALUE,
                    foodDistance = if (usingSafe) bestSafeDist else bestAnyDist,
                    hunger = hunger, chosen = chosenForce.d, candidates = candidates,
                    depth = 1, nodes = legal.size,
                    hungerFactor = hungerFactor, regionWeight = wRegion,
                    strategyId = state, qValue = q[state][lastAction], nVisits = n[state][lastAction],
                    forceEatActive = true, forceEatSafe = usingSafe, safeFollowMode = false
                )
                return chosenForce.d
            }
        }

        val safeFollowMode = snake.size >= safeFollowLength
        if (safeFollowMode) {
            val scoreFutures: List<Future<Pair<Candidate, Float>>> = legal.map { cand ->
                aiPool.submit(Callable { cand to safeFollowScore(cand) })
            }
            var bestC: Candidate? = null
            var bestS = -1e30f
            for (f in scoreFutures) {
                val (cand, sc) = f.get()
                if (sc > bestS) { bestS = sc; bestC = cand }
            }
            if (bestC != null) {
                lastState = state
                lastAction = dirs.indexOfFirst { it == bestC.d }.coerceAtLeast(0)
                val reg = freeRegion(snake)
                ai = Snapshot(
                    strategy = "SAFE_FOLLOW 长蛇模式",
                    reason = "蛇长 ${snake.size} ≥ $safeFollowLength，优先保命",
                    danger = danger, region = reg,
                    spaceRatio = reg.toFloat() / max(1, snake.size),
                    tailReachable = tailReachable(snake), foodReachable = true, foodDistance = -1,
                    hunger = hunger, chosen = bestC.d, candidates = candidates,
                    depth = 1, nodes = legal.size,
                    hungerFactor = hungerFactor, regionWeight = wRegion * 3f,
                    strategyId = state, qValue = q[state][lastAction], nVisits = n[state][lastAction],
                    forceEatActive = false, forceEatSafe = false, safeFollowMode = true
                )
                return bestC.d
            }
        }

        val autoBeam = hunger >= autoBeamHunger
        val scored = when (strategy) {
            0 -> legal.maxByOrNull { bfsScore(it) }
            1 -> legal.maxByOrNull { tailScore(it) }
            2 -> legal.maxByOrNull { hamScore(it) }
            else -> beamBest(legal)
        } ?: legal.first()
        val final = if (autoBeam) beamBest(legal)
        else if (forcedStrategy >= 0) {
            val fs = forcedStrategy.coerceIn(0, 4)
            when (fs) {
                0 -> legal.maxByOrNull { bfsScore(it) }
                1 -> legal.maxByOrNull { tailScore(it) }
                2 -> legal.maxByOrNull { hamScore(it) }
                4 -> beamBest(legal)
                else -> legal.first()
            } ?: scored
        } else scored
        val action = dirs.indexOfFirst { it == final.d }.coerceAtLeast(0)
        lastState = state; lastAction = action
        val region = freeRegion(snake)
        val foodDistance = distance(snake.first(), food, snake, true)
        val stratId = if (forcedStrategy >= 0) forcedStrategy else strategy
        ai = Snapshot(
            strategy = if (autoBeam) "BEAM 饥饿自动" else strategyName(stratId),
            reason = if (autoBeam) "饥饿 $hunger 步未进食，切 BEAM 追食物" else reasonFor(final, strategy, danger),
            danger = danger, region = region,
            spaceRatio = region.toFloat() / max(1, snake.size),
            tailReachable = tailReachable(snake),
            foodReachable = foodDistance >= 0, foodDistance = foodDistance,
            hunger = hunger, chosen = final.d, candidates = candidates,
            depth = if (strategy == 3 || autoBeam) 4 else 2,
            nodes = if (strategy == 3 || autoBeam) beamNodes else candidates.size,
            hungerFactor = hungerFactor, regionWeight = wRegion,
            strategyId = stratId, qValue = q[state][action], nVisits = n[state][action],
            forceEatActive = false, forceEatSafe = false, safeFollowMode = false
        )
        return final.d
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
            val tailOkAfter = tail
            val spaceOkAfter = region >= needSpace
            if (!tailOkAfter || !spaceOkAfter) {
                eatPenalty = -2000f - snake.size * 30f
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

        val beamDepth = if (snake.size >= safeFollowLength) 16 else 8
        val beamWidth = if (snake.size >= safeFollowLength) 32 else 16

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
        wFoodAte = clampW(wFoodAte * 1.01f, 300f, 3000f)
        wTailGood = clampW(wTailGood * 1.005f, 60f, 800f)
    }

    private fun adjustWeights(cause: String) {
        val beforeEdge = wEdge; val beforeTail = wTailGood
        val beforeSpace = wSpace; val beforeFood = wFoodNear
        when (cause) {
            "WALL" -> wEdge = clampW(wEdge * 1.15f, 20f, 400f)
            "SELF" -> {
                wTailGood = clampW(wTailGood * 1.15f, 60f, 800f)
                wTailBad = clampW(wTailBad * 1.10f, -1500f, -80f)
            }
            "TRAP" -> wSpace = clampW(wSpace * 1.20f, 8f, 300f)
            "HUNGER" -> {
                wFoodNear = clampW(wFoodNear * 1.25f, 100f, 2500f)
                wFoodAte = clampW(wFoodAte * 1.15f, 300f, 3000f)
            }
        }
        lastLearnAction = when (cause) {
            "WALL" -> "边界 ${"%.0f→%.0f".format(beforeEdge, wEdge)}"
            "SELF" -> "尾巴+ ${"%.0f→%.0f".format(beforeTail, wTailGood)}"
            "TRAP" -> "空间 ${"%.0f→%.0f".format(beforeSpace, wSpace)}"
            "HUNGER" -> "食物近 ${"%.0f→%.0f".format(beforeFood, wFoodNear)}"
            else -> "无变化"
        }
        wRegion = wRegion * 0.999f + wRegion0 * 0.001f
        wMobility = wMobility * 0.999f + wMobility0 * 0.001f
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
            "HUNGER" -> { deathTrap++; learn(-30f) }
            else -> { deathTrap++; learn(-8f) }
        }
        adjustWeights(cause)
        totalGames++
        recentScores.addLast(score)
        while (recentScores.size > 50) recentScores.removeFirst()
        if (score > bestRecentScore) bestRecentScore = score

        aggression = when (cause) {
            "WALL" -> max(0.5f, aggression * 0.97f)
            "SELF" -> max(0.5f, aggression * 0.99f)
            "HUNGER" -> min(3f, aggression * 1.15f)
            else -> max(0.5f, aggression * 0.94f)
        }
        if (cause == "TRAP") safetyMargin = min(3f, safetyMargin * 1.04f)

        lastDeathInfo = "死因=$cause 长度=${snake.size} 分=$score " +
                "空间=${ai.region} 需求=${(snake.size * safetyMargin).toInt()}"

        if (!trainingMode || totalGames % 50 == 0) {
            saveLearning()
        }

        if (trainingMode) {
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
        visited[startIndex] = false
        var head = 0; var tail = 0
        queue[tail++] = startIndex
        var count = 0
        while (head < tail) {
            val curr = queue[head++]
            if (curr !in 0 until total) continue
            val cx = curr % cols; val cy = curr / cols
            count++
            if (cx > 0) { val ni = curr - 1; if (!visited[ni]) { visited[ni] = true; queue[tail++] = ni } }
            if (cx < cols - 1) { val ni = curr + 1; if (!visited[ni]) { visited[ni] = true; queue[tail++] = ni } }
            if (cy > 0) { val ni = curr - cols; if (!visited[ni]) { visited[ni] = true; queue[tail++] = ni } }
            if (cy < rows - 1) { val ni = curr + cols; if (!visited[ni]) { visited[ni] = true; queue[tail++] = ni } }
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
        visited[startIndex] = false
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
                if (cx > 0) { val ni = curr - 1; if (!visited[ni]) { visited[ni] = true; queue[tail++] = ni } }
                if (cx < cols - 1) { val ni = curr + 1; if (!visited[ni]) { visited[ni] = true; queue[tail++] = ni } }
                if (cy > 0) { val ni = curr - cols; if (!visited[ni]) { visited[ni] = true; queue[tail++] = ni } }
                if (cy < rows - 1) { val ni = curr + cols; if (!visited[ni]) { visited[ni] = true; queue[tail++] = ni } }
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
        val speedText = "速度 ${(1000f / gameSpeed).toInt()}步/秒   深度 ${ai.depth}" +
                if (trainingMode) "   [训练中]" else ""
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

    override fun onTouchEvent(e: MotionEvent): Boolean {
        if (e.action != MotionEvent.ACTION_UP) return true
        if (gameOver) { reset(); return true }
        if (aiMode != 0) return true
        if (snake.isEmpty()) return true

        val dx = e.x - (ox + (snake.first().x + 0.5f) * cell)
        val dy = e.y - (oy + (snake.first().y + 0.5f) * cell)

        val d = if (abs(dx) > abs(dy)) P(if (dx > 0) 1 else -1, 0)
                else P(0, if (dy > 0) 1 else -1)

        if (!isReverse(d, dir)) queue.add(d)
        return true
    }

    override fun onDetachedFromWindow() {
        super.onDetachedFromWindow()
        bgm?.stop()
        try { toneGen?.release() } catch (_: Throwable) {}
        try { aiPool.shutdownNow() } catch (_: Throwable) {}
    }

    // ============================================================
    // BGM 播放器
    // ============================================================
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
