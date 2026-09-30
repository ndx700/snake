package com.example.snake

import android.content.Context
import android.graphics.*
import android.os.Build
import android.os.VibrationEffect
import android.os.Vibrator
import android.os.VibratorManager
import android.util.AttributeSet
import android.view.Choreographer
import android.view.MotionEvent
import android.view.View
import java.util.ArrayDeque
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

    private var gameSpeed = 16L
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

    private val safeFollowLength = 60

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

    private val bfsVisited = BooleanArray(cols * rows)
    private val bfsQueue = IntArray(cols * rows)
    private var beamNodes = 0

    private val autoBeamHunger = 120
    private val hungerKillLimit = 500
    private var autoRestartDelay = 250L
    private var restartCountdown = 0L

    private fun hungerForceEat(): Int = when {
        snake.size < 20 -> 50
        snake.size < 35 -> 70
        snake.size < 55 -> 100
        snake.size < 80 -> 140
        else -> 200
    }

    private val frame = object : Choreographer.FrameCallback {
        override fun doFrame(ns: Long) {
            if (!running) return
            if (lastFrame == 0L) lastFrame = ns
            val dt = ((ns - lastFrame) / 1_000_000L).coerceAtMost(100L)
            lastFrame = ns
            if (gameOver) {
                restartCountdown -= dt
                if (restartCountdown <= 0L) reset()
            } else {
                accumulator += dt
                while (accumulator >= gameSpeed) {
                    updateGame()
                    if (gameOver) break
                    accumulator -= gameSpeed
                }
            }
            updateEffects(dt / 16f)
            invalidate()
            Choreographer.getInstance().postFrameCallback(this)
        }
    }

    init {
        highScore = prefs.getInt("high_score", 0)
        money = prefs.getInt("money", 0)
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
        updateCurrentSkin()
        updateCurrentBoard()
        reset()
    }

    fun getAIMode(): Int = aiMode
    fun setAIMode(m: Int) { aiMode = m; reset() }
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
        gameSpeed = 16L; accumulator = 0L; lastFrame = 0L
        particles.clear(); floats.clear(); flash = 0f; restartCountdown = 0L
        ai = Snapshot(chosen = dir)
        placeFood()
        onScoreChanged?.invoke(score)
        invalidate()
    }

    fun resume() {
        if (running) return
        running = true; lastFrame = 0L
        Choreographer.getInstance().postFrameCallback(frame)
    }

    fun pause() {
        running = false
        Choreographer.getInstance().removeFrameCallback(frame)
    }

    private fun updateGame() {
        if (gameOver) return
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
            score += 10 + min(combo, 20); combo++; hunger = 0; money++
            if (score > highScore) { highScore = score; prefs.edit().putInt("high_score", highScore).apply() }
            onScoreChanged?.invoke(score)
            onMoneyChanged?.invoke(money)
            prefs.edit().putInt("money", money).apply()
            learn(2.5f + combo * 0.05f); rewardEatStep()
            spawnFoodEffect(nh); placeFood(); gameSpeed = 16L
        } else {
            snake.removeLast(); hunger++; combo = max(0, combo - 1); learn(0.025f)
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
        val candidates = dirs.map { d -> evaluate(d) }
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
                    strategy = if (usingSafe) "🍎 饥饿强制(安全)" else "🍎 饥饿强制(兜底)",
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
            var bestC: Candidate? = null
            var bestS = -1e30f
            for (cand in legal) {
                val sc = safeFollowScore(cand)
                if (sc > bestS) { bestS = sc; bestC = cand }
            }
            if (bestC != null) {
                lastState = state
                lastAction = dirs.indexOfFirst { it == bestC.d }.coerceAtLeast(0)
                val reg = freeRegion(snake)
                ai = Snapshot(
                    strategy = "🛡 SAFE_FOLLOW 长蛇模式",
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
        val lenBoost = if (snake.size >= safeFollowLength)
            (snake.size.toFloat() / safeFollowLength).coerceIn(1f, 3f)
        else 1f
        val effRegionW = wRegion * lenBoost
        val effTailGood = wTailGood * lenBoost
        val effTailBad = wTailBad * lenBoost
        val regionScoreVal = region * effRegionW
        val mobilityScoreVal = mobility * wMobility
        val tailScoreVal = if (tail) effTailGood else effTailBad
        var foodScoreVal = if (foodDist >= 0) hungerFactor * aggression * (wFoodNear / (foodDist + 1))
                           else -450f * hungerFactor
        if (ate) foodScoreVal += wFoodAte * aggression
        val edge = min(min(sim.body.first().x, cols - 1 - sim.body.first().x),
                       min(sim.body.first().y, rows - 1 - sim.body.first().y))
        val edgeScoreVal = -max(0, 2 - edge) * wEdge
        val spacePenalty = max(0f, snake.size * safetyMargin - region.toFloat())
        val spaceScoreVal = -spacePenalty * wSpace
        val total = regionScoreVal + mobilityScoreVal + tailScoreVal + foodScoreVal + edgeScoreVal + spaceScoreVal
        val reason = when { ate -> "马上吃到食物"; tail -> "保持尾巴可达"; else -> "扩大可用空间" }
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
    private fun tailScore(c: Candidate): Float =
        c.score + if (tailReachable(simulate(snake.first(), c.d).body)) 350f else -500f
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
        val beamDepth = if (snake.size >= safeFollowLength) 7 else 3
        repeat(beamDepth) {
            val next = ArrayList<Node>()
            for (nod in layer) {
                beamNodes++
                if (nod.score > bestScore) {
                    bestScore = nod.score
                    best = legal.firstOrNull { it.d == nod.first } ?: best
                }
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
                    next.add(Node(sm.body, nod.first, sc, nod.depth + 1))
                }
            }
            layer = next.sortedByDescending { it.score }.take(8)
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
        val beforeSpace = wSpace; val beforeFood = wFoodNear; val beforeRegion = wRegion
        when (cause) {
            "WALL" -> { wEdge = clampW(wEdge * 1.15f, 20f, 400f); wRegion = clampW(wRegion * 1.03f, 2f, 50f) }
            "SELF" -> {
                wRegion = clampW(wRegion * 0.95f, 2f, 50f)
                wTailGood = clampW(wTailGood * 1.15f, 60f, 800f)
                wTailBad = clampW(wTailBad * 1.10f, -1500f, -80f)
            }
            "TRAP" -> { wSpace = clampW(wSpace * 1.20f, 8f, 300f); wRegion = clampW(wRegion * 1.05f, 2f, 50f) }
            "HUNGER" -> { wFoodNear = clampW(wFoodNear * 1.25f, 100f, 2500f); wFoodAte = clampW(wFoodAte * 1.15f, 300f, 3000f) }
        }
        lastLearnAction = when (cause) {
            "WALL" -> "边界 ${"%.0f→%.0f".format(beforeEdge, wEdge)} 区域 ${"%.1f→%.1f".format(beforeRegion, wRegion)}"
            "SELF" -> "尾巴+ ${"%.0f→%.0f".format(beforeTail, wTailGood)} 区域 ${"%.1f→%.1f".format(beforeRegion, wRegion)}"
            "TRAP" -> "空间 ${"%.0f→%.0f".format(beforeSpace, wSpace)} 区域 ${"%.1f→%.1f".format(beforeRegion, wRegion)}"
            "HUNGER" -> "食物近 ${"%.0f→%.0f".format(beforeFood, wFoodNear)}"
            else -> "无变化"
        }
        val k = 0.98f; val rk = 1f - k
        wRegion = wRegion * k + wRegion0 * rk
        wMobility = wMobility * k + wMobility0 * rk
        wTailGood = wTailGood * k + wTailGood0 * rk
        wTailBad = wTailBad * k + wTailBad0 * rk
        wFoodNear = wFoodNear * k + wFoodNear0 * rk
        wFoodAte = wFoodAte * k + wFoodAte0 * rk
        wEdge = wEdge * k + wEdge0 * rk
        wSpace = wSpace * k + wSpace0 * rk
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
        if (++steps % 20 == 0) saveLearning()
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
        lastDeathInfo = "死亡=$cause 长度=${snake.size} 分数=$score " +
                "空间=${ai.region} 需求=${(snake.size * safetyMargin).toInt()} " +
                "尾巴=${if (ai.tailReachable) "可达" else "不可达"}"
        saveLearning(); flash = 1f
        vibrator?.let {
            if (Build.VERSION.SDK_INT >= 26) it.vibrate(VibrationEffect.createOneShot(120, VibrationEffect.DEFAULT_AMPLITUDE))
            else { @Suppress("DEPRECATION") it.vibrate(120) }
        }
        restartCountdown = autoRestartDelay
        invalidate()
    }

    private fun reasonFor(c: Candidate, strategy: Int, danger: Int): String = when {
        !c.legal -> "此方向不合法"
        c.d == dir && danger >= 4 -> "危险较高，保持可控路线"
        c.reason == "马上吃到食物" -> "食物可安全取得，收益高"
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

    private fun legalDirection(d: P): Boolean =
        d != P(0, 0) && !isReverse(d, dir) && canSim(snake, d)

    private fun isReverse(a: P, b: P): Boolean = a.x == -b.x && a.y == -b.y

    private fun directionOfFirst(body: ArrayDeque<P>): P {
        if (body.size < 2) return dir
        return P(body.elementAt(0).x - body.elementAt(1).x, body.elementAt(0).y - body.elementAt(1).y)
    }

    private fun inside(p: P): Boolean = p.x in 0 until cols && p.y in 0 until rows

    private fun freeRegion(body: ArrayDeque<P>): Int {
        if (body.isEmpty()) return 0
        val total = cols * rows
        java.util.Arrays.fill(bfsVisited, false)
        for (p in body) {
            if (p.x !in 0 until cols || p.y !in 0 until rows) continue
            val index = p.y * cols + p.x
            if (index in 0 until total) bfsVisited[index] = true
        }
        val start = body.first()
        if (start.x !in 0 until cols || start.y !in 0 until rows) return 0
        val startIndex = start.y * cols + start.x
        if (startIndex !in 0 until total) return 0
        bfsVisited[startIndex] = false
        var head = 0; var tail = 0
        bfsQueue[tail++] = startIndex
        var count = 0
        while (head < tail) {
            val curr = bfsQueue[head++]
            if (curr !in 0 until total) continue
            val cx = curr % cols; val cy = curr / cols
            count++
            fun addNode(index: Int) {
                if (index !in 0 until total) return
                if (bfsVisited[index]) return
                bfsVisited[index] = true
                if (tail < bfsQueue.size) bfsQueue[tail++] = index
            }
            if (cx > 0) addNode(curr - 1)
            if (cx < cols - 1) addNode(curr + 1)
            if (cy > 0) addNode(curr - cols)
            if (cy < rows - 1) addNode(curr + cols)
        }
        return count
    }

    private fun distance(start: P, target: P, body: Collection<P>, allowTail: Boolean): Int {
        if (start.x !in 0 until cols || start.y !in 0 until rows ||
            target.x !in 0 until cols || target.y !in 0 until rows) return -1
        if (start == target) return 0
        val total = cols * rows
        java.util.Arrays.fill(bfsVisited, false)
        for (p in body) {
            if (p.x !in 0 until cols || p.y !in 0 until rows) continue
            val index = p.y * cols + p.x
            if (index in 0 until total) bfsVisited[index] = true
        }
        if (allowTail && body.isNotEmpty()) {
            val last = body.last()
            if (last.x in 0 until cols && last.y in 0 until rows) {
                val lastIndex = last.y * cols + last.x
                if (lastIndex in 0 until total) bfsVisited[lastIndex] = false
            }
        }
        val startIndex = start.y * cols + start.x
        if (startIndex !in 0 until total) return -1
        bfsVisited[startIndex] = false
        var head = 0; var tail = 0
        bfsQueue[tail++] = startIndex
        var dist = 0
        while (head < tail) {
            val layerSize = tail - head
            var i = 0
            while (i < layerSize) {
                i++
                if (head >= tail) break
                val curr = bfsQueue[head++]
                if (curr !in 0 until total) continue
                val cx = curr % cols; val cy = curr / cols
                if (cx == target.x && cy == target.y) return dist
                fun addNode(index: Int) {
                    if (index !in 0 until total) return
                    if (bfsVisited[index]) return
                    bfsVisited[index] = true
                    if (tail < bfsQueue.size) bfsQueue[tail++] = index
                }
                if (cx > 0) addNode(curr - 1)
                if (cx < cols - 1) addNode(curr + 1)
                if (cy > 0) addNode(curr - cols)
                if (cy < rows - 1) addNode(curr + cols)
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
        cell = min(w.toFloat() / cols, h.toFloat() / rows)
        ox = (w - cols * cell) / 2f
        oy = (h - rows * cell) / 2f
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

    /* ============================================================
     * 可视化辅助函数
     * ============================================================ */

    private fun drawDangerGauge(c: Canvas, cx: Float, cy: Float, r: Float, danger: Int) {
        val arcPaint = Paint(Paint.ANTI_ALIAS_FLAG)
        arcPaint.style = Paint.Style.STROKE
        arcPaint.strokeWidth = 10f
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
            c.drawRect(x + 2f, top, x + barW - 6f, top + h, barPaint)

            // 100% 基准线
            barPaint.color = Color.rgb(100, 100, 100)
            val baseY = top + h - h * (1f / maxRatio)
            c.drawLine(x + 2f, baseY, x + barW - 6f, baseY, barPaint)

            // 柱子颜色反映偏离程度
            barPaint.color = when {
                ratio > 1.3f -> Color.rgb(231, 76, 60)
                ratio > 1.1f -> Color.rgb(241, 196, 15)
                ratio < 0.8f -> Color.rgb(52, 152, 219)
                else -> Color.rgb(46, 204, 113)
            }
            c.drawRect(x + 2f, top + h - barH, x + barW - 6f, top + h, barPaint)

            // 标签
            text.textAlign = Paint.Align.CENTER
            text.textSize = 9f
            text.color = Color.LTGRAY
            c.drawText(name, x + (barW - 4f) / 2f, top + h + 11f, text)

            // 百分比
            text.textSize = 9f
            text.color = Color.WHITE
            val pct = (values[i] * 100f).toInt()
            c.drawText("$pct%", x + (barW - 4f) / 2f, top + h + 23f, text)
        }
        text.textAlign = Paint.Align.LEFT
    }

    private fun drawLearningCurve(c: Canvas, left: Float, top: Float, w: Float, h: Float) {
        barPaint.style = Paint.Style.FILL
        barPaint.color = Color.rgb(25, 25, 25)
        c.drawRect(left, top, left + w, top + h, barPaint)

        if (recentScores.size < 2) {
            text.textAlign = Paint.Align.CENTER
            text.textSize = 10f
            text.color = Color.GRAY
            c.drawText("数据不足", left + w / 2f, top + h / 2f, text)
            text.textAlign = Paint.Align.LEFT
            return
        }

        val scores = recentScores.toList()
        val maxScore = scores.max().coerceAtLeast(1)
        val stepX = w / (scores.size - 1).coerceAtLeast(1)

        // 面积填充
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

        // 折线
        val linePath = Path()
        scores.forEachIndexed { i, s ->
            val x = left + i * stepX
            val y = top + h - h * (s.toFloat() / maxScore)
            if (i == 0) linePath.moveTo(x, y) else linePath.lineTo(x, y)
        }

        val curvePaint = Paint(Paint.ANTI_ALIAS_FLAG)
        curvePaint.style = Paint.Style.STROKE
        curvePaint.strokeWidth = 2f
        curvePaint.color = Color.rgb(120, 255, 180)
        c.drawPath(linePath, curvePaint)

        text.textSize = 9f
        text.color = Color.LTGRAY
        c.drawText("max $maxScore", left + 4f, top + 10f, text)
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

    /* ============================================================
     * 主绘制
     * ============================================================ */
    private fun drawDebug(c: Canvas) {
        if (aiMode == 0 && !gameOver) return

        val w = min(width * 0.97f, 720f)
        val h = 560f
        val left = (width - w) / 2f
        val top = if (gameOver) max(12f, height - h - 12f) else 12f

        panel.color = Color.argb(230, 0, 0, 0)
        c.drawRoundRect(left, top, left + w, top + h, 22f, 22f, panel)

        border.color = when (ai.danger) {
            1 -> Color.GREEN
            2 -> Color.rgb(150, 255, 80)
            3 -> Color.YELLOW
            4 -> Color.rgb(255, 150, 0)
            else -> Color.RED
        }
        border.style = Paint.Style.STROKE
        border.strokeWidth = 4f
        c.drawRoundRect(left, top, left + w, top + h, 22f, 22f, border)

        text.textAlign = Paint.Align.LEFT

        // ─── 标题 ───
        text.isFakeBoldText = true
        text.textSize = 20f
        text.color = Color.WHITE
        c.drawText("🧠 ${ai.strategy}", left + 16f, top + 28f, text)

        text.isFakeBoldText = false
        text.textSize = 11f
        text.color = Color.YELLOW
        c.drawText(ai.reason, left + 16f, top + 45f, text)

        // ─── 危险圆环 ───
        val gaugeCX = left + 48f
        val gaugeCY = top + 90f
        val gaugeR = 32f
        drawDangerGauge(c, gaugeCX, gaugeCY, gaugeR, ai.danger)

        text.textAlign = Paint.Align.CENTER
        text.isFakeBoldText = true
        text.textSize = 20f
        text.color = Color.WHITE
        c.drawText("${ai.danger}", gaugeCX, gaugeCY + 7f, text)
        text.isFakeBoldText = false
        text.textSize = 9f
        text.color = Color.LTGRAY
        c.drawText("危险", gaugeCX, gaugeCY + 22f, text)

        // ─── 状态 ───
        text.textAlign = Paint.Align.LEFT
        text.textSize = 12f
        text.color = Color.WHITE
        c.drawText(
            "空间 ${ai.region}   比例 ${"%.1f".format(ai.spaceRatio)}",
            left + 95f, top + 68f, text
        )
        c.drawText(
            "尾巴 ${if (ai.tailReachable) "✓" else "✗"}   " +
                "食物 ${if (ai.foodReachable) "✓" else "✗"}   " +
                "距离 ${if (ai.foodDistance < 0) "∞" else ai.foodDistance}",
            left + 95f, top + 84f, text
        )
        c.drawText(
            "Q ${"%+.3f".format(ai.qValue)}   访问 ${ai.nVisits}   深度 ${ai.depth}",
            left + 95f, top + 100f, text
        )

        // ─── 权重柱状图 ───
        val wbY = top + 130f
        text.textAlign = Paint.Align.LEFT
        text.isFakeBoldText = true
        text.textSize = 11f
        text.color = Color.rgb(255, 200, 100)
        c.drawText("【权重柱状图】100% = 初始值   越长=当前越在意", left + 16f, wbY, text)
        text.isFakeBoldText = false
        drawWeightBars(c, left + 16f, wbY + 6f, w - 32f, 50f)

        // ─── 上次学习 ───
        val learnY = top + 222f
        text.textSize = 11f
        text.isFakeBoldText = true
        text.color = Color.rgb(255, 150, 255)
        c.drawText("【上次学习】", left + 16f, learnY, text)
        text.isFakeBoldText = false
        text.color = Color.WHITE
        c.drawText("$deathCause → $lastLearnAction", left + 95f, learnY, text)

        // ─── 四方向安全条 ───
        val barStartX = left + 95f
        val barEndX = left + w - 16f
        val barW = barEndX - barStartX
        var barY = top + 244f

        text.isFakeBoldText = true
        text.textSize = 11f
        text.color = Color.rgb(255, 200, 100)
        c.drawText("【四方向安全】", left + 16f, barY, text)
        text.isFakeBoldText = false
        barY += 8f

        val dirNames = listOf("↑", "↓", "←", "→")
        ai.candidates.forEachIndexed { idx, cand ->
            text.textSize = 16f
            text.color = if (!cand.legal) Color.GRAY
                        else if (cand.d == ai.chosen) Color.CYAN
                        else Color.WHITE
            c.drawText(dirNames[idx], left + 16f, barY + 13f, text)

            if (!cand.legal) {
                text.textSize = 10f
                text.color = Color.GRAY
                c.drawText("非法", barStartX, barY + 13f, text)
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
                c.drawRoundRect(barStartX, barY, barEndX, barY + 17f, 4f, 4f, barPaint)

                val barColor = when {
                    safeScore >= 0.9f -> Color.rgb(46, 204, 113)
                    safeScore >= 0.7f -> Color.rgb(241, 196, 15)
                    safeScore >= 0.5f -> Color.rgb(230, 126, 34)
                    else -> Color.rgb(231, 76, 60)
                }
                barPaint.color = barColor
                c.drawRoundRect(barStartX, barY, barStartX + barW * safeScore, barY + 17f, 4f, 4f, barPaint)

                text.textSize = 10f
                text.color = Color.WHITE
                c.drawText(
                    "空间${cand.region} 尾${if (cand.tailOk) "✓" else "✗"} " +
                        "食${if (cand.foodDist < 0) "∞" else cand.foodDist} " +
                        "分${"%.0f".format(cand.score)}",
                    barStartX + 6f, barY + 12f, text
                )
            }
            barY += 20f
        }

        // ─── 饥饿进度 ───
        val hungerY = barY + 6f
        text.isFakeBoldText = true
        text.textSize = 11f
        text.color = Color.rgb(255, 200, 100)
        c.drawText("【饥饿】", left + 16f, hungerY + 12f, text)
        text.isFakeBoldText = false

        val hForce = hungerForceEat()
        val hRatio = (hunger.toFloat() / hungerKillLimit).coerceIn(0f, 1f)

        barPaint.color = Color.rgb(40, 40, 40)
        c.drawRoundRect(barStartX, hungerY, barEndX, hungerY + 17f, 4f, 4f, barPaint)

        val hColor = when {
            hunger >= hungerKillLimit -> Color.RED
            hunger >= autoBeamHunger -> Color.rgb(255, 100, 50)
            hunger >= hForce -> Color.rgb(241, 196, 15)
            hunger >= 30 -> Color.rgb(230, 200, 100)
            else -> Color.rgb(100, 200, 100)
        }
        barPaint.color = hColor
        c.drawRoundRect(barStartX, hungerY, barStartX + barW * hRatio, hungerY + 17f, 4f, 4f, barPaint)

        // 阈值标记线
        val forcePos = barStartX + barW * (hForce.toFloat() / hungerKillLimit)
        val beamPos = barStartX + barW * (autoBeamHunger.toFloat() / hungerKillLimit)
        barPaint.color = Color.WHITE
        c.drawLine(forcePos, hungerY, forcePos, hungerY + 17f, barPaint)
        c.drawLine(beamPos, hungerY, beamPos, hungerY + 17f, barPaint)

        text.textSize = 10f
        text.color = Color.WHITE
        c.drawText(
            "$hunger/$hungerKillLimit  强制${hForce}  BEAM${autoBeamHunger}",
            barStartX + 6f, hungerY + 12f, text
        )

        // ─── 学习曲线 + 死亡饼图 ───
        val chartY = hungerY + 28f
        val chartH = 55f

        val curveX = left + 16f
        val curveW = (w - 32f) * 0.55f

        text.isFakeBoldText = true
        text.textSize = 11f
        text.color = Color.rgb(120, 255, 180)
        c.drawText("【学习曲线】", curveX, chartY, text)
        text.isFakeBoldText = false
        drawLearningCurve(c, curveX, chartY + 5f, curveW, chartH)

        // 饼图
        val pieCX = left + w - 110f
        val pieCY = chartY + chartH / 2f + 8f
        val pieR = 26f

        text.isFakeBoldText = true
        text.textSize = 11f
        text.color = Color.rgb(255, 150, 150)
        c.drawText("【死亡统计】", pieCX - 40f, chartY, text)
        text.isFakeBoldText = false
        drawDeathPie(c, pieCX, pieCY, pieR)

        // 饼图旁边的数字
        text.textAlign = Paint.Align.LEFT
        text.textSize = 10f
        text.color = Color.rgb(255, 100, 100)
        c.drawText("W $deathWall", pieCX + 32f, pieCY - 12f, text)
        text.color = Color.rgb(100, 150, 255)
        c.drawText("S $deathSelf", pieCX + 32f, pieCY + 4f, text)
        text.color = Color.rgb(255, 200, 100)
        c.drawText("T $deathTrap", pieCX + 32f, pieCY + 20f, text)

        // ─── Q表热度矩阵 ───
        val heatY = chartY + chartH + 22f
        text.textAlign = Paint.Align.LEFT
        text.isFakeBoldText = true
        text.textSize = 11f
        text.color = Color.rgb(200, 180, 255)
        c.drawText("【Q表热度 10×10=100状态】绿=高价值 红=负价值 灰=未访问", left + 16f, heatY, text)
        text.isFakeBoldText = false
        drawQHeatmap(c, left + 16f, heatY + 5f, w - 32f, 50f)

        // ─── 底部信息 ───
        val infoY = heatY + 5f + 50f + 18f
        val avg = if (recentScores.isEmpty()) 0f else recentScores.average().toFloat()

        var nonZero = 0; var sumQ = 0f; var cntQ = 0
        for (s in 0 until 100) for (a in 0 until 4) {
            if (n[s][a] > 0) { nonZero++; sumQ += q[s][a]; cntQ++ }
        }
        val avgQ = if (cntQ > 0) sumQ / cntQ else 0f

        text.textSize = 11f
        text.color = Color.WHITE
        text.textAlign = Paint.Align.LEFT
        c.drawText(
            "局数 $totalGames   近50均分 ${"%.1f".format(avg)}   最佳 $bestRecentScore   " +
                "Q非零 $nonZero/400   平均Q ${"%+.3f".format(avgQ)}",
            left + 16f, infoY, text
        )
        c.drawText(
            "蛇长 ${snake.size}  分数 $score  饥饿 $hunger  最高 $highScore  金币 $money  " +
                "攻击×${"%.2f".format(aggression)}  安全×${"%.2f".format(safetyMargin)}",
            left + 16f, infoY + 16f, text
        )

        if (gameOver) {
            text.color = Color.RED
            text.isFakeBoldText = true
            text.textSize = 13f
            c.drawText("死亡原因：$deathCause", left + 16f, infoY + 36f, text)
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
        c.drawText("自动重开中…", width / 2f, height / 2f + 20, text)

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
}
