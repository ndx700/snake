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
import kotlin.math.sin
import kotlin.random.Random

class SnakeView @JvmOverloads constructor(
    context: Context,
    attrs: AttributeSet? = null
) : View(context, attrs) {

    // =========================================================
    // 基础
    // =========================================================

    private val cols = 15
    private val rows = 15
    private val totalCells = cols * rows

    private data class P(
        val x: Int,
        val y: Int
    )

    private data class Candidate(
        val d: P,
        val score: Float,
        val reason: String,
        val legal: Boolean
    )

    private data class Snapshot(
        var strategy: String = "AUTO",
        var reason: String = "初始化",
        var danger: Int = 1,
        var region: Int = 1,
        var spaceRatio: Float = 1f,
        var tailReachable: Boolean = false,
        var foodReachable: Boolean = false,
        var foodDistance: Int = -1,
        var hunger: Int = 0,
        var chosen: P = P(1, 0),
        var candidates: List<Candidate> = emptyList(),
        var depth: Int = 0,
        var nodes: Int = 0
    )

    private data class Sim(
        val body: ArrayDeque<P>,
        val ate: Boolean
    )

    private data class BeamNode(
        val body: ArrayDeque<P>,
        val first: P,
        val score: Float,
        val depth: Int
    )

    private data class Particle(
        var x: Float,
        var y: Float,
        var vx: Float,
        var vy: Float,
        var life: Float,
        val color: Int
    )

    private data class FloatText(
        var x: Float,
        var y: Float,
        var life: Float,
        val text: String
    )

    private data class Ripple(
        var x: Float,
        var y: Float,
        var life: Float
    )

    // =========================================================
    // 蛇
    // =========================================================

    private val snake = ArrayDeque<P>()
    private val queue = ArrayDeque<P>()

    private var prevSnake: List<P> = emptyList()

    private val dirs = listOf(
        P(0, -1),
        P(0, 1),
        P(-1, 0),
        P(1, 0)
    )

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
    private var accumulator = 0L
    private var lastFrame = 0L
    private var moveProgress = 0f

    private var combo = 0
    private var hunger = 0

    private var deathCause = "无"
    private var lastDeathInfo = ""

    private var aggression = 1.08f
    private var safetyMargin = 1.12f
    private var shortcutBonus = 0.88f

    private var deathWall = 0
    private var deathSelf = 0
    private var deathTrap = 0
    private var totalGames = 0

    private var ai = Snapshot()

    // =========================================================
    // AI
    // =========================================================

    private companion object {

        const val SPEED_START = 220L
        const val SPEED_MIN = 60L
        const val SPEED_DECAY = 1500f

        // 新 AI
        const val CURRENT_AI_VERSION = 4

        const val STRATEGY_BFS = 0
        const val STRATEGY_TAIL = 1
        const val STRATEGY_HAM = 2
        const val STRATEGY_BEAM = 3
    }

    private val q = Array(20) { FloatArray(5) }
    private val n = Array(20) { IntArray(5) }

    private var lastState = -1
    private var lastAction = -1
    private var steps = 0
    private var saveCounter = 0

    private var beamNodes = 0

    // =========================================================
    // 回调
    // =========================================================

    var onScoreChanged: ((Int) -> Unit)? = null
    var onMoneyChanged: ((Int) -> Unit)? = null

    private val prefs =
        context.getSharedPreferences("snake_prefs", Context.MODE_PRIVATE)

    private val vibrator: Vibrator? =
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
            val vm =
                context.getSystemService(Context.VIBRATOR_MANAGER_SERVICE)
                    as? VibratorManager
            vm?.defaultVibrator
        } else {
            @Suppress("DEPRECATION")
            context.getSystemService(Context.VIBRATOR_SERVICE) as? Vibrator
        }

    // =========================================================
    // 颜色 / 皮肤
    // =========================================================

    private var bodyColor = Color.rgb(40, 220, 90)
    private var headColor = Color.rgb(100, 255, 130)

    private var bgColor = Color.BLACK
    private var gridColor = Color.rgb(20, 80, 30)

    private var rainbowSkin = false

    private val hsv = IntArray(360)

    // =========================================================
    // 绘制对象
    // =========================================================

    private val paint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val text = Paint(Paint.ANTI_ALIAS_FLAG)

    private val snakePaint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val headPaint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val foodPaint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val gridPaint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val bgPaint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val glowPaint = Paint(Paint.ANTI_ALIAS_FLAG)

    private val panel = Paint(Paint.ANTI_ALIAS_FLAG)
    private val border = Paint(Paint.ANTI_ALIAS_FLAG)

    private var cell = 1f
    private var ox = 0f
    private var oy = 0f

    private var globalTime = 0f
    private var foodPhase = 0f
    private var flash = 0f

    private var shakeAmp = 0f
    private var shakeX = 0f
    private var shakeY = 0f

    private val particles = ArrayList<Particle>()
    private val floats = ArrayList<FloatText>()
    private val ripples = ArrayList<Ripple>()

    private var ptsBuf = FloatArray(0)

    // =========================================================
    // BFS 缓冲
    // =========================================================

    private val bfsVisited = BooleanArray(totalCells)
    private val bfsQueue = IntArray(totalCells)
    private val bfsParent = IntArray(totalCells)

    // =========================================================
    // 初始化
    // =========================================================

    init {

        loadPrefs()
        loadLearning()

        val oldVersion =
            prefs.getInt("ai_version", 0)

        if (oldVersion != CURRENT_AI_VERSION) {

            for (i in q.indices) {
                java.util.Arrays.fill(q[i], 0f)
                java.util.Arrays.fill(n[i], 0)
            }

            lastState = -1
            lastAction = -1

            prefs.edit()
                .putInt("ai_version", CURRENT_AI_VERSION)
                .apply()
        }

        for (i in 0 until 360) {
            hsv[i] = Color.HSVToColor(
                floatArrayOf(i.toFloat(), 0.85f, 1f)
            )
        }

        setLayerType(View.LAYER_TYPE_HARDWARE, null)

        updateCurrentSkin(
            prefs.getString("skin", "green") ?: "green"
        )

        updateCurrentBoard(
            prefs.getString("board", "dark") ?: "dark"
        )

        reset()
    }

    // =========================================================
    // 生命周期
    // =========================================================

    override fun onDetachedFromWindow() {
        pause()
        super.onDetachedFromWindow()
    }

    // =========================================================
    // 对外接口
    // =========================================================

    fun getAIMode(): Int = aiMode

    fun setAIMode(mode: Int) {

        aiMode = mode.coerceIn(0, 1)

        if (aiMode != 0) {
            queue.clear()
        }

        reset()
    }

    fun setForcedStrategy(strategy: Int) {

        forcedStrategy =
            when (strategy) {
                0, 1, 2, 3 -> strategy
                else -> -1
            }

        if (running && aiMode != 0) {
            chooseMove()
        }

        invalidate()
    }

    fun updateCurrentSkin(id: String) {

        rainbowSkin = id == "rgb"

        when (id) {

            "blue" -> {
                bodyColor = Color.rgb(40, 130, 255)
                headColor = Color.rgb(100, 200, 255)
            }

            "red" -> {
                bodyColor = Color.rgb(220, 40, 40)
                headColor = Color.rgb(255, 100, 80)
            }

            "purple" -> {
                bodyColor = Color.rgb(150, 50, 230)
                headColor = Color.rgb(210, 120, 255)
            }

            "gold" -> {
                bodyColor = Color.rgb(210, 150, 30)
                headColor = Color.rgb(255, 220, 80)
            }

            "rgb" -> {
                bodyColor = Color.WHITE
                headColor = Color.WHITE
            }

            else -> {
                bodyColor = Color.rgb(40, 220, 90)
                headColor = Color.rgb(100, 255, 130)
            }
        }

        prefs.edit()
            .putString("skin", id)
            .apply()

        invalidate()
    }

    fun setSnakeColors(
        body: Int,
        head: Int
    ) {
        bodyColor = body
        headColor = head
        rainbowSkin = false
        invalidate()
    }

    fun updateCurrentBoard(id: String) {

        when (id) {

            "light" -> {
                bgColor = Color.rgb(245, 245, 245)
                gridColor = Color.rgb(180, 180, 180)
            }

            "blue" -> {
                bgColor = Color.rgb(0, 8, 25)
                gridColor = Color.rgb(20, 100, 220)
            }

            "forest" -> {
                bgColor = Color.rgb(3, 18, 8)
                gridColor = Color.rgb(30, 110, 50)
            }

            "cyberpunk" -> {
                bgColor = Color.rgb(10, 0, 20)
                gridColor = Color.rgb(180, 30, 220)
            }

            "rainbow" -> {
                bgColor = Color.rgb(5, 5, 10)
                gridColor = Color.rgb(80, 80, 255)
            }

            else -> {
                bgColor = Color.BLACK
                gridColor = Color.rgb(20, 80, 30)
            }
        }

        prefs.edit()
            .putString("board", id)
            .apply()

        invalidate()
    }

    // =========================================================
    // 存档
    // =========================================================

    private fun loadPrefs() {

        highScore = prefs.getInt("high_score", 0)
        money = prefs.getInt("money", 0)

        aggression =
            prefs.getFloat("aggression", 1.08f)

        safetyMargin =
            prefs.getFloat("safety_margin", 1.12f)

        shortcutBonus =
            prefs.getFloat("shortcut_bonus", 0.88f)
    }

    private fun loadLearning() {

        for (s in q.indices) {
            for (a in q[s].indices) {

                q[s][a] =
                    prefs.getFloat("q_${s}_$a", 0f)

                n[s][a] =
                    prefs.getInt("n_${s}_$a", 0)
            }
        }
    }

    private fun saveLearning() {

        val e = prefs.edit()

        for (s in q.indices) {
            for (a in q[s].indices) {

                e.putFloat(
                    "q_${s}_$a",
                    q[s][a]
                )

                e.putInt(
                    "n_${s}_$a",
                    n[s][a]
                )
            }
        }

        e.putFloat("aggression", aggression)
        e.putFloat("safety_margin", safetyMargin)
        e.putFloat("shortcut_bonus", shortcutBonus)

        e.apply()
    }

    // =========================================================
    // 速度 / 倍率 / 阶段
    // =========================================================

    private fun computeGameSpeed(): Long {

        val decay =
            kotlin.math.exp(
                -score / SPEED_DECAY
            )

        return (
            SPEED_MIN +
                (SPEED_START - SPEED_MIN) * decay
            ).toLong().coerceIn(
                SPEED_MIN,
                SPEED_START
            )
    }

    private fun computeScoreMultiplier(): Float {

        return when {

            score < 20 -> 1f
            score < 50 -> 1.3f
            score < 100 -> 1.7f
            score < 180 -> 2.2f
            score < 300 -> 2.8f
            score < 450 -> 3.5f
            score < 650 -> 4.2f
            score < 900 -> 5f

            else ->
                min(
                    8f,
                    5f + (score - 900) / 1000f
                )
        }
    }

    private fun computeStage(): Int {

        return when {

            score < 20 -> 0
            score < 50 -> 1
            score < 100 -> 2
            score < 180 -> 3
            score < 280 -> 4
            score < 400 -> 5
            score < 550 -> 6
            score < 750 -> 7
            score < 1000 -> 8
            score < 1400 -> 9
            else -> 10
        }
    }

    // =========================================================
    // 重置
    // =========================================================

    private fun reset() {

        snake.clear()
        queue.clear()

        val start =
            if (aiMode == 2) {
                P(0, 0)
            } else {
                P(cols / 2, rows / 2)
            }

        snake.add(start)

        dir = P(1, 0)

        if (aiMode == 2) {
            dir = P(1, 0)
        }

        prevSnake = snake.toList()

        score = 0
        combo = 0
        hunger = 0

        gameOver = false
        deathCause = "无"
        lastDeathInfo = ""

        gameSpeed = SPEED_START
        accumulator = 0L
        moveProgress = 0f

        aggression =
            aggression.coerceIn(0.8f, 1.35f)

        safetyMargin =
            safetyMargin.coerceIn(1.03f, 1.28f)

        ai = Snapshot(
            chosen = dir
        )

        particles.clear()
        floats.clear()
        ripples.clear()

        placeFood()

        onScoreChanged?.invoke(score)
        onMoneyChanged?.invoke(money)

        invalidate()
    }

    fun resume() {

        if (gameOver) {
            reset()
        }

        running = true
        lastFrame = 0L

        Choreographer.getInstance()
            .postFrameCallback(frameCallback)
    }

    fun pause() {
        running = false
    }

    // =========================================================
    // 帧循环
    // =========================================================

    private val frameCallback =
        object : Choreographer.FrameCallback {

            override fun doFrame(frameTimeNanos: Long) {

                if (!running) {
                    return
                }

                if (lastFrame == 0L) {
                    lastFrame = frameTimeNanos
                }

                val dt =
                    (frameTimeNanos - lastFrame) / 1_000_000L

                lastFrame = frameTimeNanos

                accumulator +=
                    dt.coerceIn(0L, 100L)

                var loops = 0

                while (
                    accumulator >= gameSpeed &&
                    loops < 4 &&
                    !gameOver
                ) {

                    updateGame()

                    accumulator -= gameSpeed
                    loops++
                }

                moveProgress =
                    (
                        accumulator.toFloat() /
                            max(1L, gameSpeed).toFloat()
                        ).coerceIn(0f, 1f)

                updateEffects(
                    dt.toFloat()
                )

                invalidate()

                Choreographer.getInstance()
                    .postFrameCallback(this)
            }
        }

    // =========================================================
    // 游戏更新
    // =========================================================

    private fun updateGame() {

        if (snake.isEmpty()) {
            return
        }

        prevSnake = snake.toList()

        if (aiMode != 0) {

            val chosen = chooseMove()

            if (
                !isReverse(chosen, dir) &&
                legalDirection(chosen)
            ) {
                queue.add(chosen)
            }
        }

        if (queue.isNotEmpty()) {

            val requested = queue.removeFirst()

            if (
                !isReverse(requested, dir) &&
                legalDirection(requested)
            ) {
                dir = requested
            }
        }

        val head = snake.first()

        val newHead = P(
            head.x + dir.x,
            head.y + dir.y
        )

        if (!inside(newHead)) {

            deathWall++

            die("撞墙")
            return
        }

        val willEat = newHead == food

        val occupied =
            snake.contains(newHead)

        val tail = snake.last()

        val hitsTail =
            newHead == tail && !willEat

        if (occupied && !hitsTail) {

            val test = ArrayDeque<P>()

            test.add(newHead)

            for (p in snake) {
                test.add(p)
            }

            if (!willEat && test.isNotEmpty()) {
                test.removeLast()
            }

            val region = freeRegion(test)

            val need =
                max(
                    2,
                    (snake.size * safetyMargin).toInt()
                )

            if (region < need) {
                deathTrap++
                die("进入死区")
            } else {
                deathSelf++
                die("撞到自己")
            }

            return
        }

        snake.addFirst(newHead)

        if (willEat) {

            val mul = computeScoreMultiplier()

            val gained =
                (10f * mul).toInt()

            score += gained
            combo++
            hunger = 0

            money++

            if (score > highScore) {
                highScore = score
            }

            onScoreChanged?.invoke(score)
            onMoneyChanged?.invoke(money)

            prefs.edit()
                .putInt("high_score", highScore)
                .putInt("money", money)
                .apply()

            learn(1.5f)

            spawnFoodEffect(
                newHead,
                gained,
                mul
            )

            flash = 0.12f
            shakeAmp = 2.5f

            placeFood()

            gameSpeed =
                computeGameSpeed()

        } else {

            if (snake.isNotEmpty()) {
                snake.removeLast()
            }

            hunger++

            if (combo > 0) {
                combo--
            }

            learn(0.02f)
        }

        if (hunger > max(80, snake.size * 5)) {

            hunger = 0

            if (combo > 0) {
                combo--
            }
        }

        steps++
    }

    // =========================================================
    // AI 主入口
    // =========================================================

    private fun chooseMove(): P {

        val candidates =
            dirs.map { evaluate(it) }

        val legal =
            candidates.filter { it.legal }

        if (legal.isEmpty()) {

            ai = Snapshot(
                strategy = "NO MOVE",
                reason = "四个方向都不安全",
                danger = 5,
                region = freeRegion(snake),
                spaceRatio =
                    freeRegion(snake).toFloat() /
                        max(1, snake.size),
                tailReachable = tailReachable(snake),
                foodReachable = false,
                foodDistance = -1,
                hunger = hunger,
                chosen = dir,
                candidates = candidates,
                depth = 0,
                nodes = candidates.size
            )

            return dir
        }

        val danger =
            calculateDanger()

        val state =
            learnState(
                snake.size,
                danger
            )

        val strategy =
            selectStrategy(
                state,
                danger
            )

        val selectedStrategy =
            if (forcedStrategy >= 0) {
                forcedStrategy
            } else {
                strategy
            }

        val final =
            when (selectedStrategy) {

                STRATEGY_BFS ->
                    bfsChoose(legal)

                STRATEGY_TAIL ->
                    tailChoose(legal)

                STRATEGY_HAM ->
                    hamChoose(legal)

                else ->
                    beamBest(legal)
            } ?: legal.maxByOrNull {
                it.score
            } ?: legal.first()

        val region =
            freeRegion(snake)

        val ratio =
            region.toFloat() /
                max(1, snake.size)

        val tail =
            tailReachable(snake)

        val foodDist =
            distance(
                snake.first(),
                food,
                snake,
                true
            )

        ai = Snapshot(
            strategy =
                strategyName(selectedStrategy),

            reason =
                reasonFor(
                    final,
                    strategy,
                    danger
                ),

            danger = danger,

            region = region,

            spaceRatio = ratio,

            tailReachable = tail,

            foodReachable =
                foodDist >= 0,

            foodDistance =
                foodDist,

            hunger = hunger,

            chosen = final.d,

            candidates = candidates,

            depth =
                if (
                    selectedStrategy ==
                    STRATEGY_BEAM
                ) 5 else 2,

            nodes =
                if (
                    selectedStrategy ==
                    STRATEGY_BEAM
                ) {
                    beamNodes
                } else {
                    candidates.size
                }
        )

        return final.d
    }

    // =========================================================
    // AI 评价
    // =========================================================

    private fun evaluate(d: P): Candidate {

        if (!legalDirection(d)) {

            return Candidate(
                d,
                -1_000_000f,
                "撞墙/身体/反向",
                false
            )
        }

        val sim = simulate(d)

        if (sim.body.isEmpty()) {

            return Candidate(
                d,
                -1_000_000f,
                "模拟失败",
                false
            )
        }

        val body = sim.body

        val region =
            freeRegion(body)

        val mobility =
            countSafeMoves(body)

        val tail =
            tailReachable(body)

        val foodDist =
            distance(
                body.first(),
                food,
                body,
                true
            )

        val danger =
            futureDanger(body)

        val trap =
            trapRisk(body)

        val edge =
            edgeDistance(body.first())

        var s = 0f

        // -----------------------------------------------------
        // 1. 生存空间：最高优先级
        // -----------------------------------------------------

        s += region * 18f

        s += mobility * 48f

        val required =
            max(
                5,
                (body.size * safetyMargin).toInt()
            )

        if (region < required) {
            s -= (
                required - region
                ) * 100f
        }

        // -----------------------------------------------------
        // 2. 尾巴可达
        // -----------------------------------------------------

        if (tail) {
            s += 360f
        } else {
            s -= 700f
        }

        // -----------------------------------------------------
        // 3. 未来陷阱
        // -----------------------------------------------------

        s -= trap * 150f

        if (danger >= 4) {
            s -= futureDanger(body) * 120f
        }

        // -----------------------------------------------------
        // 4. 食物
        // -----------------------------------------------------

        if (foodDist >= 0) {

            val foodValue =
                when {

                    danger >= 4 ->
                        35f / (foodDist + 1)

                    danger == 3 ->
                        80f / (foodDist + 1)

                    else ->
                        (
                            260f *
                                aggression
                            ) / (foodDist + 1)
                }

            s += foodValue

        } else {

            s -= 100f
        }

        // -----------------------------------------------------
        // 5. 吃食物后的评估
        // -----------------------------------------------------

        if (sim.ate) {

            val postRegion =
                freeRegion(body)

            val postTail =
                tailReachable(body)

            if (postTail) {
                s += 450f
            } else {
                s -= 650f
            }

            if (
                postRegion >=
                max(
                    6,
                    (body.size * 0.8f).toInt()
                )
            ) {
                s += 350f
            } else {
                s -= 500f
            }
        }

        // -----------------------------------------------------
        // 6. 靠墙惩罚
        // -----------------------------------------------------

        if (edge == 0) {
            s -= 110f
        } else if (edge == 1) {
            s -= 45f
        }

        // -----------------------------------------------------
        // 7. 头部周围拥挤
        // -----------------------------------------------------

        var nearby = 0

        for (other in body.drop(1)) {

            val dist =
                abs(
                    other.x - body.first().x
                ) +
                    abs(
                        other.y - body.first().y
                    )

            if (dist <= 2) {
                nearby++
            }
        }

        s -= nearby * 28f

        // -----------------------------------------------------
        // 8. 饥饿
        // -----------------------------------------------------

        if (hunger > snake.size * 2) {

            s += if (foodDist >= 0) {
                100f / (foodDist + 1)
            } else {
                -20f
            }
        }

        val reason =
            when {

                danger >= 4 ->
                    "高危，优先保命"

                !tail ->
                    "尾巴不可达"

                trap >= 3 ->
                    "预测存在陷阱"

                sim.ate && tail ->
                    "吃食物后仍可逃生"

                foodDist >= 0 &&
                    foodDist <= 3 ->
                    "安全接近食物"

                mobility >= 3 ->
                    "扩大活动空间"

                else ->
                    "保持安全路线"
            }

        return Candidate(
            d,
            s,
            reason,
            true
        )
    }

    // =========================================================
    // BFS 策略
    // =========================================================

    private fun bfsChoose(
        legal: List<Candidate>
    ): Candidate? {

        val path =
            bfsPathToFood()

        if (path != null) {

            val candidate =
                legal.firstOrNull {
                    it.d == path
                }

            if (
                candidate != null &&
                isMoveVerySafe(path)
            ) {
                return candidate
            }
        }

        return legal.maxByOrNull {
            it.score
        }
    }

    // =========================================================
    // TAIL 策略
    // =========================================================

    private fun tailChoose(
        legal: List<Candidate>
    ): Candidate? {

        var best: Candidate? = null
        var bestScore = -1_000_000f

        for (candidate in legal) {

            val sim =
                simulate(candidate.d)

            if (sim.body.isEmpty()) {
                continue
            }

            val tail =
                tailReachable(sim.body)

            val region =
                freeRegion(sim.body)

            val mobility =
                countSafeMoves(sim.body)

            val foodDist =
                distance(
                    sim.body.first(),
                    food,
                    sim.body,
                    true
                )

            var s =
                candidate.score

            if (tail) {
                s += 650f
            } else {
                s -= 850f
            }

            s += region * 12f
            s += mobility * 35f

            if (foodDist >= 0) {

                s +=
                    50f /
                        (foodDist + 1)
            }

            if (s > bestScore) {
                bestScore = s
                best = candidate
            }
        }

        return best
            ?: legal.maxByOrNull {
                it.score
            }
    }

    // =========================================================
    // HAM
    // =========================================================

    private fun hamChoose(
        legal: List<Candidate>
    ): Candidate? {

        val safe =
            legal.filter {
                isMoveVerySafe(it.d)
            }

        if (safe.isEmpty()) {
            return legal.maxByOrNull {
                it.score
            }
        }

        val foodDist =
            distance(
                snake.first(),
                food,
                snake,
                true
            )

        if (
            foodDist in 0..2
        ) {

            val foodCandidate =
                safe.maxByOrNull {
                    if (
                        simulate(it.d).ate
                    ) {
                        it.score + 700f
                    } else {
                        it.score
                    }
                }

            if (foodCandidate != null) {
                return foodCandidate
            }
        }

        val currentIndex =
            hamIndexOf(snake.first())

        return safe.minByOrNull {

            val next =
                P(
                    snake.first().x +
                        it.d.x,
                    snake.first().y +
                        it.d.y
                )

            val target =
                hamIndexOf(next)

            val diff =
                (target - currentIndex + totalCells) %
                    totalCells

            if (diff == 0) {
                totalCells
            } else {
                diff
            }
        } ?: safe.maxByOrNull {
            it.score
        }
    }

    // =========================================================
    // BEAM SEARCH
    // =========================================================

    private fun beamBest(
        legal: List<Candidate>
    ): Candidate? {

        beamNodes = 0

        if (legal.isEmpty()) {
            return null
        }

        val maxDepth =
            when {

                snake.size < 20 -> 4
                snake.size < 50 -> 5
                else -> 6
            }

        var nodes =
            legal.mapNotNull {

                val sim =
                    simulate(it.d)

                if (sim.body.isEmpty()) {
                    null
                } else {

                    BeamNode(
                        cloneBody(sim.body),
                        it.d,
                        beamImmediateScore(
                            sim.body,
                            it.score,
                            sim.ate
                        ),
                        1
                    )
                }
            }

        beamNodes += nodes.size

        repeat(maxDepth - 1) {

            val next =
                ArrayList<BeamNode>()

            for (node in nodes) {

                val currentDir =
                    directionOfFirst(node.body)

                for (d in dirs) {

                    if (isReverse(d, currentDir)) {
                        continue
                    }

                    if (!canSim(node.body, d)) {
                        continue
                    }

                    val sim =
                        simulateOn(
                            node.body,
                            d
                        )

                    if (sim.body.isEmpty()) {
                        continue
                    }

                    val extra =
                        beamImmediateScore(
                            sim.body,
                            0f,
                            sim.ate
                        )

                    next.add(
                        BeamNode(
                            cloneBody(sim.body),
                            node.first,
                            node.score +
                                extra *
                                    depthWeight(
                                        node.depth + 1
                                    ),
                            node.depth + 1
                        )
                    )

                    beamNodes++

                    if (beamNodes > 500) {
                        break
                    }
                }

                if (beamNodes > 500) {
                    break
                }
            }

            if (next.isEmpty()) {
                return@repeat
            }

            next.sortByDescending {
                it.score
            }

            nodes =
                if (next.size > 10) {
                    ArrayList(next.take(10))
                } else {
                    next
                }
        }

        if (nodes.isEmpty()) {
            return legal.maxByOrNull {
                it.score
            }
        }

        val best =
            nodes.maxByOrNull {
                it.score
            } ?: return legal.maxByOrNull {
                it.score
            }

        return legal.firstOrNull {
            it.d == best.first
        } ?: legal.maxByOrNull {
            it.score
        }
    }

    private fun beamImmediateScore(
        body: ArrayDeque<P>,
        base: Float,
        ate: Boolean
    ): Float {

        val region =
            freeRegion(body)

        val mobility =
            countSafeMoves(body)

        val tail =
            tailReachable(body)

        val foodDist =
            distance(
                body.first(),
                food,
                body,
                true
            )

        val trap =
            trapRisk(body)

        var s = base

        s += region * 10f
        s += mobility * 30f

        if (tail) {
            s += 130f
        } else {
            s -= 240f
        }

        s -= trap * 90f

        if (foodDist >= 0) {
            s += 120f /
                (foodDist + 1)
        }

        if (ate) {
            s += 500f
        }

        return s
    }

    private fun depthWeight(
        depth: Int
    ): Float {

        return when (depth) {
            1 -> 1f
            2 -> 0.95f
            3 -> 0.85f
            4 -> 0.75f
            5 -> 0.65f
            else -> 0.55f
        }
    }

    // =========================================================
    // 策略选择
    // =========================================================

    private fun selectStrategy(
        state: Int,
        danger: Int
    ): Int {

        if (forcedStrategy >= 0) {
            return forcedStrategy
        }

        val len = snake.size

        // 极危险：不追食物
        if (danger >= 5) {
            return STRATEGY_TAIL
        }

        if (danger == 4) {
            return STRATEGY_TAIL
        }

        // 短蛇：安全情况下可以主动找食物
        if (len < 18) {

            return if (
                danger <= 2 &&
                distance(
                    snake.first(),
                    food,
                    snake,
                    true
                ) in 0..6
            ) {
                STRATEGY_BFS
            } else {
                STRATEGY_BEAM
            }
        }

        // 中期
        if (len < 45) {

            return when {
                danger >= 3 ->
                    STRATEGY_TAIL

                hunger > len * 2 ->
                    STRATEGY_BFS

                else ->
                    STRATEGY_BEAM
            }
        }

        // 长蛇
        return when {

            danger >= 3 ->
                STRATEGY_TAIL

            danger == 2 ->
                STRATEGY_BEAM

            else -> {

                val learned =
                    bestLearnedAction(state)

                if (
                    learned == STRATEGY_TAIL ||
                    learned == STRATEGY_BEAM
                ) {
                    learned
                } else {
                    STRATEGY_BEAM
                }
            }
        }
    }

    // =========================================================
    // 模拟
    // =========================================================

    private fun simulate(
        d: P
    ): Sim {

        return simulateOn(
            snake,
            d
        )
    }

    private fun simulateOn(
        source: ArrayDeque<P>,
        d: P
    ): Sim {

        if (source.isEmpty()) {
            return Sim(
                ArrayDeque(),
                false
            )
        }

        val result =
            cloneBody(source)

        val head =
            result.first()

        val nh =
            P(
                head.x + d.x,
                head.y + d.y
            )

        if (!inside(nh)) {
            return Sim(
                ArrayDeque(),
                false
            )
        }

        val willEat =
            nh == food

        val occupied =
            result.contains(nh)

        val tail =
            result.last()

        if (
            occupied &&
            !(nh == tail && !willEat)
        ) {
            return Sim(
                ArrayDeque(),
                false
            )
        }

        result.addFirst(nh)

        if (!willEat) {
            result.removeLast()
        }

        return Sim(
            result,
            willEat
        )
    }

    private fun cloneBody(
        source: ArrayDeque<P>
    ): ArrayDeque<P> {

        val copy =
            ArrayDeque<P>()

        for (p in source) {
            copy.add(p)
        }

        return copy
    }

    private fun canSim(
        body: ArrayDeque<P>,
        d: P
    ): Boolean {

        return simulateOn(
            body,
            d
        ).body.isNotEmpty()
    }

    private fun legalDirection(
        d: P
    ): Boolean {

        if (!inside(
                P(
                    snake.firstOrNull()?.x
                        ?: return false,
                    snake.firstOrNull()?.y
                        ?: return false
                )
            )
        ) {
            return false
        }

        val h =
            snake.first()

        val nh =
            P(
                h.x + d.x,
                h.y + d.y
            )

        if (!inside(nh)) {
            return false
        }

        if (isReverse(d, dir)) {
            return false
        }

        if (
            snake.contains(nh) &&
            nh != snake.last()
        ) {
            return false
        }

        return true
    }

    private fun isReverse(
        a: P,
        b: P
    ): Boolean {

        return a.x == -b.x &&
            a.y == -b.y
    }

    private fun directionOfFirst(
        body: ArrayDeque<P>
    ): P {

        if (body.size < 2) {
            return dir
        }

        return P(
            body.elementAt(0).x -
                body.elementAt(1).x,

            body.elementAt(0).y -
                body.elementAt(1).y
        )
    }

    // =========================================================
    // 空间搜索
    // =========================================================

    private fun inside(
        p: P
    ): Boolean {

        return p.x in 0 until cols &&
            p.y in 0 until rows
    }

    private fun indexOf(
        p: P
    ): Int {

        return p.y * cols + p.x
    }

    private fun freeRegion(
        body: ArrayDeque<P>
    ): Int {

        if (body.isEmpty()) {
            return 0
        }

        java.util.Arrays.fill(
            bfsVisited,
            false
        )

        val blocked =
            BooleanArray(totalCells)

        for (p in body) {

            if (!inside(p)) {
                continue
            }

            blocked[indexOf(p)] = true
        }

        val start =
            body.first()

        if (!inside(start)) {
            return 0
        }

        // 头部本身必须能够开始搜索
        blocked[indexOf(start)] = false

        var head = 0
        var tail = 0

        bfsQueue[tail++] =
            indexOf(start)

        bfsVisited[
            indexOf(start)
        ] = true

        var count = 0

        while (
            head < tail &&
            head < bfsQueue.size
        ) {

            val cur =
                bfsQueue[head++]

            if (
                cur < 0 ||
                cur >= totalCells
            ) {
                continue
            }

            count++

            val x =
                cur % cols

            val y =
                cur / cols

            fun add(
                next: Int
            ) {

                if (
                    next < 0 ||
                    next >= totalCells
                ) {
                    return
                }

                if (bfsVisited[next]) {
                    return
                }

                if (blocked[next]) {
                    return
                }

                // 关键：先判断容量，再写数组
                if (tail >= bfsQueue.size) {
                    return
                }

                bfsVisited[next] = true
                bfsQueue[tail++] = next
            }

            if (x > 0) {
                add(cur - 1)
            }

            if (x < cols - 1) {
                add(cur + 1)
            }

            if (y > 0) {
                add(cur - cols)
            }

            if (y < rows - 1) {
                add(cur + cols)
            }
        }

        return count
    }

    // =========================================================
    // BFS 食物路线
    // =========================================================

    private fun bfsPathToFood(): P? {

        if (snake.isEmpty()) {
            return null
        }

        val start =
            snake.first()

        if (start == food) {
            return null
        }

        if (!inside(start) || !inside(food)) {
            return null
        }

        java.util.Arrays.fill(
            bfsVisited,
            false
        )

        java.util.Arrays.fill(
            bfsParent,
            -1
        )

        val blocked =
            BooleanArray(totalCells)

        for (p in snake) {

            if (inside(p)) {
                blocked[indexOf(p)] = true
            }
        }

        // 尾巴下一步通常会移动，因此允许经过尾巴
        val tail =
            snake.last()

        if (inside(tail)) {
            blocked[indexOf(tail)] = false
        }

        val startIdx =
            indexOf(start)

        val targetIdx =
            indexOf(food)

        blocked[startIdx] = false

        var head = 0
        var tailIndex = 0

        bfsQueue[tailIndex++] =
            startIdx

        bfsVisited[startIdx] = true

        var found = false

        while (
            head < tailIndex &&
            head < bfsQueue.size
        ) {

            val cur =
                bfsQueue[head++]

            if (cur == targetIdx) {
                found = true
                break
            }

            val x =
                cur % cols

            val y =
                cur / cols

            fun add(
                next: Int
            ) {

                if (
                    next < 0 ||
                    next >= totalCells
                ) {
                    return
                }

                if (bfsVisited[next]) {
                    return
                }

                if (blocked[next]) {
                    return
                }

                if (
                    tailIndex >= bfsQueue.size
                ) {
                    return
                }

                bfsVisited[next] = true
                bfsParent[next] = cur
                bfsQueue[tailIndex++] = next
            }

            if (x > 0) {
                add(cur - 1)
            }

            if (x < cols - 1) {
                add(cur + 1)
            }

            if (y > 0) {
                add(cur - cols)
            }

            if (y < rows - 1) {
                add(cur + cols)
            }
        }

        if (!found) {
            return null
        }

        var cur = targetIdx

        while (
            bfsParent[cur] != -1 &&
            bfsParent[cur] != startIdx
        ) {
            cur = bfsParent[cur]
        }

        if (bfsParent[cur] == -1) {
            return null
        }

        val nx =
            cur % cols

        val ny =
            cur / cols

        return P(
            nx - start.x,
            ny - start.y
        )
    }

    // =========================================================
    // 距离
    // =========================================================

    private fun distance(
        start: P,
        target: P,
        body: Collection<P>,
        allowTail: Boolean
    ): Int {

        if (!inside(start) || !inside(target)) {
            return -1
        }

        if (start == target) {
            return 0
        }

        java.util.Arrays.fill(
            bfsVisited,
            false
        )

        val blocked =
            BooleanArray(totalCells)

        for (p in body) {

            if (inside(p)) {
                blocked[indexOf(p)] = true
            }
        }

        if (
            allowTail &&
            body.isNotEmpty()
        ) {

            val last =
                body.last()

            if (inside(last)) {
                blocked[indexOf(last)] = false
            }
        }

        val startIdx =
            indexOf(start)

        blocked[startIdx] = false

        var head = 0
        var tail = 0

        bfsQueue[tail++] =
            startIdx

        bfsVisited[startIdx] = true

        var distance = 0

        while (
            head < tail &&
            head < bfsQueue.size
        ) {

            val layerEnd = tail

            while (
                head < layerEnd
            ) {

                val cur =
                    bfsQueue[head++]

                if (cur == indexOf(target)) {
                    return distance
                }

                val x =
                    cur % cols

                val y =
                    cur / cols

                fun add(
                    next: Int
                ) {

                    if (
                        next < 0 ||
                        next >= totalCells
                    ) {
                        return
                    }

                    if (bfsVisited[next]) {
                        return
                    }

                    if (blocked[next]) {
                        return
                    }

                    if (
                        tail >= bfsQueue.size
                    ) {
                        return
                    }

                    bfsVisited[next] = true
                    bfsQueue[tail++] = next
                }

                if (x > 0) {
                    add(cur - 1)
                }

                if (x < cols - 1) {
                    add(cur + 1)
                }

                if (y > 0) {
                    add(cur - cols)
                }

                if (y < rows - 1) {
                    add(cur + cols)
                }
            }

            distance++
        }

        return -1
    }

    // =========================================================
    // 安全判断
    // =========================================================

    private fun isMoveSafe(
        d: P
    ): Boolean {

        val sim =
            simulate(d)

        if (sim.body.isEmpty()) {
            return false
        }

        val body =
            sim.body

        val region =
            freeRegion(body)

        val tail =
            tailReachable(body)

        val mobility =
            countSafeMoves(body)

        val trap =
            trapRisk(body)

        val need =
            when {

                body.size < 15 ->
                    max(
                        7,
                        body.size * 3 / 4
                    )

                body.size < 40 ->
                    max(
                        10,
                        body.size * 2 / 3
                    )

                else ->
                    max(
                        14,
                        body.size / 2
                    )
            }

        return region >= need &&
            mobility >= 1 &&
            tail &&
            trap <= 2
    }

    private fun isMoveVerySafe(
        d: P
    ): Boolean {

        val sim =
            simulate(d)

        if (sim.body.isEmpty()) {
            return false
        }

        val body =
            sim.body

        val region =
            freeRegion(body)

        val ratio =
            region.toFloat() /
                max(1, body.size)

        val mobility =
            countSafeMoves(body)

        val tail =
            tailReachable(body)

        val trap =
            trapRisk(body)

        return tail &&
            mobility >= 1 &&
            ratio >= 1.35f &&
            trap <= 1
    }

    private fun countSafeMoves(
        body: ArrayDeque<P>
    ): Int {

        if (body.isEmpty()) {
            return 0
        }

        val h =
            body.first()

        val currentDir =
            directionOfFirst(body)

        var count = 0

        for (d in dirs) {

            if (isReverse(d, currentDir)) {
                continue
            }

            val nh =
                P(
                    h.x + d.x,
                    h.y + d.y
                )

            if (!inside(nh)) {
                continue
            }

            val hits =
                body.contains(nh)

            if (
                hits &&
                nh != body.last()
            ) {
                continue
            }

            val sim =
                simulateOn(
                    body,
                    d
                )

            if (sim.body.isEmpty()) {
                continue
            }

            val region =
                freeRegion(sim.body)

            if (
                region >=
                max(
                    4,
                    sim.body.size / 3
                )
            ) {
                count++
            }
        }

        return count
    }

    private fun tailReachable(
        body: ArrayDeque<P>
    ): Boolean {

        if (body.isEmpty()) {
            return false
        }

        if (body.size == 1) {
            return true
        }

        return distance(
            body.first(),
            body.last(),
            body,
            true
        ) >= 0
    }

    // =========================================================
    // 未来危险 / 陷阱
    // =========================================================

    private fun futureDanger(
        body: ArrayDeque<P>
    ): Int {

        if (body.isEmpty()) {
            return 5
        }

        val mobility =
            countSafeMoves(body)

        val region =
            freeRegion(body)

        val ratio =
            region.toFloat() /
                max(1, body.size)

        val tail =
            tailReachable(body)

        return when {

            mobility == 0 ->
                5

            !tail && body.size > 5 ->
                5

            ratio < 1.25f ->
                5

            ratio < 1.7f ->
                4

            ratio < 2.5f ->
                3

            ratio < 3.8f ->
                2

            else ->
                1
        }
    }

    private fun trapRisk(
        body: ArrayDeque<P>
    ): Int {

        if (body.isEmpty()) {
            return 5
        }

        val head =
            body.first()

        var risk = 0

        for (d in dirs) {

            val nh =
                P(
                    head.x + d.x,
                    head.y + d.y
                )

            if (!inside(nh)) {
                risk++
                continue
            }

            if (
                body.contains(nh) &&
                nh != body.last()
            ) {
                risk++
                continue
            }

            val sim =
                simulateOn(
                    body,
                    d
                )

            if (sim.body.isEmpty()) {
                risk++
                continue
            }

            val mobility =
                countSafeMoves(sim.body)

            val region =
                freeRegion(sim.body)

            if (mobility <= 1) {
                risk++
            }

            if (
                region <
                max(
                    5,
                    sim.body.size / 2
                )
            ) {
                risk++
            }
        }

        return risk.coerceIn(0, 5)
    }

    private fun calculateDanger(): Int {

        return futureDanger(snake)
    }

    private fun edgeDistance(
        p: P
    ): Int {

        return min(
            min(
                p.x,
                cols - 1 - p.x
            ),
            min(
                p.y,
                rows - 1 - p.y
            )
        )
    }

    // =========================================================
    // HAM 坐标
    // =========================================================

    private fun hamIndexOf(
        p: P
    ): Int {

        return if (p.x % 2 == 0) {

            p.x * rows + p.y

        } else {

            p.x * rows +
                (rows - 1 - p.y)
        }
    }

    // =========================================================
    // 食物
    // =========================================================

    private fun placeFood() {

        val free =
            ArrayList<P>()

        for (x in 0 until cols) {

            for (y in 0 until rows) {

                val p =
                    P(x, y)

                if (!snake.contains(p)) {
                    free.add(p)
                }
            }
        }

        if (free.isNotEmpty()) {

            food =
                free[
                    Random.nextInt(
                        free.size
                    )
                ]
        }
    }

    // =========================================================
    // 学习
    // =========================================================

    private fun learnState(
        len: Int,
        danger: Int
    ): Int {

        val stage =
            when {

                len < 20 -> 0
                len < 40 -> 1
                len < 70 -> 2
                else -> 3
            }

        return (
            stage * 5 +
                (danger - 1).coerceIn(0, 4)
            ).coerceIn(0, 19)
    }

    private fun learn(
        reward: Float
    ) {

        if (
            lastState !in q.indices ||
            lastAction !in q[0].indices
        ) {
            return
        }

        val visits =
            n[lastState][lastAction]++

        val alpha =
            when {

                visits < 10 -> 0.20f
                visits < 40 -> 0.10f
                else -> 0.04f
            }

        q[lastState][lastAction] +=
            alpha * (
                reward -
                    q[lastState][lastAction]
                )

        saveCounter++

        if (saveCounter >= 20) {

            saveCounter = 0
            saveLearning()
        }
    }

    private fun bestLearnedAction(
        state: Int
    ): Int {

        if (
            state !in q.indices
        ) {
            return STRATEGY_BEAM
        }

        var best = 0
        var bestValue =
            Float.NEGATIVE_INFINITY

        for (a in 0..3) {

            if (
                q[state][a] >
                bestValue
            ) {
                bestValue =
                    q[state][a]
                best = a
            }
        }

        return best
    }

    // =========================================================
    // 死亡
    // =========================================================

    private fun die(
        cause: String
    ) {

        if (gameOver) {
            return
        }

        gameOver = true
        running = false

        deathCause = cause

        totalGames++

        lastDeathInfo =
            "$cause  |  长度 ${snake.size}  |  分数 $score"

        learn(-3f)

        when (cause) {

            "撞墙" ->
                aggression -= 0.02f

            "撞到自己" ->
                safetyMargin += 0.015f

            "进入死区" -> {
                safetyMargin += 0.025f
                aggression -= 0.015f
            }
        }

        aggression =
            aggression.coerceIn(
                0.8f,
                1.35f
            )

        safetyMargin =
            safetyMargin.coerceIn(
                1.03f,
                1.28f
            )

        saveLearning()

        flash = 0.65f
        shakeAmp = 14f

        try {

            if (Build.VERSION.SDK_INT >=
                Build.VERSION_CODES.O
            ) {

                vibrator?.vibrate(
                    VibrationEffect.createOneShot(
                        120,
                        VibrationEffect.DEFAULT_AMPLITUDE
                    )
                )

            } else {

                @Suppress("DEPRECATION")
                vibrator?.vibrate(120)
            }

        } catch (_: Exception) {
        }

        invalidate()
    }

    // =========================================================
    // AI 说明
    // =========================================================

    private fun reasonFor(
        candidate: Candidate,
        strategy: Int,
        danger: Int
    ): String {

        if (danger >= 5) {
            return "极危险，寻找最大逃生空间"
        }

        if (danger == 4) {
            return "危险较高，保持尾巴可达"
        }

        return when {

            candidate.reason.isNotEmpty() ->
                candidate.reason

            strategy == STRATEGY_BFS ->
                "安全情况下寻找食物"

            strategy == STRATEGY_TAIL ->
                "跟随尾巴维持生存空间"

            strategy == STRATEGY_HAM ->
                "保持稳定巡航路线"

            else ->
                "多步预测最佳路线"
        }
    }

    private fun strategyName(
        strategy: Int
    ): String {

        return when (strategy) {

            STRATEGY_BFS ->
                "BFS"

            STRATEGY_TAIL ->
                "TAIL"

            STRATEGY_HAM ->
                "HAM"

            STRATEGY_BEAM ->
                "BEAM"

            else ->
                "AUTO"
        }
    }

    // =========================================================
    // 特效
    // =========================================================

    private fun spawnFoodEffect(
        p: P,
        gained: Int,
        mul: Float
    ) {

        val count =
            (
                14 +
                    min(
                        20,
                        (mul * 6).toInt()
                    )
                ).coerceAtMost(40)

        repeat(count) {

            particles.add(
                Particle(
                    p.x.toFloat(),
                    p.y.toFloat(),
                    Random.nextFloat() - 0.5f,
                    Random.nextFloat() - 0.5f,
                    1f,
                    Color.YELLOW
                )
            )
        }

        floats.add(
            FloatText(
                p.x.toFloat(),
                p.y.toFloat(),
                1f,
                "+$gained"
            )
        )

        ripples.add(
            Ripple(
                p.x.toFloat(),
                p.y.toFloat(),
                1f
            )
        )
    }

    private fun updateEffects(
        dt: Float
    ) {

        globalTime +=
            dt * 0.016f

        foodPhase =
            (
                foodPhase +
                    dt * 0.03f
                ) % 1f

        flash =
            max(
                0f,
                flash - dt * 0.05f
            )

        if (shakeAmp > 0.01f) {

            shakeX =
                (
                    Random.nextFloat() - 0.5f
                    ) *
                    shakeAmp *
                    2f

            shakeY =
                (
                    Random.nextFloat() - 0.5f
                    ) *
                    shakeAmp *
                    2f

            shakeAmp *=
                (
                    1f -
                        0.15f * dt
                    ).coerceIn(
                        0.7f,
                        0.98f
                    )

        } else {

            shakeAmp = 0f
            shakeX = 0f
            shakeY = 0f
        }

        particles.forEach {

            it.x +=
                it.vx *
                    dt *
                    0.15f

            it.y +=
                it.vy *
                    dt *
                    0.15f

            it.vx *=
                (
                    1f -
                        0.06f * dt
                    ).coerceIn(
                        0.5f,
                        1f
                    )

            it.vy *=
                (
                    1f -
                        0.06f * dt
                    ).coerceIn(
                        0.5f,
                        1f
                    )

            it.life -=
                dt * 0.03f
        }

        particles.removeAll {
            it.life <= 0f
        }

        floats.forEach {

            it.y -=
                dt * 0.04f

            it.life -=
                dt * 0.02f
        }

        floats.removeAll {
            it.life <= 0f
        }

        ripples.forEach {
            it.life -=
                dt * 0.03f
        }

        ripples.removeAll {
            it.life <= 0f
        }
    }

    // =========================================================
    // 尺寸
    // =========================================================

    override fun onSizeChanged(
        w: Int,
        h: Int,
        oldw: Int,
        oldh: Int
    ) {

        cell =
            min(
                w.toFloat() / cols,
                h.toFloat() / rows
            )

        ox =
            (w - cols * cell) /
                2f

        oy =
            (h - rows * cell) /
                2f

        invalidate()
    }

    // =========================================================
    // 绘制
    // =========================================================

    override fun onDraw(
        c: Canvas
    ) {

        super.onDraw(c)

        c.drawColor(bgColor)

        drawBackgroundGlow(c)

        c.save()

        if (
            shakeX != 0f ||
            shakeY != 0f
        ) {
            c.translate(
                shakeX,
                shakeY
            )
        }

        drawGrid(c)
        drawFood(c)
        drawSnake(c)
        drawParticles(c)
        drawRipples(c)
        drawFloats(c)

        c.restore()

        drawMultiplierHud(c)

        if (
            aiMode != 0 ||
            gameOver
        ) {
            drawDebug(c)
        }

        if (gameOver) {
            drawGameOver(c)
        }

        if (flash > 0.001f) {

            paint.color =
                Color.argb(
                    (
                        flash * 140
                        ).toInt().coerceIn(
                            0,
                            255
                        ),
                    255,
                    40,
                    40
                )

            c.drawRect(
                0f,
                0f,
                width.toFloat(),
                height.toFloat(),
                paint
            )
        }
    }

    private fun drawBackgroundGlow(
        c: Canvas
    ) {

        val w =
            width.toFloat()

        val h =
            height.toFloat()

        val r =
            max(w, h) * 0.7f

        val pulse =
            0.85f +
                0.15f *
                sin(
                    globalTime * 0.7f
                )

        bgPaint.shader =
            RadialGradient(
                w / 2f,
                h / 2f,
                r * pulse,
                intArrayOf(
                    Color.argb(
                        60,
                        Color.red(gridColor),
                        Color.green(gridColor),
                        Color.blue(gridColor)
                    ),
                    Color.argb(
                        0,
                        0,
                        0,
                        0
                    )
                ),
                floatArrayOf(
                    0f,
                    1f
                ),
                Shader.TileMode.CLAMP
            )

        c.drawRect(
            0f,
            0f,
            w,
            h,
            bgPaint
        )

        bgPaint.shader = null
    }

    private fun drawGrid(
        c: Canvas
    ) {

        val breathe =
            (
                60 +
                    40 *
                    sin(
                        globalTime * 1.4f
                    )
                ).toInt().coerceIn(
                    0,
                    100
                )

        gridPaint.color =
            Color.argb(
                breathe.coerceIn(
                    30,
                    140
                ),
                Color.red(gridColor),
                Color.green(gridColor),
                Color.blue(gridColor)
            )

        gridPaint.style =
            Paint.Style.STROKE

        gridPaint.strokeWidth = 1f

        for (i in 0..cols) {

            c.drawLine(
                ox + i * cell,
                oy,
                ox + i * cell,
                oy + rows * cell,
                gridPaint
            )
        }

        for (i in 0..rows) {

            c.drawLine(
                ox,
                oy + i * cell,
                ox + cols * cell,
                oy + i * cell,
                gridPaint
            )
        }
    }

    private fun drawFood(
        c: Canvas
    ) {

        val cx =
            ox +
                (food.x + 0.5f) *
                cell

        val cy =
            oy +
                (food.y + 0.5f) *
                cell

        val pulse =
            1f +
                0.18f *
                sin(
                    foodPhase *
                        2f *
                        Math.PI.toFloat()
                )

        val baseR =
            cell * 0.22f *
                pulse

        foodPaint.shader =
            RadialGradient(
                cx,
                cy,
                cell * 0.55f,
                intArrayOf(
                    Color.argb(
                        140,
                        255,
                        90,
                        90
                    ),
                    Color.argb(
                        0,
                        255,
                        90,
                        90
                    )
                ),
                floatArrayOf(
                    0f,
                    1f
                ),
                Shader.TileMode.CLAMP
            )

        c.drawCircle(
            cx,
            cy,
            cell * 0.55f,
            foodPaint
        )

        foodPaint.shader = null

        foodPaint.color =
            Color.argb(
                90,
                255,
                200,
                120
            )

        val rot =
            globalTime * 90f

        c.save()

        c.rotate(
            rot,
            cx,
            cy
        )

        val rect =
            RectF(
                cx - cell * 0.42f,
                cy - cell * 0.42f,
                cx + cell * 0.42f,
                cy + cell * 0.42f
            )

        c.drawArc(
            rect,
            0f,
            40f,
            true,
            foodPaint
        )

        c.drawArc(
            rect,
            180f,
            40f,
            true,
            foodPaint
        )

        c.restore()

        foodPaint.color =
            Color.RED

        c.drawCircle(
            cx,
            cy,
            baseR,
            foodPaint
        )

        foodPaint.color =
            Color.WHITE

        c.drawCircle(
            cx - baseR * 0.35f,
            cy - baseR * 0.35f,
            baseR * 0.35f,
            foodPaint
        )
    }

    private fun ensurePts(
        n: Int
    ) {

        val need =
            n * 2

        if (ptsBuf.size < need) {
            ptsBuf =
                FloatArray(
                    need * 2
                )
        }
    }

    private fun drawSnake(
        c: Canvas
    ) {

        if (snake.isEmpty()) {
            return
        }

        val prev =
            if (prevSnake.isEmpty()) {
                snake.toList()
            } else {
                prevSnake
            }

        val curr =
            snake.toList()

        val nCount =
            curr.size

        val t =
            if (gameOver) {
                1f
            } else {
                moveProgress
            }

        ensurePts(nCount)

        for (i in 0 until nCount) {

            val a =
                if (i < prev.size) {
                    prev[i]
                } else {
                    prev.last()
                }

            val b =
                curr[i]

            ptsBuf[i * 2] =
                a.x +
                    (b.x - a.x) * t

            ptsBuf[i * 2 + 1] =
                a.y +
                    (b.y - a.y) * t
        }

        val sub =
            when {

                nCount < 30 -> 4
                nCount < 70 -> 3
                else -> 2
            }

        for (
            i in nCount - 1 downTo 1
        ) {

            val x0 =
                ptsBuf[i * 2]

            val y0 =
                ptsBuf[i * 2 + 1]

            val x1 =
                ptsBuf[(i - 1) * 2]

            val y1 =
                ptsBuf[(i - 1) * 2 + 1]

            for (
                s in sub - 1 downTo 0
            ) {

                val k =
                    s / sub.toFloat()

                val px =
                    x0 +
                        (x1 - x0) * k

                val py =
                    y0 +
                        (y1 - y0) * k

                val frac =
                    (i + k) /
                        (nCount - 1f)
                            .coerceAtLeast(
                                1f
                            )

                val r =
                    cell *
                        (
                            0.44f -
                                0.22f *
                                frac
                            )

                snakePaint.color =
                    if (rainbowSkin) {

                        val hue =
                            (
                                i * 8 +
                                    globalTime *
                                    140f +
                                    score
                                ) % 360f

                        hsv[
                            (
                                hue.toInt() %
                                    360 +
                                    360
                                ) % 360
                        ]

                    } else {

                        blendColor(
                            bodyColor,
                            headColor,
                            (1f - frac) *
                                0.5f
                        )
                    }

                c.drawCircle(
                    ox +
                        (px + 0.5f) *
                        cell,
                    oy +
                        (py + 0.5f) *
                        cell,
                    r,
                    snakePaint
                )
            }
        }

        val hx =
            ptsBuf[0]

        val hy =
            ptsBuf[1]

        val hcx =
            ox +
                (hx + 0.5f) *
                cell

        val hcy =
            oy +
                (hy + 0.5f) *
                cell

        val dirX: Float
        val dirY: Float

        if (nCount >= 2) {

            dirX =
                hx -
                    ptsBuf[2]

            dirY =
                hy -
                    ptsBuf[3]

        } else {

            dirX =
                dir.x.toFloat()

            dirY =
                dir.y.toFloat()
        }

        val dl =
            max(
                0.0001f,
                kotlin.math.sqrt(
                    dirX * dirX +
                        dirY * dirY
                )
            )

        val ndx =
            dirX / dl

        val ndy =
            dirY / dl

        glowPaint.shader =
            RadialGradient(
                hcx,
                hcy,
                cell * 0.75f,
                intArrayOf(
                    Color.argb(
                        110,
                        Color.red(headColor),
                        Color.green(headColor),
                        Color.blue(headColor)
                    ),
                    Color.argb(
                        0,
                        Color.red(headColor),
                        Color.green(headColor),
                        Color.blue(headColor)
                    )
                ),
                floatArrayOf(
                    0f,
                    1f
                ),
                Shader.TileMode.CLAMP
            )

        c.drawCircle(
            hcx,
            hcy,
            cell * 0.75f,
            glowPaint
        )

        glowPaint.shader = null

        headPaint.color =
            if (rainbowSkin) {

                hsv[
                    (
                        globalTime *
                            90f
                    ).toInt() %
                        360
                ]

            } else {
                headColor
            }

        c.drawCircle(
            hcx,
            hcy,
            cell * 0.46f,
            headPaint
        )

        val ex =
            -ndy

        val ey =
            ndx

        val eyeOffset =
            cell * 0.16f

        val eyeForward =
            cell * 0.12f

        val eyeR =
            cell * 0.085f

        val e1x =
            hcx +
                ex * eyeOffset +
                ndx * eyeForward

        val e1y =
            hcy +
                ey * eyeOffset +
                ndy * eyeForward

        val e2x =
            hcx -
                ex * eyeOffset +
                ndx * eyeForward

        val e2y =
            hcy -
                ey * eyeOffset +
                ndy * eyeForward

        paint.color =
            Color.WHITE

        c.drawCircle(
            e1x,
            e1y,
            eyeR,
            paint
        )

        c.drawCircle(
            e2x,
            e2y,
            eyeR,
            paint
        )

        val fdx =
            (food.x + 0.5f) -
                hx

        val fdy =
            (food.y + 0.5f) -
                hy

        val fl =
            max(
                0.0001f,
                kotlin.math.sqrt(
                    fdx * fdx +
                        fdy * fdy
                )
            )

        val pdx =
            fdx / fl

        val pdy =
            fdy / fl

        val pupilR =
            eyeR * 0.55f

        paint.color =
            Color.BLACK

        c.drawCircle(
            e1x +
                pdx *
                eyeR *
                0.35f,
            e1y +
                pdy *
                eyeR *
                0.35f,
            pupilR,
            paint
        )

        c.drawCircle(
            e2x +
                pdx *
                eyeR *
                0.35f,
            e2y +
                pdy *
                eyeR *
                0.35f,
            pupilR,
            paint
        )
    }

    private fun blendColor(
        c1: Int,
        c2: Int,
        f: Float
    ): Int {

        val g =
            f.coerceIn(
                0f,
                1f
            )

        val a =
            (
                Color.alpha(c1) +
                    (
                        Color.alpha(c2) -
                            Color.alpha(c1)
                        ) * g
                ).toInt()

        val r =
            (
                Color.red(c1) +
                    (
                        Color.red(c2) -
                            Color.red(c1)
                        ) * g
                ).toInt()

        val gg =
            (
                Color.green(c1) +
                    (
                        Color.green(c2) -
                            Color.green(c1)
                        ) * g
                ).toInt()

        val b =
            (
                Color.blue(c1) +
                    (
                        Color.blue(c2) -
                            Color.blue(c1)
                        ) * g
                ).toInt()

        return Color.argb(
            a,
            r,
            gg,
            b
        )
    }

    private fun drawParticles(
        c: Canvas
    ) {

        particles.forEach {

            val alpha =
                (
                    it.life * 255
                    ).toInt().coerceIn(
                        0,
                        255
                    )

            paint.color =
                Color.argb(
                    alpha,
                    Color.red(it.color),
                    Color.green(it.color),
                    Color.blue(it.color)
                )

            c.drawCircle(
                ox +
                    (it.x + 0.5f) *
                    cell,
                oy +
                    (it.y + 0.5f) *
                    cell,
                max(
                    2f,
                    cell * 0.05f
                ),
                paint
            )
        }
    }

    private fun drawRipples(
        c: Canvas
    ) {

        if (ripples.isEmpty()) {
            return
        }

        paint.style =
            Paint.Style.STROKE

        paint.strokeWidth =
            max(
                2f,
                cell * 0.06f
            )

        ripples.forEach {

            val frac =
                1f - it.life

            val r =
                cell *
                    (
                        0.2f +
                            frac * 1.1f
                        )

            val alpha =
                (
                    it.life * 200
                    ).toInt().coerceIn(
                        0,
                        255
                    )

            paint.color =
                Color.argb(
                    alpha,
                    255,
                    220,
                    80
                )

            c.drawCircle(
                ox +
                    (it.x + 0.5f) *
                    cell,
                oy +
                    (it.y + 0.5f) *
                    cell,
                r,
                paint
            )
        }

        paint.style =
            Paint.Style.FILL
    }

    private fun drawFloats(
        c: Canvas
    ) {

        if (floats.isEmpty()) {
            return
        }

        text.textAlign =
            Paint.Align.CENTER

        text.isFakeBoldText = true

        text.textSize =
            cell * 0.32f

        floats.forEach {

            text.color =
                Color.argb(
                    (
                        it.life * 255
                        ).toInt().coerceIn(
                            0,
                            255
                        ),
                    255,
                    215,
                    0
                )

            c.drawText(
                it.text,
                ox +
                    (it.x + 0.5f) *
                    cell,
                oy +
                    (it.y + 0.3f) *
                    cell,
                text
            )
        }

        text.isFakeBoldText = false
    }

    // =========================================================
    // 倍率 HUD
    // =========================================================

    private fun drawMultiplierHud(
        c: Canvas
    ) {

        if (
            aiMode == 0 &&
            !gameOver
        ) {
            return
        }

        val mul =
            computeScoreMultiplier()

        text.textAlign =
            Paint.Align.RIGHT

        text.isFakeBoldText = true

        text.textSize =
            cell * 0.55f

        text.color =
            when {

                mul < 1.5f ->
                    Color.LTGRAY

                mul < 2.5f ->
                    Color.CYAN

                mul < 3.5f ->
                    Color.YELLOW

                mul < 5f ->
                    Color.rgb(
                        255,
                        150,
                        0
                    )

                else ->
                    Color.RED
            }

        c.drawText(
            "×${"%.1f".format(mul)}",
            width - 24f,
            oy + cell * 0.9f,
            text
        )

        text.isFakeBoldText = false
    }

    // =========================================================
    // 调试面板
    // =========================================================

    private fun drawDebug(
        c: Canvas
    ) {

        if (
            aiMode == 0 &&
            !gameOver
        ) {
            return
        }

        val w =
            min(
                width * 0.97f,
                620f
            )

        val h = 300f

        val left =
            (width - w) / 2f

        val top =
            if (gameOver) {
                max(
                    12f,
                    height - h - 12f
                )
            } else {
                12f
            }

        panel.color =
            Color.argb(
                220,
                0,
                0,
                0
            )

        c.drawRoundRect(
            left,
            top,
            left + w,
            top + h,
            22f,
            22f,
            panel
        )

        border.color =
            when (ai.danger) {

                1 ->
                    Color.GREEN

                2 ->
                    Color.rgb(
                        150,
                        255,
                        80
                    )

                3 ->
                    Color.YELLOW

                4 ->
                    Color.rgb(
                        255,
                        150,
                        0
                    )

                else ->
                    Color.RED
            }

        border.style =
            Paint.Style.STROKE

        border.strokeWidth = 4f

        c.drawRoundRect(
            left,
            top,
            left + w,
            top + h,
            22f,
            22f,
            border
        )

        text.textAlign =
            Paint.Align.LEFT

        text.isFakeBoldText = true

        text.textSize = 20f
        text.color = Color.WHITE

        c.drawText(
            "🧠 AI  ${ai.strategy}",
            left + 16f,
            top + 30f,
            text
        )

        text.isFakeBoldText = false
        text.textSize = 14f
        text.color = Color.YELLOW

        c.drawText(
            "正在判断：${ai.reason}",
            left + 16f,
            top + 54f,
            text
        )

        text.color =
            Color.WHITE

        val dangerText =
            "危险 " +
                "●".repeat(
                    ai.danger
                ) +
                "○".repeat(
                    5 - ai.danger
                )

        c.drawText(
            dangerText,
            left + 16f,
            top + 78f,
            text
        )

        c.drawText(
            "空间 ${ai.region}",
            left + 180f,
            top + 78f,
            text
        )

        c.drawText(
            "比例 ${"%.1f".format(ai.spaceRatio)}",
            left + 310f,
            top + 78f,
            text
        )

        val tailText =
            if (ai.tailReachable)
                "✓ 可达"
            else
                "✗ 不可达"

        val foodText =
            if (ai.foodReachable)
                "✓ 可达"
            else
                "✗ 不可达"

        val foodDistanceText =
            if (ai.foodDistance < 0)
                "∞"
            else
                ai.foodDistance.toString()

        c.drawText(
            "尾巴 $tailText",
            left + 16f,
            top + 102f,
            text
        )

        c.drawText(
            "食物 $foodText",
            left + 180f,
            top + 102f,
            text
        )

        c.drawText(
            "距离 $foodDistanceText",
            left + 340f,
            top + 102f,
            text
        )

        c.drawText(
            "长度 ${snake.size}",
            left + 16f,
            top + 126f,
            text
        )

        c.drawText(
            "饥饿 $hunger",
            left + 160f,
            top + 126f,
            text
        )

        c.drawText(
            "分数 $score",
            left + 290f,
            top + 126f,
            text
        )

        c.drawText(
            "学习局数 $totalGames",
            left + 410f,
            top + 126f,
            text
        )

        c.drawText(
            "探索深度 ${ai.depth}",
            left + 16f,
            top + 150f,
            text
        )

        c.drawText(
            "节点 ${ai.nodes}",
            left + 180f,
            top + 150f,
            text
        )

        c.drawText(
            "攻击 ${"%.2f".format(aggression)}",
            left + 310f,
            top + 150f,
            text
        )

        val mulNow =
            computeScoreMultiplier()

        val stage =
            computeStage()

        text.color =
            when {

                mulNow < 1.5f ->
                    Color.LTGRAY

                mulNow < 2.5f ->
                    Color.CYAN

                mulNow < 3.5f ->
                    Color.YELLOW

                mulNow < 5f ->
                    Color.rgb(
                        255,
                        150,
                        0
                    )

                else ->
                    Color.RED
            }

        c.drawText(
            "倍率 ×${"%.1f".format(mulNow)}",
            left + 16f,
            top + 172f,
            text
        )

        text.color =
            Color.WHITE

        c.drawText(
            "速度 ${gameSpeed}ms",
            left + 180f,
            top + 172f,
            text
        )

        c.drawText(
            "阶段 ${stage + 1}/11",
            left + 310f,
            top + 172f,
            text
        )

        text.textSize = 13f

        var x =
            left + 16f

        ai.candidates.forEach {

            val label =
                when (it.d) {

                    P(0, -1) -> "↑"
                    P(0, 1) -> "↓"
                    P(-1, 0) -> "←"

                    else -> "→"
                }

            text.color =
                if (it.legal)
                    Color.WHITE
                else
                    Color.GRAY

            c.drawText(
                "$label ${"%.0f".format(it.score)}",
                x,
                top + 196f,
                text
            )

            x +=
                w / 4f
        }

        text.textSize = 14f
        text.color =
            Color.CYAN

        c.drawText(
            "选择 ${arrow(ai.chosen)}",
            left + 16f,
            top + 224f,
            text
        )

        text.color =
            Color.LTGRAY

        c.drawText(
            "死亡统计  W$deathWall  S$deathSelf  T$deathTrap",
            left + 150f,
            top + 224f,
            text
        )

        text.textSize = 12f
        text.color =
            Color.rgb(
                180,
                220,
                255
            )

        c.drawText(
            "安全空间 + 尾巴可达 + 陷阱预测 + BEAM 多步搜索",
            left + 16f,
            top + 248f,
            text
        )

        if (gameOver) {

            text.color =
                Color.RED

            text.isFakeBoldText =
                true

            text.textSize =
                17f

            c.drawText(
                "死亡原因：$deathCause",
                left + 16f,
                top + 276f,
                text
            )

            text.isFakeBoldText =
                false
        }
    }

    // =========================================================
    // GAME OVER
    // =========================================================

    private fun drawGameOver(
        c: Canvas
    ) {

        paint.color =
            Color.argb(
                150,
                0,
                0,
                0
            )

        c.drawRect(
            0f,
            0f,
            width.toFloat(),
            height.toFloat(),
            paint
        )

        text.textAlign =
            Paint.Align.CENTER

        text.isFakeBoldText = true
        text.textSize = 30f
        text.color = Color.WHITE

        c.drawText(
            "GAME OVER",
            width / 2f,
            height / 2f - 45,
            text
        )

        text.textSize = 15f
        text.isFakeBoldText = false

        c.drawText(
            "分数 $score   最高 $highScore   长度 ${snake.size}",
            width / 2f,
            height / 2f - 15,
            text
        )

        text.color =
            Color.YELLOW

        c.drawText(
            "点击屏幕重新开始",
            width / 2f,
            height / 2f + 20,
            text
        )

        text.color =
            Color.LTGRAY

        text.textSize = 11f

        c.drawText(
            lastDeathInfo,
            width / 2f,
            height / 2f + 48,
            text
        )
    }

    private fun arrow(
        p: P
    ): String {

        return when (p) {

            P(0, -1) -> "↑"
            P(0, 1) -> "↓"
            P(-1, 0) -> "←"
            P(1, 0) -> "→"

            else -> "·"
        }
    }

    // =========================================================
    // 触摸
    // =========================================================

    override fun onTouchEvent(
        e: MotionEvent
    ): Boolean {

        if (
            e.action !=
            MotionEvent.ACTION_UP
        ) {
            return true
        }

        if (gameOver) {

            reset()

            if (!running) {
                resume()
            }

            return true
        }

        if (aiMode != 0) {
            return true
        }

        if (snake.isEmpty()) {
            return true
        }

        val dx =
            e.x -
                (
                    ox +
                        (snake.first().x + 0.5f) *
                        cell
                    )

        val dy =
            e.y -
                (
                    oy +
                        (snake.first().y + 0.5f) *
                        cell
                    )

        val d =
            if (abs(dx) > abs(dy)) {

                P(
                    if (dx > 0)
                        1
                    else
                        -1,
                    0
                )

            } else {

                P(
                    0,
                    if (dy > 0)
                        1
                    else
                        -1
                )
            }

        if (!isReverse(d, dir)) {
            queue.add(d)
        }

        return true
    }
}
