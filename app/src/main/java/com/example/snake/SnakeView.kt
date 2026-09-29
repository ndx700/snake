package com.example.snake

import android.app.Activity
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
) : View(
    context,
    attrs
) {

    // =========================================================
    // 网格
    // =========================================================
    private val cols = 15
    private val rows = 15

    private var cell = 0f
    private var ox = 0f
    private var oy = 0f

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
        var chosen: P = P(0, 0),
        var candidates: List<Candidate> = emptyList(),
        var depth: Int = 0,
        var nodes: Int = 0
    )

    private data class Sim(
        val body: ArrayDeque<P>,
        val ate: Boolean
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
    // 蛇 / 逻辑状态
    // =========================================================
    private val snake =
        ArrayDeque<P>()

    private val queue =
        ArrayDeque<P>()

    private var prevSnake: List<P> =
        emptyList()

    private var moveProgress = 0f

    private val dirs =
        listOf(
            P(0, -1),
            P(0, 1),
            P(-1, 0),
            P(1, 0)
        )

    private var dir =
        P(1, 0)

    private var food =
        P(5, 5)

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

    private var combo = 0
    private var hunger = 0

    private var deathCause = "无"
    private var lastDeathInfo = ""

    private var ai =
        Snapshot()

    private var aggression = 1.15f
    private var safetyMargin = 1.10f
    private var shortcutBonus = 0.90f

    private var deathWall = 0
    private var deathSelf = 0
    private var deathTrap = 0
    private var totalGames = 0

    // =========================================================
    // 分数倍率 / 速度曲线参数
    // =========================================================
    private val SPEED_START = 220L
    private val SPEED_MIN = 60L
    private val SPEED_DECAY = 1500f

    private var lastMultiplier = 1f
    private var lastStage = 0

    // =========================================================
    // 学习参数
    // =========================================================
    private val q =
        Array(20) {
            FloatArray(5)
        }

    private val n =
        Array(20) {
            IntArray(5)
        }

    private var lastState = -1
    private var lastAction = -1
    private var steps = 0
    private var saveCounter = 0

    var onScoreChanged:
        ((Int) -> Unit)? = null

    var onMoneyChanged:
        ((Int) -> Unit)? = null

    private val prefs =
        context.getSharedPreferences(
            "snake_prefs",
            Context.MODE_PRIVATE
        )

    private val vibrator: Vibrator? =
        if (
            Build.VERSION.SDK_INT >=
            Build.VERSION_CODES.S
        ) {
            (
                context.getSystemService(
                    Context.VIBRATOR_MANAGER_SERVICE
                ) as? VibratorManager
            )?.defaultVibrator
        } else {
            @Suppress("DEPRECATION")
            context.getSystemService(
                Context.VIBRATOR_SERVICE
            ) as? Vibrator
        }

    // =========================================================
    // 皮肤 / 背景
    // =========================================================
    private var bodyColor =
        Color.rgb(
            46,
            204,
            113
        )

    private var headColor =
        Color.rgb(
            39,
            174,
            96
        )

    private var bgColor =
        Color.BLACK

    private var gridColor =
        Color.CYAN

    private var rainbowSkin =
        false

    private val hsv =
        IntArray(360) {
            Color.HSVToColor(
                floatArrayOf(
                    it.toFloat(),
                    1f,
                    1f
                )
            )
        }

    // =========================================================
    // 特效容器
    // =========================================================
    private val particles =
        mutableListOf<Particle>()

    private val floats =
        mutableListOf<FloatText>()

    private val ripples =
        mutableListOf<Ripple>()

    private var globalTime = 0f
    private var foodPhase = 0f
    private var flash = 0f
    private var shakeX = 0f
    private var shakeY = 0f
    private var shakeAmp = 0f

    // =========================================================
    // Paint
    // =========================================================
    private val paint =
        Paint(Paint.ANTI_ALIAS_FLAG)

    private val text =
        Paint(Paint.ANTI_ALIAS_FLAG)

    private val panel =
        Paint(Paint.ANTI_ALIAS_FLAG)

    private val border =
        Paint(Paint.ANTI_ALIAS_FLAG)

    private val gridPaint =
        Paint(Paint.ANTI_ALIAS_FLAG)

    private val snakePaint =
        Paint(Paint.ANTI_ALIAS_FLAG)

    private val headPaint =
        Paint(Paint.ANTI_ALIAS_FLAG)

    private val foodPaint =
        Paint(Paint.ANTI_ALIAS_FLAG)

    private val glowPaint =
        Paint(Paint.ANTI_ALIAS_FLAG)

    private val bgPaint =
        Paint(Paint.ANTI_ALIAS_FLAG)

    private var ptsBuf =
        FloatArray(128)

    // =========================================================
    // BFS 缓冲
    // =========================================================
    private val bfsVisited =
        BooleanArray(
            cols * rows
        )

    private val bfsQueue =
        IntArray(
            cols * rows
        )

    private val bfsParent =
        IntArray(
            cols * rows
        )

    private var beamNodes = 0

    // =========================================================
    // 帧回调
    // =========================================================
    private val frame =
        object : Choreographer.FrameCallback {

            override fun doFrame(
                ns: Long
            ) {

                if (!running) {
                    return
                }

                if (lastFrame == 0L) {
                    lastFrame = ns
                }

                val dtMs =
                    (
                        (
                            ns -
                                lastFrame
                            ) /
                            1_000_000L
                        )
                        .coerceAtMost(
                            100L
                        )

                lastFrame = ns

                accumulator += dtMs

                var guard = 0

                while (
                    accumulator >=
                    gameSpeed &&
                    guard < 4
                ) {

                    updateGame()

                    accumulator -=
                        gameSpeed

                    guard++
                }

                if (guard >= 4) {
                    accumulator = 0L
                }

                moveProgress =
                    (
                        accumulator.toFloat() /
                            gameSpeed.toFloat()
                        )
                        .coerceIn(
                            0f,
                            1f
                        )

                updateEffects(
                    dtMs / 16f
                )

                invalidate()

                Choreographer
                    .getInstance()
                    .postFrameCallback(
                        this
                    )
            }
        }

    // =========================================================
    // init
    // =========================================================
    init {

        highScore =
            prefs.getInt(
                "high_score",
                0
            )

        money =
            prefs.getInt(
                "money",
                0
            )

        aggression =
            prefs.getFloat(
                "learn_aggression",
                1.15f
            )

        safetyMargin =
            prefs.getFloat(
                "learn_safety",
                1.10f
            )

        shortcutBonus =
            prefs.getFloat(
                "learn_shortcut",
                0.90f
            )

        deathWall =
            prefs.getInt(
                "stat_wall",
                0
            )

        deathSelf =
            prefs.getInt(
                "stat_self",
                0
            )

        deathTrap =
            prefs.getInt(
                "stat_trap",
                0
            )

        totalGames =
            prefs.getInt(
                "stat_total",
                0
            )

        for (s in 0 until 20) {

            for (a in 0 until 5) {

                q[s][a] =
                    prefs.getFloat(
                        "q_${s}_$a",
                        0f
                    )

                n[s][a] =
                    prefs.getInt(
                        "n_${s}_$a",
                        0
                    )
            }
        }

        setLayerType(
            LAYER_TYPE_HARDWARE,
            null
        )

        updateCurrentSkin()
        updateCurrentBoard()

        reset()
    }

    // =========================================================
    // 生命周期
    // =========================================================
    override fun onAttachedToWindow() {

        super.onAttachedToWindow()

        // Choreographer 会自动跟随屏幕刷新率：
        // 120Hz 屏幕即 120fps，60Hz 屏幕即 60fps。
        // 无需显式调用 Window.setFrameRate()。
    }

    override fun onDetachedFromWindow() {

        super.onDetachedFromWindow()

        pause()
    }

    // =========================================================
    // 对外接口
    // =========================================================
    fun getAIMode(): Int {

        return aiMode
    }

    fun setAIMode(
        m: Int
    ) {

        aiMode = m

        reset()
    }

    fun setForcedStrategy(
        s: Int
    ) {

        forcedStrategy = s

        invalidate()
    }

    fun updateCurrentSkin() {

        when (
            prefs.getString(
                "equipped_skin",
                "green"
            )
        ) {

            "blue" -> {

                setSnakeColors(
                    Color.rgb(
                        52,
                        152,
                        219
                    ),
                    Color.rgb(
                        41,
                        128,
                        185
                    ),
                    false
                )
            }

            "red" -> {

                setSnakeColors(
                    Color.rgb(
                        231,
                        76,
                        60
                    ),
                    Color.rgb(
                        192,
                        57,
                        43
                    ),
                    false
                )
            }

            "purple" -> {

                setSnakeColors(
                    Color.rgb(
                        155,
                        89,
                        182
                    ),
                    Color.rgb(
                        142,
                        68,
                        173
                    ),
                    false
                )
            }

            "gold" -> {

                setSnakeColors(
                    Color.rgb(
                        241,
                        196,
                        15
                    ),
                    Color.rgb(
                        243,
                        156,
                        18
                    ),
                    false
                )
            }

            "rainbow" -> {

                setSnakeColors(
                    Color.WHITE,
                    Color.WHITE,
                    true
                )
            }

            else -> {

                setSnakeColors(
                    Color.rgb(
                        46,
                        204,
                        113
                    ),
                    Color.rgb(
                        39,
                        174,
                        96
                    ),
                    false
                )
            }
        }

        invalidate()
    }

    private fun setSnakeColors(
        body: Int,
        head: Int,
        rainbow: Boolean
    ) {

        bodyColor = body
        headColor = head
        rainbowSkin = rainbow

        snakePaint.color = body

        snakePaint.style =
            Paint.Style.FILL

        headPaint.color = head
    }

    fun updateCurrentBoard() {

        when (
            prefs.getString(
                "equipped_board",
                "dark"
            )
        ) {

            "light" -> {

                bgColor =
                    Color.rgb(
                        240,
                        240,
                        240
                    )

                gridColor =
                    Color.rgb(
                        200,
                        200,
                        200
                    )
            }

            "neon" -> {

                bgColor =
                    Color.rgb(
                        10,
                        25,
                        47
                    )

                gridColor =
                    Color.CYAN
            }

            "forest" -> {

                bgColor =
                    Color.rgb(
                        27,
                        46,
                        26
                    )

                gridColor =
                    Color.rgb(
                        46,
                        74,
                        45
                    )
            }

            "cyberpunk" -> {

                bgColor =
                    Color.rgb(
                        43,
                        15,
                        59
                    )

                gridColor =
                    Color.MAGENTA
            }

            "rainbow_board" -> {

                bgColor =
                    Color.BLACK

                gridColor =
                    Color.WHITE
            }

            else -> {

                bgColor =
                    Color.BLACK

                gridColor =
                    Color.CYAN
            }
        }

        invalidate()
    }

    // =========================================================
    // 分数倍率 / 速度曲线
    // =========================================================

    /**
     * 速度曲线：指数衰减。
     */
    private fun computeGameSpeed(): Long {

        val k =
            kotlin.math.exp(
                -score.toFloat() /
                    SPEED_DECAY
            )

        val s =
            SPEED_MIN +
                (
                    SPEED_START -
                        SPEED_MIN
                    ) * k

        return s
            .toLong()
            .coerceIn(
                SPEED_MIN,
                SPEED_START
            )
    }

    /**
     * 分数倍率 = 阶段倍率 × 连击倍率
     */
    private fun computeScoreMultiplier(): Float {

        val stage =
            when {

                score < 50 ->
                    1.0f

                score < 150 ->
                    1.2f

                score < 300 ->
                    1.5f

                score < 500 ->
                    1.8f

                score < 800 ->
                    2.2f

                score < 1200 ->
                    2.6f

                score < 1800 ->
                    3.0f

                score < 2500 ->
                    3.5f

                score < 3500 ->
                    4.0f

                score < 5000 ->
                    4.5f

                else ->
                    5.0f +
                        (
                            score -
                                5000
                            ) /
                        2000f
            }

        val comboMul =
            1f +
                min(
                    combo,
                    20
                ) * 0.03f

        return stage * comboMul
    }

    /**
     * 当前所处的阶段编号。
     */
    private fun computeStage(): Int =
        when {

            score < 50 ->
                0

            score < 150 ->
                1

            score < 300 ->
                2

            score < 500 ->
                3

            score < 800 ->
                4

            score < 1200 ->
                5

            score < 1800 ->
                6

            score < 2500 ->
                7

            score < 3500 ->
                8

            score < 5000 ->
                9

            else ->
                10
        }

    // =========================================================
    // 重置 / 生命周期
    // =========================================================
    fun reset() {

        snake.clear()
        queue.clear()

        prevSnake =
            emptyList()

        moveProgress = 0f

        if (aiMode == 2) {

            snake.add(
                P(
                    0,
                    0
                )
            )

            dir =
                P(
                    0,
                    1
                )

        } else {

            snake.add(
                P(
                    cols / 2,
                    rows / 2
                )
            )

            dir =
                P(
                    1,
                    0
                )
        }

        score = 0
        combo = 0
        hunger = 0

        gameOver = false

        deathCause = "无"
        lastDeathInfo = ""

        gameSpeed =
            SPEED_START

        lastStage = 0
        lastMultiplier = 1f

        accumulator = 0L
        lastFrame = 0L

        particles.clear()
        floats.clear()
        ripples.clear()

        flash = 0f
        shakeX = 0f
        shakeY = 0f
        shakeAmp = 0f

        ai =
            Snapshot(
                chosen = dir
            )

        placeFood()

        onScoreChanged?.invoke(
            score
        )

        invalidate()
    }

    fun resume() {

        if (running) {
            return
        }

        running = true
        lastFrame = 0L

        Choreographer
            .getInstance()
            .postFrameCallback(
                frame
            )
    }

    fun pause() {

        running = false

        try {

            Choreographer
                .getInstance()
                .removeFrameCallback(
                    frame
                )

        } catch (
            _: Throwable
        ) {
        }
    }

    // =========================================================
    // 逻辑更新
    // =========================================================
    private fun updateGame() {

        if (gameOver) {
            return
        }

        prevSnake =
            snake.toList()

        if (aiMode != 0) {

            val chosen =
                chooseMove()

            queue.clear()

            queue.add(
                chosen
            )
        }

        if (queue.isNotEmpty()) {

            val requested =
                queue.removeFirst()

            if (
                !isReverse(
                    requested,
                    dir
                ) &&
                legalDirection(
                    requested
                )
            ) {

                dir = requested
            }
        }

        if (
            dir ==
            P(
                0,
                0
            )
        ) {
            return
        }

        val nh =
            P(
                snake.first().x +
                    dir.x,

                snake.first().y +
                    dir.y
            )

        if (!inside(nh)) {

            die("WALL")

            return
        }

        val ate =
            nh == food

        val body =
            snake.toList()

        val hitIndex =
            body.indexOf(
                nh
            )

        val tail =
            snake.last()

        if (
            hitIndex >= 0 &&
            !(
                nh == tail &&
                    !ate
                )
        ) {

            val b =
                ArrayDeque(
                    snake
                )

            b.addFirst(nh)

            if (!ate) {
                b.removeLast()
            }

            val region =
                freeRegion(b)

            val need =
                max(
                    2,
                    (
                        snake.size *
                            safetyMargin
                        ).toInt()
                )

            if (region < need) {

                die("TRAP")

            } else {

                die("SELF")
            }

            return
        }

        snake.addFirst(nh)

        if (ate) {

            val mul =
                computeScoreMultiplier()

            lastMultiplier = mul

            val gained =
                (
                    10f *
                        mul
                    )
                    .toInt()
                    .coerceAtLeast(
                        1
                    )

            score += gained

            combo++
            hunger = 0
            money++

            if (score > highScore) {

                highScore =
                    score

                prefs
                    .edit()
                    .putInt(
                        "high_score",
                        highScore
                    )
                    .apply()
            }

            onScoreChanged?.invoke(
                score
            )

            onMoneyChanged?.invoke(
                money
            )

            prefs
                .edit()
                .putInt(
                    "money",
                    money
                )
                .apply()

            learn(
                2.5f +
                    combo *
                    0.05f
            )

            val newStage =
                computeStage()

            if (newStage > lastStage) {

                lastStage = newStage

                floats.add(
                    FloatText(
                        snake.first().x
                            .toFloat(),

                        snake.first().y
                            .toFloat(),

                        1.6f,

                        "倍率 ×${
                            "%.1f".format(
                                mul
                            )
                        }"
                    )
                )

                flash =
                    max(
                        flash,
                        0.4f
                    )

                shakeAmp =
                    max(
                        shakeAmp,
                        cell * 0.25f
                    )
            }

            spawnFoodEffect(
                nh,
                gained,
                mul
            )

            shakeAmp =
                max(
                    shakeAmp,
                    cell * 0.15f
                )

            placeFood()

            gameSpeed =
                computeGameSpeed()

        } else {

            snake.removeLast()

            hunger++

            combo =
                max(
                    0,
                    combo - 1
                )

            learn(0.025f)
        }

        steps++
    }

    // =========================================================
    // AI 决策
    // =========================================================
    private fun chooseMove(): P {

        val candidates =
            dirs.map { d ->

                evaluate(d)
            }

        val legal =
            candidates.filter {
                it.legal
            }

        if (legal.isEmpty()) {

            ai =
                Snapshot(
                    strategy = "NO MOVE",
                    reason =
                        "四个方向都无法安全前进",
                    danger = 5,
                    chosen = dir,
                    candidates =
                        candidates
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

        val pickStrategy =
            if (forcedStrategy >= 0) {

                forcedStrategy
                    .coerceIn(
                        0,
                        3
                    )

            } else {

                strategy
            }

        val final =
            when (pickStrategy) {

                0 ->
                    bfsChoose(legal)

                1 ->
                    legal.maxByOrNull {
                        tailScore(it)
                    }

                2 ->
                    hamChoose(legal)

                else ->
                    beamBest(legal)

            } ?: legal.first()

        val action =
            dirs
                .indexOfFirst {
                    it == final.d
                }
                .coerceAtLeast(
                    0
                )

        lastState = state
        lastAction = action

        val region =
            freeRegion(snake)

        val foodDistance =
            distance(
                snake.first(),
                food,
                snake,
                true
            )

        ai =
            Snapshot(
                strategy =
                    strategyName(
                        pickStrategy
                    ),

                reason =
                    reasonFor(
                        final,
                        strategy,
                        danger
                    ),

                danger = danger,

                region = region,

                spaceRatio =
                    region.toFloat() /
                        max(
                            1,
                            snake.size
                        ),

                tailReachable =
                    tailReachable(snake),

                foodReachable =
                    foodDistance >= 0,

                foodDistance =
                    foodDistance,

                hunger = hunger,

                chosen = final.d,

                candidates = candidates,

                depth =
                    if (pickStrategy == 3)
                        4
                    else
                        2,

                nodes =
                    if (pickStrategy == 3)
                        beamNodes
                    else
                        candidates.size
            )

        return final.d
    }

    private fun evaluate(
        d: P
    ): Candidate {

        if (!legalDirection(d)) {

            return Candidate(
                d,
                -1e9f,
                "撞墙/身体",
                false
            )
        }

        val sim =
            simulate(d)

        val region =
            freeRegion(
                sim.body
            )

        val tail =
            tailReachable(
                sim.body
            )

        val foodDist =
            distance(
                sim.body.first(),
                food,
                sim.body,
                true
            )

        val ate =
            sim.ate

        val mobility =
            countSafeMoves(
                sim.body
            )

        var s =
            region * 11f +
                mobility * 35f

        if (tail) {

            s += 180f

        } else {

            s -= 250f
        }

        if (foodDist >= 0) {

            s +=
                aggression *
                    (
                        300f /
                            (
                                foodDist + 1
                                )
                        )

        } else {

            s -= 450f
        }

        if (ate) {

            s +=
                850f *
                    aggression
        }

        val edge =
            min(
                min(
                    sim.body.first().x,
                    cols - 1 -
                        sim.body.first().x
                ),
                min(
                    sim.body.first().y,
                    rows - 1 -
                        sim.body.first().y
                )
            )

        s -=
            max(
                0,
                2 - edge
            ) * 55f

        val spacePenalty =
            max(
                0f,
                snake.size *
                    safetyMargin -
                    region.toFloat()
            )

        s -=
            spacePenalty *
                30f

        val reason =
            when {

                ate ->
                    "马上吃到食物"

                tail ->
                    "保持尾巴可达"

                else ->
                    "扩大可用空间"
            }

        return Candidate(
            d,
            s,
            reason,
            true
        )
    }

    // ---------------------------------------------------------
    // 策略 1：BFS 真正寻路到食物
    // ---------------------------------------------------------
    private fun bfsChoose(
        legal: List<Candidate>
    ): Candidate? {

        val step =
            bfsPathToFood()

        if (step != null) {

            val cand =
                legal.firstOrNull {
                    it.d == step
                }

            if (
                cand != null &&
                isMoveSafe(step)
            ) {

                return cand
            }
        }

        return legal.maxByOrNull {
            it.score
        }
    }

    // ---------------------------------------------------------
    // 策略 2：HAM 蛇形路径
    // ---------------------------------------------------------
    private fun hamChoose(
        legal: List<Candidate>
    ): Candidate? {

        val head =
            snake.first()

        val curIdx =
            hamIndexOf(head)

        val total =
            cols * rows

        val foodStep =
            bfsPathToFood()

        if (foodStep != null) {

            val cand =
                legal.firstOrNull {
                    it.d == foodStep
                }

            if (cand != null) {

                val dist =
                    distance(
                        head,
                        food,
                        snake,
                        true
                    )

                if (
                    dist in 1..2 &&
                    isMoveSafe(foodStep)
                ) {

                    return cand
                }
            }
        }

        var best: Candidate? = null
        var bestScore = -1e9f

        for (c in legal) {

            val next =
                P(
                    head.x + c.d.x,
                    head.y + c.d.y
                )

            val nextIdx =
                hamIndexOf(next)

            val diff =
                (
                    nextIdx -
                        curIdx +
                        total
                    ) % total

            val bonus =
                when {

                    diff == 1 ->
                        400f

                    diff in 2..6 ->
                        80f

                    else ->
                        -150f
                }

            val sc =
                c.score * 0.15f +
                    bonus

            if (sc > bestScore) {

                bestScore = sc
                best = c
            }
        }

        return best
    }

    // ---------------------------------------------------------
    // 策略 3：TAIL 追尾
    // ---------------------------------------------------------
    private fun tailScore(
        c: Candidate
    ): Float {

        return c.score +
            if (
                tailReachable(
                    simulate(c.d).body
                )
            ) {

                350f

            } else {

                -500f
            }
    }

    // ---------------------------------------------------------
    // 策略 4：BEAM 前瞻
    // ---------------------------------------------------------
    private fun beamBest(
        legal: List<Candidate>
    ): Candidate {

        var best =
            legal.maxByOrNull {
                it.score
            } ?: legal.first()

        var bestScore = -1e30f

        beamNodes = 0

        data class Node(
            val body: ArrayDeque<P>,
            val first: P,
            val score: Float,
            val depth: Int
        )

        var layer =
            legal.map {

                Node(
                    simulate(
                        it.d
                    ).body,

                    it.d,

                    it.score,

                    1
                )
            }

        repeat(3) {

            val next =
                ArrayList<Node>()

            for (nod in layer) {

                beamNodes++

                if (nod.score > bestScore) {

                    bestScore =
                        nod.score

                    best =
                        legal.firstOrNull {
                            it.d ==
                                nod.first
                        } ?: best
                }

                for (d in dirs) {

                    if (
                        isReverse(
                            d,
                            directionOfFirst(
                                nod.body
                            )
                        )
                    ) {
                        continue
                    }

                    if (
                        !canSim(
                            nod.body,
                            d
                        )
                    ) {
                        continue
                    }

                    val sm =
                        simulateOn(
                            nod.body,
                            d
                        )

                    val r =
                        freeRegion(
                            sm.body
                        )

                    val t =
                        tailReachable(
                            sm.body
                        )

                    val fd =
                        distance(
                            sm.body.first(),
                            food,
                            sm.body,
                            true
                        )

                    var sc =
                        nod.score +
                            r * 6f +
                            if (t)
                                90f
                            else
                                -140f

                    if (fd >= 0) {

                        sc +=
                            100f /
                                (
                                    fd + 1
                                    )
                    }

                    if (sm.ate) {
                        sc += 500f
                    }

                    next.add(
                        Node(
                            sm.body,
                            nod.first,
                            sc,
                            nod.depth + 1
                        )
                    )
                }
            }

            layer =
                next
                    .sortedByDescending {
                        it.score
                    }
                    .take(8)
        }

        return best
    }

    // ---------------------------------------------------------
    // 策略选择
    // ---------------------------------------------------------
    private fun selectStrategy(
        state: Int,
        danger: Int
    ): Int {

        if (forcedStrategy >= 0) {

            return forcedStrategy
                .coerceIn(
                    0,
                    4
                )
                .let {

                    if (it == 4)
                        3
                    else
                        it
                }
        }

        val hungerBias =
            if (hunger > 18)
                1.5f
            else
                0f

        val dangerBias =
            if (danger >= 4)
                2.5f
            else
                0f

        val prior =
            floatArrayOf(

                if (
                    snake.size < 35
                )
                    1.2f +
                        hungerBias
                else
                    0.5f,

                1f +
                    dangerBias,

                if (
                    snake.size >= 35
                )
                    1.8f
                else
                    0.4f,

                if (
                    snake.size < 100
                )
                    1.3f
                else
                    0.7f,

                0f
            )

        var best = 0
        var value = -1e9f

        for (a in 0..3) {

            val bonus =
                if (n[state][a] == 0)
                    0.8f
                else
                    q[state][a]

            val ucb =
                bonus +
                    prior[a]

            if (ucb > value) {

                value = ucb
                best = a
            }
        }

        return best
    }

    private fun learnState(
        len: Int,
        danger: Int
    ): Int {

        val stage =
            when {

                len < 25 ->
                    0

                len < 50 ->
                    1

                len < 85 ->
                    2

                else ->
                    3
            }

        return stage * 5 +
            (
                danger - 1
                ).coerceIn(
                0,
                4
            )
    }

    private fun learn(
        reward: Float
    ) {

        if (
            lastState < 0 ||
            lastAction < 0
        ) {
            return
        }

        val s = lastState
        val a = lastAction

        val alpha =
            when {

                n[s][a] < 10 ->
                    0.20f

                n[s][a] < 50 ->
                    0.10f

                else ->
                    0.04f
            }

        q[s][a] +=
            alpha *
                (
                    reward -
                        q[s][a]
                    )

        n[s][a]++

        if (
            ++saveCounter %
            20 == 0
        ) {
            saveLearning()
        }
    }

    private fun saveLearning() {

        val e =
            prefs
                .edit()
                .putFloat(
                    "learn_aggression",
                    aggression
                )
                .putFloat(
                    "learn_safety",
                    safetyMargin
                )
                .putFloat(
                    "learn_shortcut",
                    shortcutBonus
                )
                .putInt(
                    "stat_wall",
                    deathWall
                )
                .putInt(
                    "stat_self",
                    deathSelf
                )
                .putInt(
                    "stat_trap",
                    deathTrap
                )
                .putInt(
                    "stat_total",
                    totalGames
                )
                .putInt(
                    "money",
                    money
                )

        for (s in 0 until 20) {

            for (a in 0 until 5) {

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

        e.apply()
    }

    private fun die(
        cause: String
    ) {

        gameOver = true
        deathCause = cause

        when (cause) {

            "WALL" -> {

                deathWall++

                learn(-6f)
            }

            "SELF" -> {

                deathSelf++

                learn(-7f)
            }

            else -> {

                deathTrap++

                learn(-8f)
            }
        }

        totalGames++

        aggression =
            when (cause) {

                "WALL" ->
                    max(
                        0.5f,
                        aggression * 0.97f
                    )

                "SELF" ->
                    max(
                        0.5f,
                        aggression * 0.99f
                    )

                else ->
                    max(
                        0.5f,
                        aggression * 0.94f
                    )
            }

        if (
            cause ==
            "TRAP"
        ) {

            safetyMargin =
                min(
                    3f,
                    safetyMargin * 1.04f
                )
        }

        lastDeathInfo =
            "死亡=$cause  长度=${snake.size}  分数=$score  " +
                "空间=${ai.region} 需求=${
                    (
                        snake.size *
                            safetyMargin
                        ).toInt()
                }  " +
                "尾巴=${
                    if (ai.tailReachable)
                        "可达"
                    else
                        "不可达"
                }"

        saveLearning()

        flash = 1f

        shakeAmp =
            cell * 0.55f

        vibrator?.let {

            if (
                Build.VERSION.SDK_INT >=
                26
            ) {

                it.vibrate(
                    VibrationEffect
                        .createOneShot(
                            120,
                            VibrationEffect
                                .DEFAULT_AMPLITUDE
                        )
                )

            } else {

                @Suppress("DEPRECATION")

                it.vibrate(120)
            }
        }

        invalidate()
    }

    private fun reasonFor(
        c: Candidate,
        strategy: Int,
        danger: Int
    ): String {

        return when {

            !c.legal ->
                "此方向不合法"

            c.d == dir &&
                danger >= 4 ->
                "危险较高，继续保持可控路线"

            c.reason ==
                "马上吃到食物" ->
                "食物可安全取得，收益高"

            c.reason ==
                "保持尾巴可达" ->
                "优先保持尾巴出口，避免困死"

            else ->
                "综合空间、食物、尾巴与边界风险"
        }
    }

    private fun strategyName(
        s: Int
    ): String {

        return when (s) {

            0 ->
                "BFS 寻路"

            1 ->
                "TAIL 追尾"

            2 ->
                "HAM 蛇形"

            3 ->
                "BEAM 前瞻"

            4 ->
                "BEAM 前瞻"

            else ->
                "AUTO"
        }
    }

    // =========================================================
    // 模拟 / BFS / 工具
    // =========================================================
    private fun simulate(
        d: P
    ): Sim {

        return simulateOn(
            ArrayDeque(snake),
            d
        )
    }

    private fun simulateOn(
        src: ArrayDeque<P>,
        d: P
    ): Sim {

        val b =
            ArrayDeque(src)

        if (b.isEmpty()) {

            return Sim(
                b,
                false
            )
        }

        val nh =
            P(
                b.first().x +
                    d.x,

                b.first().y +
                    d.y
            )

        if (!inside(nh)) {

            return Sim(
                b,
                false
            )
        }

        val ate =
            nh == food

        if (
            b.contains(nh) &&
            !(
                nh == b.last() &&
                    !ate
                )
        ) {

            return Sim(
                b,
                false
            )
        }

        b.addFirst(nh)

        if (!ate) {
            b.removeLast()
        }

        return Sim(
            b,
            ate
        )
    }

    private fun canSim(
        body: ArrayDeque<P>,
        d: P
    ): Boolean {

        if (body.isEmpty()) {
            return false
        }

        val h =
            body.first()

        val nh =
            P(
                h.x + d.x,
                h.y + d.y
            )

        if (!inside(nh)) {
            return false
        }

        val ate =
            nh == food

        return !body.contains(nh) ||
            (
                nh == body.last() &&
                    !ate
                )
    }

    private fun legalDirection(
        d: P
    ): Boolean {

        return d !=
            P(
                0,
                0
            ) &&
            !isReverse(
                d,
                dir
            ) &&
            canSim(
                snake,
                d
            )
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

    private fun inside(
        p: P
    ): Boolean {

        return p.x in 0 until cols &&
            p.y in 0 until rows
    }

    private fun freeRegion(
        body: ArrayDeque<P>
    ): Int {

        if (body.isEmpty()) {
            return 0
        }

        val total =
            cols * rows

        java.util.Arrays.fill(
            bfsVisited,
            false
        )

        for (p in body) {

            if (
                p.x !in 0 until cols ||
                p.y !in 0 until rows
            ) {
                continue
            }

            val idx =
                p.y * cols +
                    p.x

            if (
                idx in 0 until total
            ) {

                bfsVisited[idx] =
                    true
            }
        }

        val start =
            body.first()

        if (
            start.x !in 0 until cols ||
            start.y !in 0 until rows
        ) {
            return 0
        }

        val startIndex =
            start.y * cols +
                start.x

        if (
            startIndex !in 0 until total
        ) {
            return 0
        }

        bfsVisited[startIndex] =
            false

        var head = 0
        var tail = 0

        bfsQueue[tail++] =
            startIndex

        var count = 0

        while (
            head < tail
        ) {

            val curr =
                bfsQueue[head++]

            if (
                curr !in 0 until total
            ) {
                continue
            }

            val cx =
                curr % cols

            val cy =
                curr / cols

            count++

            fun addNode(
                index: Int
            ) {

                if (
                    index !in 0 until total
                ) {
                    return
                }

                if (
                    bfsVisited[index]
                ) {
                    return
                }

                bfsVisited[index] =
                    true

                if (
                    tail <
                    bfsQueue.size
                ) {

                    bfsQueue[tail++] =
                        index
                }
            }

            if (cx > 0) {
                addNode(curr - 1)
            }

            if (cx < cols - 1) {
                addNode(curr + 1)
            }

            if (cy > 0) {
                addNode(curr - cols)
            }

            if (cy < rows - 1) {
                addNode(curr + cols)
            }
        }

        return count
    }

    private fun bfsPathToFood(): P? {

        if (snake.isEmpty()) {
            return null
        }

        val start =
            snake.first()

        if (start == food) {
            return null
        }

        val total =
            cols * rows

        java.util.Arrays.fill(
            bfsVisited,
            false
        )

        java.util.Arrays.fill(
            bfsParent,
            -1
        )

        for (p in snake) {

            val idx =
                p.y * cols +
                    p.x

            if (
                idx in 0 until total
            ) {

                bfsVisited[idx] =
                    true
            }
        }

        val tail =
            snake.last()

        bfsVisited[
            tail.y * cols +
                tail.x
        ] = false

        val startIdx =
            start.y * cols +
                start.x

        val targetIdx =
            food.y * cols +
                food.x

        bfsVisited[startIdx] =
            false

        var h = 0
        var t = 0

        bfsQueue[t++] =
            startIdx

        bfsVisited[startIdx] =
            true

        var found = false

        while (h < t) {

            val cur =
                bfsQueue[h++]

            if (cur == targetIdx) {

                found = true
                break
            }

            val cx =
                cur % cols

            val cy =
                cur / cols

            if (
                cx > 0 &&
                !bfsVisited[cur - 1]
            ) {

                bfsVisited[cur - 1] =
                    true

                bfsParent[cur - 1] =
                    cur

                if (t < bfsQueue.size) {
                    bfsQueue[t++] =
                        cur - 1
                }
            }

            if (
                cx < cols - 1 &&
                !bfsVisited[cur + 1]
            ) {

                bfsVisited[cur + 1] =
                    true

                bfsParent[cur + 1] =
                    cur

                if (t < bfsQueue.size) {
                    bfsQueue[t++] =
                        cur + 1
                }
            }

            if (
                cy > 0 &&
                !bfsVisited[cur - cols]
            ) {

                bfsVisited[cur - cols] =
                    true

                bfsParent[cur - cols] =
                    cur

                if (t < bfsQueue.size) {
                    bfsQueue[t++] =
                        cur - cols
                }
            }

            if (
                cy < rows - 1 &&
                !bfsVisited[cur + cols]
            ) {

                bfsVisited[cur + cols] =
                    true

                bfsParent[cur + cols] =
                    cur

                if (t < bfsQueue.size) {
                    bfsQueue[t++] =
                        cur + cols
                }
            }
        }

        if (!found) {
            return null
        }

        var cur =
            targetIdx

        while (
            bfsParent[cur] != startIdx &&
            bfsParent[cur] != -1
        ) {

            cur =
                bfsParent[cur]
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

    private fun isMoveSafe(
        d: P
    ): Boolean {

        val sim =
            simulate(d)

        if (sim.body.isEmpty()) {
            return false
        }

        if (
            !tailReachable(
                sim.body
            )
        ) {
            return false
        }

        val region =
            freeRegion(sim.body)

        return region >=
            max(
                3,
                sim.body.size
            )
    }

    private fun distance(
        start: P,
        target: P,
        body: Collection<P>,
        allowTail: Boolean
    ): Int {

        if (
            start.x !in 0 until cols ||
            start.y !in 0 until rows
        ) {
            return -1
        }

        if (
            target.x !in 0 until cols ||
            target.y !in 0 until rows
        ) {
            return -1
        }

        if (start == target) {
            return 0
        }

        val total =
            cols * rows

        java.util.Arrays.fill(
            bfsVisited,
            false
        )

        for (p in body) {

            if (
                p.x !in 0 until cols ||
                p.y !in 0 until rows
            ) {
                continue
            }

            val idx =
                p.y * cols +
                    p.x

            if (
                idx in 0 until total
            ) {

                bfsVisited[idx] =
                    true
            }
        }

        if (
            allowTail &&
            body.isNotEmpty()
        ) {

            val last =
                body.last()

            if (
                last.x in 0 until cols &&
                last.y in 0 until rows
            ) {

                val idx =
                    last.y * cols +
                        last.x

                if (
                    idx in 0 until total
                ) {

                    bfsVisited[idx] =
                        false
                }
            }
        }

        val startIndex =
            start.y * cols +
                start.x

        if (
            startIndex !in 0 until total
        ) {
            return -1
        }

        bfsVisited[startIndex] =
            false

        var head = 0
        var tail = 0

        bfsQueue[tail++] =
            startIndex

        var dist = 0

        while (
            head < tail
        ) {

            val layerSize =
                tail - head

            for (i in 0 until layerSize) {

                if (
                    head >= tail
                ) {
                    break
                }

                val curr =
                    bfsQueue[head++]

                if (
                    curr !in 0 until total
                ) {
                    continue
                }

                val cx =
                    curr % cols

                val cy =
                    curr / cols

                if (
                    cx == target.x &&
                    cy == target.y
                ) {

                    return dist
                }

                fun addNode(
                    index: Int
                ) {

                    if (
                        index !in 0 until total
                    ) {
                        return
                    }

                    if (
                        bfsVisited[index]
                    ) {
                        return
                    }

                    bfsVisited[index] =
                        true

                    if (
                        tail <
                        bfsQueue.size
                    ) {

                        bfsQueue[tail++] =
                            index
                    }
                }

                if (cx > 0) {
                    addNode(curr - 1)
                }

                if (cx < cols - 1) {
                    addNode(curr + 1)
                }

                if (cy > 0) {
                    addNode(curr - cols)
                }

                if (cy < rows - 1) {
                    addNode(curr + cols)
                }
            }

            dist++
        }

        return -1
    }

    private fun countSafeMoves(
        body: ArrayDeque<P>
    ): Int {

        if (body.isEmpty()) {
            return 0
        }

        val h =
            body.first()

        return dirs.count { d ->

            val nh =
                P(
                    h.x + d.x,
                    h.y + d.y
                )

            inside(nh) &&
                (
                    !body.contains(nh) ||
                        (
                            nh ==
                                body.last() &&
                                nh != food
                            )
                    ) &&
                !isReverse(
                    d,
                    directionOfFirst(body)
                )
        }
    }

    private fun tailReachable(
        body: ArrayDeque<P>
    ): Boolean {

        if (body.isEmpty()) {
            return false
        }

        return distance(
            body.first(),
            body.last(),
            body,
            true
        ) >= 0
    }

    private fun calculateDanger(): Int {

        val region =
            freeRegion(snake)

        val ratio =
            region.toFloat() /
                max(
                    1,
                    snake.size
                )

        val mobility =
            countSafeMoves(snake)

        return when {

            mobility <= 0 ->
                5

            ratio < 1.5f ->
                5

            ratio < 2.2f ->
                4

            ratio < 3.5f ->
                3

            ratio < 5f ->
                2

            else ->
                1
        }
    }

    private fun hamIndexOf(
        p: P
    ): Int {

        return if (
            p.x % 2 == 0
        ) {

            p.x * rows +
                p.y

        } else {

            p.x * rows +
                (
                    rows - 1 -
                        p.y
                    )
        }
    }

    private fun placeFood() {

        val free =
            ArrayList<P>()

        for (x in 0 until cols) {

            for (y in 0 until rows) {

                val p =
                    P(
                        x,
                        y
                    )

                if (
                    !snake.contains(p)
                ) {

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
                        (
                            mul * 6
                            ).toInt()
                    )
                ).coerceAtMost(40)

        repeat(count) {

            particles.add(
                Particle(
                    p.x.toFloat(),
                    p.y.toFloat(),
                    Random.nextFloat() -
                        0.5f,
                    Random.nextFloat() -
                        0.5f,
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
                flash -
                    dt * 0.05f
            )

        if (shakeAmp > 0.01f) {

            shakeX =
                (
                    Random.nextFloat() -
                        0.5f
                    ) *
                    shakeAmp *
                    2f

            shakeY =
                (
                    Random.nextFloat() -
                        0.5f
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
            (
                w -
                    cols * cell
                ) / 2f

        oy =
            (
                h -
                    rows * cell
                ) / 2f

        invalidate()
    }

    // =========================================================
    // 绘制
    // =========================================================
    override fun onDraw(
        c: Canvas
    ) {

        super.onDraw(c)

        c.drawColor(
            bgColor
        )

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
                        )
                        .toInt()
                        .coerceIn(
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
            max(
                w,
                h
            ) * 0.7f

        val pulse =
            0.85f +
                0.15f *
                sin(
                    globalTime *
                        0.7f
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
            60 +
                (
                    40 *
                        sin(
                            globalTime *
                                1.4f
                        )
                    )
                    .toInt()
                    .coerceIn(
                        0,
                        80
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

        gridPaint.strokeWidth =
            1f

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
            cell *
                0.22f *
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

        val rot =
            globalTime * 90f

        foodPaint.color =
            Color.argb(
                90,
                255,
                200,
                120
            )

        c.save()

        c.rotate(
            rot,
            cx,
            cy
        )

        val rect =
            RectF(
                cx -
                    cell * 0.42f,
                cy -
                    cell * 0.42f,
                cx +
                    cell * 0.42f,
                cy +
                    cell * 0.42f
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
            if (prevSnake.isEmpty())
                snake.toList()
            else
                prevSnake

        val curr =
            snake.toList()

        val nCount =
            curr.size

        val t =
            if (gameOver)
                1f
            else
                moveProgress

        ensurePts(nCount)

        for (i in 0 until nCount) {

            val a =
                if (i < prev.size)
                    prev[i]
                else
                    prev.last()

            val b =
                curr[i]

            ptsBuf[i * 2] =
                a.x +
                    (b.x - a.x) *
                    t

            ptsBuf[i * 2 + 1] =
                a.y +
                    (b.y - a.y) *
                    t
        }

        val sub =
            when {

                nCount < 30 ->
                    4

                nCount < 70 ->
                    3

                else ->
                    2
            }

        for (i in nCount - 1 downTo 1) {

            val x0 =
                ptsBuf[i * 2]

            val y0 =
                ptsBuf[i * 2 + 1]

            val x1 =
                ptsBuf[(i - 1) * 2]

            val y1 =
                ptsBuf[(i - 1) * 2 + 1]

            for (s in sub - 1 downTo 0) {

                val k =
                    s / sub.toFloat()

                val px =
                    x0 +
                        (x1 - x0) *
                        k

                val py =
                    y0 +
                        (y1 - y0) *
                        k

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
                                0.22f * frac
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
                                (
                                    hue.toInt() %
                                        360
                                    ) +
                                    360
                                ) % 360
                        ]

                    } else {

                        blendColor(
                            bodyColor,
                            headColor,
                            (
                                1f -
                                    frac
                                ) * 0.5f
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

            val px =
                ptsBuf[2]

            val py =
                ptsBuf[3]

            dirX =
                hx - px

            dirY =
                hy - py

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
            if (rainbowSkin)
                hsv[
                    (
                        (
                            globalTime *
                                90f
                            ).toInt() %
                            360 +
                            360
                        ) % 360
                ]
            else
                headColor

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
            e1x + pdx * eyeR * 0.35f,
            e1y + pdy * eyeR * 0.35f,
            pupilR,
            paint
        )

        c.drawCircle(
            e2x + pdx * eyeR * 0.35f,
            e2y + pdy * eyeR * 0.35f,
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
                    )
                    .toInt()
                    .coerceIn(
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
                    )
                    .toInt()
                    .coerceIn(
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

        text.isFakeBoldText =
            true

        text.textSize =
            cell * 0.32f

        floats.forEach {

            text.color =
                Color.argb(
                    (
                        it.life * 255
                        )
                        .toInt()
                        .coerceIn(
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

        text.isFakeBoldText =
            false
    }

    // ---------------------------------------------------------
    // 右上角倍率 HUD
    // ---------------------------------------------------------
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

        text.isFakeBoldText =
            true

        text.textSize =
            cell * 0.55f

        val col =
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

        text.color =
            col

        c.drawText(
            "×${
                "%.1f".format(
                    mul
                )
            }",

            width - 24f,

            oy +
                cell * 0.9f,

            text
        )

        text.isFakeBoldText =
            false
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

        val h =
            if (gameOver)
                300f
            else
                300f

        val left =
            (width - w) / 2f

        val top =
            if (gameOver) {

                max(
                    12f,
                    height -
                        h -
                        12f
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

        border.strokeWidth =
            4f

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

        text.isFakeBoldText =
            true

        text.textSize =
            20f

        text.color =
            Color.WHITE

        c.drawText(
            "🧠 AI  ${ai.strategy}",
            left + 16f,
            top + 30f,
            text
        )

        text.isFakeBoldText =
            false

        text.textSize =
            14f

        text.color =
            Color.YELLOW

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
                    5 -
                        ai.danger
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
            "比例 ${
                "%.1f".format(
                    ai.spaceRatio
                )
            }",
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
                ai.foodDistance
                    .toString()

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
            "攻击 ${
                "%.2f".format(
                    aggression
                )
            }",
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
            "倍率 ×${
                "%.1f".format(
                    mulNow
                )
            }",
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

        text.textSize =
            13f

        var x =
            left + 16f

        ai.candidates.forEach {

            val label =
                when (it.d) {

                    P(0, -1) ->
                        "↑"

                    P(0, 1) ->
                        "↓"

                    P(-1, 0) ->
                        "←"

                    else ->
                        "→"
                }

            text.color =
                if (it.legal)
                    Color.WHITE
                else
                    Color.GRAY

            c.drawText(
                "$label ${
                    "%.0f".format(
                        it.score
                    )
                }",
                x,
                top + 196f,
                text
            )

            x +=
                w / 4f
        }

        text.textSize =
            14f

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

        text.textSize =
            12f

        text.color =
            Color.rgb(
                180,
                220,
                255
            )

        c.drawText(
            "BFS 寻路 / HAM 蛇形 / BEAM 前瞻",
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

        text.isFakeBoldText =
            true

        text.textSize =
            30f

        text.color =
            Color.WHITE

        c.drawText(
            "GAME OVER",
            width / 2f,
            height / 2f - 45,
            text
        )

        text.textSize =
            15f

        text.isFakeBoldText =
            false

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

        text.textSize =
            11f

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

            P(0, -1) ->
                "↑"

            P(0, 1) ->
                "↓"

            P(-1, 0) ->
                "←"

            P(1, 0) ->
                "→"

            else ->
                "·"
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
                        (
                            snake.first().x +
                                0.5f
                            ) *
                            cell
                    )

        val dy =
            e.y -
                (
                    oy +
                        (
                            snake.first().y +
                                0.5f
                            ) *
                            cell
                    )

        val d =
            if (
                abs(dx) >
                abs(dy)
            ) {

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

        if (
            !isReverse(
                d,
                dir
            )
        ) {

            queue.add(d)
        }

        return true
    }
}
