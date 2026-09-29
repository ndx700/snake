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

    private val snake = ArrayDeque<P>()
    private val queue = ArrayDeque<P>()

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

    /*
     * ============================================================
     * 极速自动学习版
     *
     * gameSpeed 固定 16ms ≈ 60 步/秒，
     * 一局平均几秒钟就结束，方便刷数据。
     * ============================================================
     */
    private var gameSpeed = 16L
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

    private val q = Array(20) {
        FloatArray(5)
    }

    private val n = Array(20) {
        IntArray(5)
    }

    private var lastState = -1
    private var lastAction = -1
    private var steps = 0

    var onScoreChanged: ((Int) -> Unit)? = null
    var onMoneyChanged: ((Int) -> Unit)? = null

    private val prefs =
        context.getSharedPreferences(
            "snake_prefs",
            Context.MODE_PRIVATE
        )

    private val vibrator: Vibrator? =
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {

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

    private val particles =
        mutableListOf<Particle>()

    private val floats =
        mutableListOf<FloatText>()

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

    private var flash = 0f

    private val bfsVisited =
        BooleanArray(
            cols * rows
        )

    private val bfsQueue =
        IntArray(
            cols * rows
        )

    private var beamNodes = 0

    /*
     * 饥饿自动切 BEAM 阈值
     */
    private val autoBeamHunger = 50

    /*
     * 自动重开之间的等待帧数（毫秒），
     * 太快会看不到 GAME OVER，
     * 太慢又拖节奏。
     */
    private var autoRestartDelay = 250L

    /*
     * 自动重开倒计时（毫秒）
     */
    private var restartCountdown = 0L

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

                val dt =
                    (
                        (
                            ns -
                                lastFrame
                            ) /
                            1_000_000L
                        )
                        .coerceAtMost(100L)

                lastFrame = ns

                // ========================================
                // 死亡后自动重开
                // ========================================
                if (gameOver) {

                    restartCountdown -=
                        dt

                    if (restartCountdown <= 0L) {

                        reset()

                        // 立刻继续下一局
                    }

                } else {

                    accumulator += dt

                    while (
                        accumulator >= gameSpeed
                    ) {

                        updateGame()

                        if (gameOver) {
                            break
                        }

                        accumulator -=
                            gameSpeed
                    }
                }

                updateEffects(
                    dt / 16f
                )

                invalidate()

                Choreographer
                    .getInstance()
                    .postFrameCallback(
                        this
                    )
            }
        }

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

        updateCurrentSkin()
        updateCurrentBoard()

        reset()
    }

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

    fun updateCurrentSkin(id: String? = null) {

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
            Paint.Style.STROKE

        snakePaint.strokeCap =
            Paint.Cap.ROUND

        snakePaint.strokeJoin =
            Paint.Join.ROUND

        snakePaint.strokeWidth = 0f

        headPaint.color = head
    }

    fun updateCurrentBoard(id: String? = null) {

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

    fun reset() {

        snake.clear()
        queue.clear()

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

        /*
         * 极速：固定 16ms
         */
        gameSpeed = 16L
        accumulator = 0L
        lastFrame = 0L

        particles.clear()
        floats.clear()

        flash = 0f

        restartCountdown = 0L

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

        Choreographer
            .getInstance()
            .removeFrameCallback(
                frame
            )
    }

    private fun updateGame() {

        if (gameOver) {
            return
        }

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
            body.indexOf(nh)

        val tail =
            snake.last()

        if (
            hitIndex >= 0 &&
            !(
                nh == tail &&
                    !ate
                )
        ) {

            val simulated =
                simulateOn(
                    ArrayDeque(snake),
                    dir
                )

            val region =
                freeRegion(
                    simulated.body
                )

            if (
                region <
                max(
                    2,
                    (
                        snake.size *
                            safetyMargin
                        ).toInt()
                )
            ) {

                die("TRAP")

            } else {

                die("SELF")
            }

            return
        }

        snake.addFirst(nh)

        if (ate) {

            score +=
                10 +
                    min(
                        combo,
                        20
                    )

            combo++

            hunger = 0
            money++

            if (
                score >
                highScore
            ) {

                highScore =
                    score

                prefs.edit()
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

            prefs.edit()
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

            spawnFoodEffect(nh)

            placeFood()

            /*
             * 极速版不再随长度变慢，
             * 始终 16ms。
             */
            gameSpeed = 16L

        } else {

            snake.removeLast()

            hunger++

            combo =
                max(
                    0,
                    combo - 1
                )

            learn(
                0.025f
            )
        }

        steps++
    }

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

        val autoBeam =
            hunger >= autoBeamHunger

        val scored =
            when (strategy) {

                0 ->
                    legal.maxByOrNull {
                        bfsScore(it)
                    }

                1 ->
                    legal.maxByOrNull {
                        tailScore(it)
                    }

                2 ->
                    legal.maxByOrNull {
                        hamScore(it)
                    }

                else ->
                    beamBest(legal)

            } ?: legal.first()

        val final =
            if (autoBeam) {

                beamBest(legal)

            } else if (
                forcedStrategy >= 0
            ) {

                val fs =
                    forcedStrategy
                        .coerceIn(
                            0,
                            4
                        )

                when (fs) {

                    0 ->
                        legal.maxByOrNull {
                            bfsScore(it)
                        }

                    1 ->
                        legal.maxByOrNull {
                            tailScore(it)
                        }

                    2 ->
                        legal.maxByOrNull {
                            hamScore(it)
                        }

                    4 ->
                        beamBest(legal)

                    else ->
                        legal.first()

                } ?: scored

            } else {

                scored
            }

        val action =
            dirs.indexOfFirst {
                it == final.d
            }.coerceAtLeast(0)

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
                    if (autoBeam)
                        "BEAM 饥饿自动"
                    else
                        strategyName(
                            if (
                                forcedStrategy >= 0
                            )
                                forcedStrategy
                            else
                                strategy
                        ),

                reason =
                    if (autoBeam)
                        "饥饿 $hunger 步未进食，临时切换 BEAM 追食物"
                    else
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

                candidates =
                    candidates,

                depth =
                    if (strategy == 3 || autoBeam)
                        4
                    else
                        2,

                nodes =
                    if (strategy == 3 || autoBeam)
                        beamNodes
                    else
                        candidates.size
            )

        return final.d
    }

    private fun evaluate(
        d: P
    ): Candidate {

        if (
            !legalDirection(d)
        ) {

            return Candidate(
                d,
                -1e9f,
                "撞墙/身体",
                false
            )
        }

        val sim =
            simulate(
                snake.first(),
                d
            )

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

    private fun bfsScore(
        c: Candidate
    ): Float {

        return c.score +
            if (c.d == dir)
                15f
            else
                0f
    }

    private fun tailScore(
        c: Candidate
    ): Float {

        return c.score +
            if (
                tailReachable(
                    simulate(
                        snake.first(),
                        c.d
                    ).body
                )
            ) {

                350f

            } else {

                -500f
            }
    }

    private fun hamScore(
        c: Candidate
    ): Float {

        val idx =
            hamIndex(c.d)

        val next =
            idx >= 0

        return c.score +
            if (next) {

                140f *
                    shortcutBonus

            } else {

                -80f
            }
    }

    private fun beamBest(
        legal: List<Candidate>
    ): Candidate {

        var best =
            legal.maxByOrNull {
                it.score
            } ?: legal.first()

        var bestScore =
            -1e30f

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
                        snake.first(),
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

                if (
                    nod.score >
                    bestScore
                ) {

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

    private fun selectStrategy(
        state: Int,
        danger: Int
    ): Int {

        if (
            forcedStrategy >= 0
        ) {

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

            if (
                ucb > value
            ) {

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
            ++steps % 20 == 0
        ) {
            saveLearning()
        }
    }

    private fun saveLearning() {

        val e =
            prefs.edit()
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
                .putInt(
                    "high_score",
                    highScore
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
            cause == "TRAP"
        ) {

            safetyMargin =
                min(
                    3f,
                    safetyMargin * 1.04f
                )
        }

        lastDeathInfo =
            "死亡=$cause  长度=${snake.size}  分数=$score  " +
                "空间=${ai.region} 需求=${(snake.size * safetyMargin).toInt()}  " +
                "尾巴=${if (ai.tailReachable) "可达" else "不可达"}"

        /*
         * 极速学习：每死一局立刻存盘，
         * 这样即使中途关掉应用，Q 表也不丢。
         */
        saveLearning()

        flash = 1f

        vibrator?.let {

            if (
                Build.VERSION.SDK_INT >= 26
            ) {

                it.vibrate(
                    VibrationEffect.createOneShot(
                        120,
                        VibrationEffect.DEFAULT_AMPLITUDE
                    )
                )

            } else {

                @Suppress("DEPRECATION")

                it.vibrate(120)
            }
        }

        /*
         * 死亡后自动重开倒计时
         * （在 frame 回调里倒计时，无需用户点屏）
         */
        restartCountdown =
            autoRestartDelay

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
                "BFS 食物"

            1 ->
                "TAIL 追尾"

            2 ->
                "HAM 路线"

            3 ->
                "BEAM 前瞻"

            4 ->
                "BEAM 前瞻"

            else ->
                "AUTO"
        }
    }

    private fun simulate(
        head: P,
        d: P
    ): Sim {

        val b =
            ArrayDeque(snake)

        return simulateOn(
            b,
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

            val index =
                p.y * cols +
                    p.x

            if (
                index in 0 until total
            ) {

                bfsVisited[index] =
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
