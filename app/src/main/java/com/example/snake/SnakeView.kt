package com.example.snake

import android.content.Context
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Paint
import android.graphics.Typeface
import android.os.Build
import android.os.VibrationEffect
import android.os.Vibrator
import android.os.VibratorManager
import android.util.AttributeSet
import android.view.Choreographer
import android.view.MotionEvent
import android.view.View
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

/*
 * 0 = 玩家
 * 1 = AI
 * 2 = 特殊 AI
 */
private var aiMode = 1

/*
 * -1 = 自动
 * 0 = BFS
 * 1 = TAIL
 * 2 = HAM
 * 3 = BEAM
 * 4 = BEAM
 */
private var forcedStrategy = -1

private var gameSpeed = 150L
private var accumulator = 0L
private var lastFrame = 0L

private var combo = 0
private var hunger = 0

private var deathCause = "无"
private var lastDeathInfo = ""

private var ai = Snapshot()
private var showDebug = true

/*
 * AI 学习参数
 */
private var aggression = 1.15f
private var safetyMargin = 1.10f
private var shortcutBonus = 0.90f

/*
 * 死亡统计
 */
private var deathWall = 0
private var deathSelf = 0
private var deathTrap = 0
private var totalGames = 0

/*
 * 简单 Q/UCB 学习
 */
private val q = Array(20) { FloatArray(5) }
private val n = Array(20) { IntArray(5) }

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
        (context.getSystemService(
            Context.VIBRATOR_MANAGER_SERVICE
        ) as? VibratorManager)?.defaultVibrator
    } else {
        @Suppress("DEPRECATION")
        context.getSystemService(
            Context.VIBRATOR_SERVICE
        ) as? Vibrator
    }

/*
 * 蛇皮肤
 */
private var bodyColor = Color.rgb(46, 204, 113)
private var headColor = Color.rgb(39, 174, 96)

/*
 * 棋盘
 */
private var bgColor = Color.BLACK
private var gridColor = Color.rgb(0, 255, 255)

private var rainbowSkin = false

private val hsv = IntArray(360) {
    Color.HSVToColor(
        floatArrayOf(
            it.toFloat(),
            1f,
            1f
        )
    )
}

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

private val bfsVisited = BooleanArray(cols * rows)
private val bfsQueue = IntArray(cols * rows)

/*
 * 帧循环
 */
private val frame = object : Choreographer.FrameCallback {

    override fun doFrame(ns: Long) {

        if (!running) return

        if (lastFrame == 0L) {
            lastFrame = ns
        }

        val dt = (
            (ns - lastFrame) / 1_000_000L
            ).coerceAtMost(100L)

        lastFrame = ns
        accumulator += dt

        while (accumulator >= gameSpeed) {
            updateGame()
            accumulator -= gameSpeed
        }

        updateEffects(dt / 16f)

        invalidate()

        Choreographer.getInstance()
            .postFrameCallback(this)
    }
}

init {

    highScore = prefs.getInt(
        "high_score",
        0
    )

    money = prefs.getInt(
        "money",
        0
    )

    aggression = prefs.getFloat(
        "learn_aggression",
        1.15f
    )

    safetyMargin = prefs.getFloat(
        "learn_safety",
        1.10f
    )

    shortcutBonus = prefs.getFloat(
        "learn_shortcut",
        0.90f
    )

    deathWall = prefs.getInt(
        "stat_wall",
        0
    )

    deathSelf = prefs.getInt(
        "stat_self",
        0
    )

    deathTrap = prefs.getInt(
        "stat_trap",
        0
    )

    totalGames = prefs.getInt(
        "stat_total",
        0
    )

    for (s in 0 until 20) {
        for (a in 0 until 5) {

            q[s][a] = prefs.getFloat(
                "q_${s}_$a",
                0f
            )

            n[s][a] = prefs.getInt(
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

fun setAIMode(m: Int) {
    aiMode = m
    reset()
}

fun setForcedStrategy(s: Int) {
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
                Color.rgb(52, 152, 219),
                Color.rgb(41, 128, 185),
                false
            )
        }

        "red" -> {
            setSnakeColors(
                Color.rgb(231, 76, 60),
                Color.rgb(192, 57, 43),
                false
            )
        }

        "purple" -> {
            setSnakeColors(
                Color.rgb(155, 89, 182),
                Color.rgb(142, 68, 173),
                false
            )
        }

        "gold" -> {
            setSnakeColors(
                Color.rgb(241, 196, 15),
                Color.rgb(243, 156, 18),
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
                Color.rgb(46, 204, 113),
                Color.rgb(39, 174, 96),
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
    snakePaint.style = Paint.Style.STROKE
    snakePaint.strokeCap = Paint.Cap.ROUND
    snakePaint.strokeJoin = Paint.Join.ROUND
    snakePaint.strokeWidth = 0f

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
            bgColor = Color.rgb(
                240,
                240,
                240
            )

            gridColor = Color.rgb(
                200,
                200,
                200
            )
        }

        "neon" -> {
            bgColor = Color.rgb(
                10,
                25,
                47
            )

            gridColor = Color.CYAN
        }

        "forest" -> {
            bgColor = Color.rgb(
                27,
                46,
                26
            )

            gridColor = Color.rgb(
                46,
                74,
                45
            )
        }

        "cyberpunk" -> {
            bgColor = Color.rgb(
                43,
                15,
                59
            )

            gridColor = Color.MAGENTA
        }

        "rainbow_board" -> {
            bgColor = Color.BLACK
            gridColor = Color.WHITE
        }

        else -> {
            bgColor = Color.BLACK
            gridColor = Color.CYAN
        }
    }

    invalidate()
}

fun reset() {

    snake.clear()
    queue.clear()

    if (aiMode == 2) {

        snake.add(
            P(0, 0)
        )

        dir = P(0, 1)

    } else {

        snake.add(
            P(
                cols / 2,
                rows / 2
            )
        )

        dir = P(1, 0)
    }

    score = 0
    combo = 0
    hunger = 0

    gameOver = false

    deathCause = "无"
    lastDeathInfo = ""

    gameSpeed = 150L

    accumulator = 0L
    lastFrame = 0L

    particles.clear()
    floats.clear()

    flash = 0f

    ai = Snapshot(
        chosen = dir
    )

    placeFood()

    onScoreChanged?.invoke(score)

    invalidate()
}

fun resume() {

    if (running) return

    running = true
    lastFrame = 0L

    Choreographer
        .getInstance()
        .postFrameCallback(frame)
}

fun pause() {

    running = false

    Choreographer
        .getInstance()
        .removeFrameCallback(frame)
}

private fun updateGame() {

    if (gameOver) return

    if (aiMode != 0) {

        val chosen = chooseMove()

        queue.clear()
        queue.add(chosen)
    }

    if (queue.isNotEmpty()) {

        val requested =
            queue.removeFirst()

        if (
            !isReverse(
                requested,
                dir
            ) &&
            legalDirection(requested)
        ) {
            dir = requested
        }
    }

    if (dir == P(0, 0)) return

    val nh = P(
        snake.first().x + dir.x,
        snake.first().y + dir.y
    )

    if (!inside(nh)) {
        die("WALL")
        return
    }

    val ate = nh == food
    val body = snake.toList()
    val hitIndex = body.indexOf(nh)
    val tail = snake.last()

    if (
        hitIndex >= 0 &&
        !(nh == tail && !ate)
    ) {

        val simulated =
            simulate(
                nh,
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
                (snake.size * safetyMargin).toInt()
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

        score += 10 + min(
            combo,
            20
        )

        combo++
        hunger = 0

        money++

        if (score > highScore) {

            highScore = score

            prefs.edit()
                .putInt(
                    "high_score",
                    highScore
                )
                .apply()
        }

        onScoreChanged?.invoke(score)
        onMoneyChanged?.invoke(money)

        prefs.edit()
            .putInt(
                "money",
                money
            )
            .apply()

        learn(
            2.5f +
                    combo * 0.05f
        )

        spawnFoodEffect(nh)

        placeFood()

        gameSpeed = max(
            65L,
            150L -
                    (snake.size / 8) * 5L
        )

    } else {

        snake.removeLast()

        hunger++

        combo = max(
            0,
            combo - 1
        )

        learn(0.025f)
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

        ai = Snapshot(
            strategy = "NO MOVE",
            reason = "四个方向都无法安全前进",
            danger = 5,
            chosen = dir,
            candidates = candidates
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

    val scored =
        when (strategy) {

            0 -> {
                legal.maxByOrNull {
                    bfsScore(it)
                }
            }

            1 -> {
                legal.maxByOrNull {
                    tailScore(it)
                }
            }

            2 -> {
                legal.maxByOrNull {
                    hamScore(it)
                }
            }

            else -> {
                beamBest(legal)
            }
        }
            ?: legal.first()

    val final =
        if (forcedStrategy >= 0) {

            val fs =
                forcedStrategy.coerceIn(
                    0,
                    4
                )

            when (fs) {

                0 -> {
                    legal.maxByOrNull {
                        bfsScore(it)
                    }
                }

                1 -> {
                    legal.maxByOrNull {
                        tailScore(it)
                    }
                }

                2 -> {
                    legal.maxByOrNull {
                        hamScore(it)
                    }
                }

                4 -> {
                    beamBest(legal)
                }

                else -> {
                    legal.first()
                }
            }
                ?: scored

        } else {
            scored
        }

    val action =
        dirs.indexOfFirst {
            it == final.d
        }.coerceAtLeast(0)

    lastState = state
    lastAction = action

    val reason =
        reasonFor(
            final,
            strategy,
            danger
        )

    val region =
        freeRegion(snake)

    val foodDistance =
        distance(
            snake.first(),
            food,
            snake,
            allowTail = true
        )

    ai = Snapshot(

        strategy =
            strategyName(
                if (forcedStrategy >= 0)
                    forcedStrategy
                else
                    strategy
            ),

        reason = reason,

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
            if (strategy == 3)
                4
            else
                2,

        nodes =
            if (strategy == 3)
                beamNodes
            else
                candidates.size
    )

    return final.d
}

private var beamNodes = 0

private fun evaluate(
    d: P
): Candidate {

    if (!legalDirection(d)) {

        return Candidate(
            d = d,
            score = -1e9f,
            reason = "撞墙/身体",
            legal = false
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
            allowTail = true
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
                                    (foodDist + 1)
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

    s -=
        max(
            0,
            (
                    snake.size *
                            safetyMargin -
                            region
                    )
        ) * 30f

    return Candidate(

        d = d,

        score = s,

        reason =
            if (ate) {
                "马上吃到食物"
            } else if (tail) {
                "保持尾巴可达"
            } else {
                "扩大可用空间"
            },

        legal = true
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
        }
            ?: legal.first()

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
                body =
                    simulate(
                        snake.first(),
                        it.d
                    ).body,

                first = it.d,

                score = it.score,

                depth = 1
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
                        allowTail = true
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
                                (fd + 1)
                }

                if (sm.ate) {
                    sc += 500f
                }

                next.add(
                    Node(
                        body = sm.body,
                        first = nod.first,
                        score = sc,
                        depth = nod.depth + 1
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

    if (forcedStrategy >= 0) {

        return forcedStrategy
            .coerceIn(0, 4)
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

            if (snake.size < 35)
                1.2f + hungerBias
            else
                .5f,

            1f + dangerBias,

            if (snake.size >= 35)
                1.8f
            else
                .4f,

            if (snake.size < 100)
                1.3f
            else
                .7f,

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
            len < 25 -> 0
            len < 50 -> 1
            len < 85 -> 2
            else -> 3
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
            n[s][a] < 10 -> .20f
            n[s][a] < 50 -> .10f
            else -> .04f
        }

    q[s][a] +=
        alpha *
                (
                        reward -
                                q[s][a]
                        )

    n[s][a]++

    if (++steps % 20 == 0) {
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
                    .5f,
                    aggression * .97f
                )

            "SELF" ->
                max(
                    .5f,
                    aggression * .99f
                )

            else ->
                max(
                    .5f,
                    aggression * .94f
                )
        }

    if (cause == "TRAP") {

        safetyMargin =
            min(
                3f,
                safetyMargin * 1.04f
            )
    }

    lastDeathInfo =
        "死亡=$cause  " +
                "长度=${snake.size}  " +
                "分数=$score  " +
                "空间=${ai.region}  " +
                "需求=${(snake.size * safetyMargin).toInt()}  " +
                "尾巴=${if (ai.tailReachable) "可达" else "不可达"}"

    saveLearning()

    flash = 1f

    vibrator?.let {

        if (Build.VERSION.SDK_INT >= 26) {

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

        0 -> "BFS 食物"

        1 -> "TAIL 追尾"

        2 -> "HAM 路线"

        3 -> "BEAM 前瞻"

        4 -> "BEAM 前瞻"

        else -> "AUTO"
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

    val nh =
        P(
            b.first().x + d.x,
            b.first().y + d.y
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
        !(nh == b.last() && !ate)
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

    return d != P(0, 0) &&
            !isReverse(d, dir) &&
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

    java.util.Arrays.fill(
        bfsVisited,
        false
    )

    for (p in body) {

        bfsVisited[
            p.y * cols + p.x
        ] = true
    }

    val start =
        body.first()

    bfsVisited[
        start.y * cols + start.x
    ] = false

    var head = 0
    var tail = 1

    bfsQueue[0] =
        start.y * cols +
                start.x

    var count = 0

    while (head < tail) {

        val curr =
            bfsQueue[head++]

        val cx =
            curr % cols

        val cy =
            curr / cols

        count++

        if (cx > 0) {

            val nx =
                curr - 1

            if (!bfsVisited[nx]) {

                bfsVisited[nx] = true
                bfsQueue[tail++] = nx
            }
        }

        if (cx < cols - 1) {

            val nx =
                curr + 1

            if (!bfsVisited[nx]) {

                bfsVisited[nx] = true
                bfsQueue[tail++] = nx
            }
        }

        if (cy > 0) {

            val nx =
                curr - cols

            if (!bfsVisited[nx]) {

                bfsVisited[nx] = true
                bfsQueue[tail++] = nx
            }
        }

        if (cy < rows - 1) {

            val nx =
                curr + cols

            if (!bfsVisited[nx]) {

                bfsVisited[nx] = true
                bfsQueue[tail++] = nx
            }
        }
    }

    return count
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
                                        nh == body.last() &&
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

    val target =
        body.last()

    return distance(
        body.first(),
        target,
        body,
        allowTail = true
    ) >= 0
}

private fun distance(
    start: P,
    target: P,
    body: Collection<P>,
    allowTail: Boolean
): Int {

    if (start == target) {
        return 0
    }

    java.util.Arrays.fill(
        bfsVisited,
        false
    )

    for (p in body) {

        bfsVisited[
            p.y * cols + p.x
        ] = true
    }

    if (
        allowTail &&
        body.isNotEmpty()
    ) {

        val last =
            body.last()

        bfsVisited[
            last.y * cols + last.x
        ] = false
    }

    bfsVisited[
        start.y * cols + start.x
    ] = false

    var head = 0
    var tail = 1

    bfsQueue[0] =
        start.y * cols +
                start.x

    var dist = 0

    while (head < tail) {

        val layerSize =
            tail - head

        repeat(layerSize) {

            val curr =
                bfsQueue[head++]

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

            if (cx > 0) {

                val nx =
                    curr - 1

                if (!bfsVisited[nx]) {

                    bfsVisited[nx] = true
                    bfsQueue[tail++] = nx
                }
            }

            if (cx < cols - 1) {

                val nx =
                    curr + 1

                if (!bfsVisited[nx]) {

                    bfsVisited[nx] = true
                    bfsQueue[tail++] = nx
                }
            }

            if (cy > 0) {

                val nx =
                    curr - cols

                if (!bfsVisited[nx]) {

                    bfsVisited[nx] = true
                    bfsQueue[tail++] = nx
                }
            }

            if (cy < rows - 1) {

                val nx =
                    curr + cols

                if (!bfsVisited[nx]) {

                    bfsVisited[nx] = true
                    bfsQueue[tail++] = nx
                }
            }
        }

        dist++
    }

    return -1
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

private fun hamIndex(
    d: P
): Int {

    val h =
        snake.first()

    val n =
        P(
            h.x + d.x,
            h.y + d.y
        )

    if (!inside(n)) {
        return -1
    }

    val x = n.x
    val y = n.y

    return x * rows + y
}

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

private fun spawnFoodEffect(
    p: P
) {

    repeat(14) {

        particles.add(
            Particle(
                x = p.x.toFloat(),
                y = p.y.toFloat(),
                vx = Random.nextFloat() - .5f,
                vy = Random.nextFloat() - .5f,
                life = 1f,
                color = Color.YELLOW
            )
        )
    }

    floats.add(
        FloatText(
            x = p.x.toFloat(),
            y = p.y.toFloat(),
            life = 1f,
            text = "+10"
        )
    )
}

private fun updateEffects(
    dt: Float
) {

    flash =
        max(
            0f,
            flash - dt * .035f
        )

    particles.forEach {

        it.x +=
            it.vx * dt

        it.y +=
            it.vy * dt

        it.life -=
            dt * .035f
    }

    particles.removeAll {
        it.life <= 0
    }

    floats.forEach {

        it.y -=
            dt * .04f

        it.life -=
            dt * .025f
    }

    floats.removeAll {
        it.life <= 0
    }
}

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
        (w - cols * cell) / 2f

    oy =
        (h - rows * cell) / 2f
}

override fun onDraw(
    c: Canvas
) {

    super.onDraw(c)

    c.drawColor(bgColor)

    gridPaint.color =
        gridColor

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

    drawFood(c)
    drawSnake(c)
    drawParticles(c)
    drawDebug(c)

    if (gameOver) {
        drawGameOver(c)
    }
}

private fun drawFood(
    c: Canvas
) {

    val cx =
        ox +
                (food.x + .5f) *
                cell

    val cy =
        oy +
                (food.y + .5f) *
                cell

    foodPaint.color =
        Color.argb(
            90,
            255,
            80,
            80
        )

    c.drawCircle(
        cx,
        cy,
        cell * .38f,
        foodPaint
    )

    foodPaint.color =
        Color.RED

    c.drawCircle(
        cx,
        cy,
        cell * .22f,
        foodPaint
    )

    foodPaint.color =
        Color.WHITE

    c.drawCircle(
        cx,
        cy,
        cell * .07f,
        foodPaint
    )
}

private fun drawSnake(
    c: Canvas
) {

    if (snake.isEmpty()) {
        return
    }

    snakePaint.strokeWidth =
        max(
            8f,
            cell * .62f
        )

    val list =
        snake.toList()

    for (i in 0 until list.size - 1) {

        val a =
            list[i]

        val b =
            list[i + 1]

        if (rainbowSkin) {

            snakePaint.color =
                hsv[
                    (i * 23 + score) % 360
                ]

        } else {

            snakePaint.color =
                bodyColor
        }

        c.drawLine(

            ox +
                    (a.x + .5f) *
                    cell,

            oy +
                    (a.y + .5f) *
                    cell,

            ox +
                    (b.x + .5f) *
                    cell,

            oy +
                    (b.y + .5f) *
                    cell,

            snakePaint
        )
    }

    val h =
        snake.first()

    headPaint.color =
        headColor

    c.drawCircle(

        ox +
                (h.x + .5f) *
                cell,

        oy +
                (h.y + .5f) *
                cell,

        cell * .36f,

        headPaint
    )

    val ex =
        when {

            dir.x > 0 ->
                .12f

            dir.x < 0 ->
                -.12f

            else ->
                0f
        }

    val ey =
        when {

            dir.y > 0 ->
                .12f

            dir.y < 0 ->
                -.12f

            else ->
                0f
        }

    paint.color =
        Color.WHITE

    c.drawCircle(

        ox +
                (h.x + .5f) *
                cell +
                cell * (.13f + ex),

        oy +
                (h.y + .5f) *
                cell +
                cell * (.13f + ey),

        cell * .075f,

        paint
    )

    c.drawCircle(

        ox +
                (h.x + .5f) *
                cell -
                cell * (.13f - ex),

        oy +
                (h.y + .5f) *
                cell -
                cell * (.13f - ey),

        cell * .075f,

        paint
    )
}

private fun drawParticles(
    c: Canvas
) {

    particles.forEach {

        paint.color =
            Color.argb(

                (
                        it.life * 255
                        )
                    .toInt()
                    .coerceIn(
                        0,
                        255
                    ),

                Color.red(it.color),
                Color.green(it.color),
                Color.blue(it.color)
            )

        c.drawCircle(

            ox +
                    (it.x + .5f) *
                    cell,

            oy +
                    (it.y + .5f) *
                    cell,

            max(
                2f,
                cell * .05f
            ),

            paint
        )
    }

    text.textAlign =
        Paint.Align.CENTER

    text.textSize =
        cell * .3f

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
                    (it.x + .5f) *
                    cell,

            oy +
                    (it.y + .3f) *
                    cell,

            text
        )
    }
}

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
            width * .94f,
            520f
        )

    val h =
        if (gameOver)
            220f
        else
            205f

    val left =
        width -
                w -
                12f

    val top =
        if (gameOver)
            height -
                    h -
                    12f
        else
            12f

    panel.color =
        Color.argb(
            205,
            0,
            0,
            0
        )

    c.drawRoundRect(
        left,
        top,
        left + w,
        top + h,
        18f,
        18f,
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
        3f

    c.drawRoundRect(
        left,
        top,
        left + w,
        top + h,
        18f,
        18f,
        border
    )

    /*
     * 这里就是修复原来
     * isFakeBoldText 报错的地方。
     */
    text.textAlign =
        Paint.Align.LEFT

    text.typeface =
        Typeface.DEFAULT_BOLD

    text.textSize =
        16f

    text.color =
        Color.WHITE

    c.drawText(
        "🧠 AI  ${ai.strategy}",
        left + 12,
        top + 24,
        text
    )

    /*
     * 恢复普通字体
     */
    text.typeface =
        Typeface.DEFAULT

    text.textSize =
        12f

    text.color =
        Color.YELLOW

    c.drawText(
        "正在判断：${ai.reason}",
        left + 12,
        top + 43,
        text
    )

    text.color =
        Color.WHITE

    c.drawText(

        "危险 ${
            "●".repeat(
                ai.danger
            )
        }${
            "○".repeat(
                5 - ai.danger
            )
        }   " +
                "空间 ${ai.region}   " +
                "比例 ${
                    "%.1f".format(
                        ai.spaceRatio
                    )
                }",

        left + 12,
        top + 61,
        text
    )

    c.drawText(

        "尾巴 ${
            if (ai.tailReachable)
                "✓ 可达"
            else
                "✗ 不可达"
        }   " +

                "食物 ${
                    if (ai.foodReachable)
                        "✓ 可达"
                    else
                        "✗ 不可达"
                }   " +

                "距离 ${
                    if (ai.foodDistance < 0)
                        "∞"
                    else
                        ai.foodDistance
                }",

        left + 12,
        top + 78,
        text
    )

    c.drawText(

        "长度 ${snake.size}   " +
                "饥饿 $hunger   " +
                "分数 $score   " +
                "学习局数 $totalGames",

        left + 12,
        top + 95,
        text
    )

    c.drawText(

        "探索深度 ${ai.depth}   " +
                "节点 ${ai.nodes}   " +
                "α/攻 ${
                    "%.2f".format(
                        aggression
                    )
                }",

        left + 12,
        top + 112,
        text
    )

    text.textSize =
        11f

    var x =
        left + 12f

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
            top + 132,
            text
        )

        x +=
            w / 4f
    }

    text.color =
        Color.CYAN

    c.drawText(

        "选择  ${arrow(ai.chosen)}     " +
                "死亡统计 " +
                "W$deathWall " +
                "S$deathSelf " +
                "T$deathTrap",

        left + 12,
        top + 150,
        text
    )

    text.color =
        Color.LTGRAY

    c.drawText(

        "学习：Q/UCB + 多步前瞻；死亡后自动调整安全策略",

        left + 12,
        top + 168,
        text
    )

    if (gameOver) {

        text.color =
            Color.RED

        text.typeface =
            Typeface.DEFAULT_BOLD

        text.textSize =
            15f

        c.drawText(

            "死亡原因：$deathCause",

            left + 12,
            top + 190,
            text
        )

        text.typeface =
            Typeface.DEFAULT
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

    text.typeface =
        Typeface.DEFAULT_BOLD

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

    text.typeface =
        Typeface.DEFAULT

    c.drawText(

        "分数 $score   " +
                "最高 $highScore   " +
                "长度 ${snake.size}",

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
                                (snake.first().x + .5f) *
                                cell
                        )

    val dy =
        e.y -
                (
                        oy +
                                (snake.first().y + .5f) *
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
