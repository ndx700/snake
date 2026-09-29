package com.example.snake

import android.content.Context
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.LinearGradient
import android.graphics.Matrix
import android.graphics.Paint
import android.graphics.Path
import android.graphics.PointF
import android.graphics.CornerPathEffect
import android.graphics.RadialGradient
import android.graphics.Shader
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
import kotlin.math.sin
import kotlin.math.cos
import kotlin.math.atan2
import kotlin.random.Random

class SnakeView @JvmOverloads constructor(
    context: Context, attrs: AttributeSet? = null
) : View(context, attrs) {

    private val cols = 15
    private val rows = 15
    private var cellSize = 0f
    private var offsetX = 0f
    private var offsetY = 0f

    private data class Point(val x: Int, val y: Int)
    private data class BeamNode(val firstDir: Point, val simSnake: ArrayDeque<Point>, val foodCount: Int)
    private data class Decision(val strategy: Int, val reason: String)

    private val snake = ArrayDeque<Point>()
    private val directionQueue = ArrayDeque<Point>()
    private var dir = Point(0, 0)
    private var food = Point(5, 5)
    private var score = 0
    private var highScore = 0
    private var gameOver = false
    private var running = false
    private var gameSpeed = 180L
    private var aiMode = 0

    var onScoreChanged: ((Int) -> Unit)? = null
    var onMoneyChanged: ((Int) -> Unit)? = null

    private val prefs = context.getSharedPreferences("snake_prefs", Context.MODE_PRIVATE)
    private var comboCount = 0
    private var hungerCounter = 0
    private var foodUnreachableStreak = 0

    // ===== 学习参数：这些值会随死亡变化，影响决策 =====
    private var aggression = 1.0f       // 激进程度：食物吸引力倍数
    private var safetyMargin = 1.2f     // 安全余量：危险判定的严格程度
    private var shortcutBonus = 1.0f    // 抄近道倍数：HAM 抄近道距离
    private var deathByWall = 0
    private var deathBySelf = 0
    private var deathByTrap = 0
    private var totalGames = 0
    private var lastDeathInfo = ""

    private var forcedStrategy = -1
    private var strategyMode = 0
    private var lastReason = "初始化"

    private val pathIndex = Array(cols) { IntArray(rows) }
    private val pathSequence = mutableListOf<Point>()

    private var bodyColor = Color.rgb(46, 204, 113)
    private var headColor = Color.rgb(39, 174, 96)
    private var bgColor = Color.BLACK
    private var gridColor = Color.rgb(0, 255, 255)
    private var isRainbowSkin = false
    private val rainbow = IntArray(361) { Color.HSVToColor(floatArrayOf(it.toFloat(), 1f, 1f)) }

    private val vibrator: Vibrator? = if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
        (context.getSystemService(Context.VIBRATOR_MANAGER_SERVICE) as? VibratorManager)?.defaultVibrator
    } else {
        @Suppress("DEPRECATION")
        context.getSystemService(Context.VIBRATOR_SERVICE) as? Vibrator
    }

    private var deathFlashAlpha = 0f
    private var shakeTime = 0f
    private var shakeOffsetX = 0f
    private var shakeOffsetY = 0f
    private var shockwaveRadius = 0f
    private var shockwaveAlpha = 0f
    private var shockwaveX = 0f
    private var shockwaveY = 0f

    private data class Particle(
        var x: Float, var y: Float, var vx: Float, var vy: Float,
        var life: Float, val color: Int, var size: Float, var decay: Float,
        var isTrail: Boolean = false
    )
    private data class FloatText(var x: Float, var y: Float, var life: Float, val text: String)

    private val particles = mutableListOf<Particle>()
    private val floats = mutableListOf<FloatText>()

    private val ffVisited = Array(cols) { BooleanArray(rows) }
    private val ffQueue = IntArray(cols * rows + 10)
    private val bfsVisited = Array(cols) { BooleanArray(rows) }
    private val bfsParentX = Array(cols) { IntArray(rows) }
    private val bfsParentY = Array(cols) { IntArray(rows) }
    private val bfsQueue = IntArray(cols * rows + 10)

    private val pathBuf = Path()
    private val pointsBuf = Array(300) { PointF() }
    private val dirsList = listOf(Point(0, -1), Point(0, 1), Point(-1, 0), Point(1, 0))

    private val paintSnakeBody = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = bodyColor; style = Paint.Style.STROKE
        strokeCap = Paint.Cap.ROUND; strokeJoin = Paint.Join.ROUND
        pathEffect = CornerPathEffect(30f); setShadowLayer(20f, 0f, 0f, bodyColor)
    }
    private val paintSnakeHead = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = headColor; style = Paint.Style.FILL; setShadowLayer(15f, 0f, 0f, headColor)
    }
    private val paintHighlight = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.WHITE; style = Paint.Style.FILL; alpha = 100
    }
    private val paintEyeW = Paint(Paint.ANTI_ALIAS_FLAG).apply { color = Color.WHITE }
    private val paintEyeB = Paint(Paint.ANTI_ALIAS_FLAG).apply { color = Color.BLACK }
    private val paintFoodGlow = Paint(Paint.ANTI_ALIAS_FLAG)
    private val paintFoodCore = Paint(Paint.ANTI_ALIAS_FLAG).apply { color = Color.WHITE }
    private val paintFoodCross = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.WHITE; style = Paint.Style.STROKE; strokeWidth = 3f
        setShadowLayer(15f, 0f, 0f, Color.CYAN)
    }
    private val paintParticle = Paint(Paint.ANTI_ALIAS_FLAG)
    private val paintFloat = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.rgb(241, 196, 15); textSize = 45f; textAlign = Paint.Align.CENTER
        setShadowLayer(10f, 0f, 0f, Color.BLACK)
    }
    private val paintGrid = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        strokeWidth = 2f; setShadowLayer(8f, 0f, 0f, Color.CYAN)
    }
    private val paintShock = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        style = Paint.Style.STROKE; strokeWidth = 8f; color = Color.RED
    }
    private val paintText = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.WHITE; textAlign = Paint.Align.CENTER
    }
    private val paintSubText = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.LTGRAY; textAlign = Paint.Align.CENTER
    }
    private val paintHamPath = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        style = Paint.Style.STROKE; strokeWidth = 3f; color = Color.argb(60, 255, 255, 255)
    }
    private val paintPanelBg = Paint(Paint.ANTI_ALIAS_FLAG).apply { color = Color.argb(180, 0, 0, 0) }
    private val paintPanelBorder = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        style = Paint.Style.STROKE; strokeWidth = 3f
    }
    private val paintModeName = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        textSize = 22f; textAlign = Paint.Align.CENTER; isFakeBoldText = true
    }
    private val paintModeDesc = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.WHITE; textSize = 13f; textAlign = Paint.Align.CENTER
    }
    private val paintReason = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.rgb(255, 215, 0); textSize = 13f; textAlign = Paint.Align.LEFT
    }
    private val paintLearn = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.rgb(120, 255, 180); textSize = 12f; textAlign = Paint.Align.LEFT
    }
    private val paintBoardBg = Paint(Paint.ANTI_ALIAS_FLAG)
    private val boardMatrix = Matrix()

    private var lastFrameTime = 0L
    private var timeAccumulator = 0L

    private val frameCallback = object : Choreographer.FrameCallback {
        override fun doFrame(ns: Long) {
            if (!running) return
            val now = System.nanoTime()
            if (lastFrameTime == 0L) lastFrameTime = now
            val dt = (now - lastFrameTime) / 1_000_000f
            lastFrameTime = now
            timeAccumulator += dt.toLong()
            if (timeAccumulator >= gameSpeed) { update(); timeAccumulator -= gameSpeed }
            updateEffects(dt)
            invalidate()
            Choreographer.getInstance().postFrameCallback(this)
        }
    }

    init {
        initHamPath()
        loadAllPrefs()
        updateCurrentSkin()
        updateCurrentBoard()
        reset()
    }

    private fun initHamPath() {
        pathSequence.clear()
        for (c in 0 until cols) {
            if (c % 2 == 0) for (r in 0 until rows) { pathIndex[c][r] = pathSequence.size; pathSequence.add(Point(c, r)) }
            else for (r in rows - 1 downTo 0) { pathIndex[c][r] = pathSequence.size; pathSequence.add(Point(c, r)) }
        }
    }

    private fun loadAllPrefs() {
        highScore = prefs.getInt("high_score", 0)
        aggression = prefs.getFloat("learn_aggression", 1.0f)
        safetyMargin = prefs.getFloat("learn_safety", 1.2f)
        shortcutBonus = prefs.getFloat("learn_shortcut", 1.0f)
        deathByWall = prefs.getInt("stat_wall", 0)
        deathBySelf = prefs.getInt("stat_self", 0)
        deathByTrap = prefs.getInt("stat_trap", 0)
        totalGames = prefs.getInt("stat_total", 0)
    }

    private fun saveLearning() {
        prefs.edit()
            .putFloat("learn_aggression", aggression)
            .putFloat("learn_safety", safetyMargin)
            .putFloat("learn_shortcut", shortcutBonus)
            .putInt("stat_wall", deathByWall)
            .putInt("stat_self", deathBySelf)
            .putInt("stat_trap", deathByTrap)
            .putInt("stat_total", totalGames)
            .apply()
    }

    fun getAIMode() = aiMode
    fun setAIMode(m: Int) { aiMode = m; reset() }
    fun setForcedStrategy(s: Int) { forcedStrategy = s }

    fun updateCurrentSkin() {
        val id = prefs.getString("equipped_skin", "green") ?: "green"
        isRainbowSkin = false
        when (id) {
            "blue" -> { bodyColor = Color.rgb(52, 152, 219); headColor = Color.rgb(41, 128, 185) }
            "red" -> { bodyColor = Color.rgb(231, 76, 60); headColor = Color.rgb(192, 57, 43) }
            "purple" -> { bodyColor = Color.rgb(155, 89, 182); headColor = Color.rgb(142, 68, 173) }
            "gold" -> { bodyColor = Color.rgb(241, 196, 15); headColor = Color.rgb(243, 156, 18) }
            "rainbow" -> {
                isRainbowSkin = true; bodyColor = Color.WHITE; headColor = Color.WHITE
                paintSnakeBody.setShadowLayer(35f, 0f, 0f, Color.WHITE)
            }
            else -> { bodyColor = Color.rgb(46, 204, 113); headColor = Color.rgb(39, 174, 96) }
        }
        if (!isRainbowSkin) {
            paintSnakeBody.shader = null; paintSnakeBody.color = bodyColor
            paintSnakeBody.setShadowLayer(20f, 0f, 0f, bodyColor)
            paintSnakeHead.color = headColor; paintSnakeHead.setShadowLayer(15f, 0f, 0f, headColor)
        }
        invalidate()
    }

    fun updateCurrentBoard() {
        val id = prefs.getString("equipped_board", "dark") ?: "dark"
        when (id) {
            "light" -> { bgColor = Color.rgb(240, 240, 240); gridColor = Color.rgb(200, 200, 200); paintGrid.setShadowLayer(0f, 0f, 0f, Color.TRANSPARENT) }
            "neon" -> { bgColor = Color.rgb(10, 25, 47); gridColor = Color.rgb(0, 255, 255); paintGrid.setShadowLayer(8f, 0f, 0f, Color.CYAN) }
            "forest" -> { bgColor = Color.rgb(27, 46, 26); gridColor = Color.rgb(46, 74, 45); paintGrid.setShadowLayer(0f, 0f, 0f, Color.TRANSPARENT) }
            "cyberpunk" -> { bgColor = Color.rgb(43, 15, 59); gridColor = Color.rgb(200, 0, 255); paintGrid.setShadowLayer(8f, 0f, 0f, Color.MAGENTA) }
            "rainbow_board" -> {
                bgColor = Color.BLACK; gridColor = Color.WHITE
                paintGrid.setShadowLayer(6f, 0f, 0f, Color.WHITE)
                paintBoardBg.shader = LinearGradient(0f, 0f, 2000f, 2000f, rainbow, null, Shader.TileMode.MIRROR)
            }
            else -> { bgColor = Color.BLACK; gridColor = Color.rgb(0, 255, 255); paintGrid.setShadowLayer(8f, 0f, 0f, Color.CYAN) }
        }
        invalidate()
    }

    fun reset() {
        snake.clear()
        if (aiMode == 2) { snake.add(Point(0, 0)); dir = Point(0, 1) }
        else { snake.add(Point(10, 10)); dir = Point(0, 0) }
        directionQueue.clear()
        score = 0; comboCount = 0; hungerCounter = 0; foodUnreachableStreak = 0
        gameOver = false; gameSpeed = 180L
        lastFrameTime = 0L; timeAccumulator = 0L
        deathFlashAlpha = 0f; shakeTime = 0f; shakeOffsetX = 0f; shakeOffsetY = 0f
        shockwaveRadius = 0f; shockwaveAlpha = 0f
        strategyMode = 0
        lastReason = "重新开始"
        particles.clear(); floats.clear()
        if (isRainbowSkin) paintSnakeBody.setShadowLayer(35f, 0f, 0f, Color.WHITE)
        else {
            paintSnakeBody.color = bodyColor
            paintSnakeBody.setShadowLayer(20f, 0f, 0f, bodyColor)
            paintSnakeHead.color = headColor
            paintSnakeHead.setShadowLayer(15f, 0f, 0f, headColor)
        }
        placeFood()
        onScoreChanged?.invoke(score)
        invalidate()
    }

    fun resume() {
        if (!running) {
            running = true; lastFrameTime = 0L; timeAccumulator = 0L
            Choreographer.getInstance().postFrameCallback(frameCallback)
        }
    }

    fun pause() {
        running = false
        Choreographer.getInstance().removeFrameCallback(frameCallback)
    }

    private fun placeFood() {
        var att = 0
        while (att < 1000) {
            val p = Point(Random.nextInt(cols), Random.nextInt(rows))
            if (snake.none { it.x == p.x && it.y == p.y }) { food = p; return }
            att++
        }
    }

    private fun vibrate(ms: Long) {
        vibrator?.let {
            if (!it.hasVibrator()) return
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O)
                it.vibrate(VibrationEffect.createOneShot(ms, VibrationEffect.DEFAULT_AMPLITUDE))
            else @Suppress("DEPRECATION") it.vibrate(ms)
        }
    }

    private fun updateEffects(dt: Float) {
        if (gameOver) {
            deathFlashAlpha = 120f + 60f * sin(System.currentTimeMillis() / 150.0).toFloat()
            if (shockwaveAlpha > 0) { shockwaveRadius += dt * 1.5f; shockwaveAlpha -= dt * 0.15f }
        } else if (deathFlashAlpha > 0) deathFlashAlpha = max(0f, deathFlashAlpha - dt * 0.5f)
        if (shakeTime > 0) {
            shakeTime -= dt
            shakeOffsetX = (Random.nextFloat() - 0.5f) * 30f * (shakeTime / 400f)
            shakeOffsetY = (Random.nextFloat() - 0.5f) * 30f * (shakeTime / 400f)
        } else { shakeOffsetX = 0f; shakeOffsetY = 0f }
        val it = particles.iterator()
        while (it.hasNext()) {
            val p = it.next()
            p.x += p.vx * (dt / 16f); p.y += p.vy * (dt / 16f)
            if (!p.isTrail) p.vy += 0.4f
            p.life -= dt * p.decay
            if (p.life <= 0) it.remove()
        }
        val ti = floats.iterator()
        while (ti.hasNext()) {
            val t = ti.next()
            t.y -= 2.5f * (dt / 16f); t.life -= dt * 0.001f
            if (t.life <= 0) ti.remove()
        }
    }

    // ============================================================
    // ============ 学习系统：死因分析 + 参数进化 ============
    // ============================================================

    /**
     * 根据死因调整学习参数。
     * 死因由 update() 在死亡发生的瞬间判定后传入，不再事后反推：
     *   WALL 撞墙（蛇头越界）
     *   SELF 撞自己（剩余空间充裕）
     *   TRAP 被围死（剩余空间 < 蛇长 * 1.2）
     *
     * 参数调整规则：
     *   WALL → 更保守（激进↓，抄近道↓）
     *   SELF → 更保守（安全余量↑）
     *   TRAP → 更保守（安全余量↑，激进↓）
     *   高分 → 奖励（激进↑，抄近道↑）
     *   速死 → 惩罚（激进↓）
     */
    private fun analyzeAndLearn(cause: String) {
        when (cause) {
            "WALL" -> {
                deathByWall++
                aggression = (aggression * 0.88f).coerceAtLeast(0.5f)
                shortcutBonus = (shortcutBonus * 0.93f).coerceAtLeast(0.5f)
                lastDeathInfo = "撞墙死了 → 激进↓ 抄近道↓"
            }
            "SELF" -> {
                deathBySelf++
                safetyMargin = (safetyMargin * 1.10f).coerceAtMost(3.0f)
                lastDeathInfo = "撞自己了 → 安全余量↑"
            }
            "TRAP" -> {
                deathByTrap++
                safetyMargin = (safetyMargin * 1.15f).coerceAtMost(3.0f)
                aggression = (aggression * 0.90f).coerceAtLeast(0.5f)
                lastDeathInfo = "被围死了 → 安全余量↑ 激进↓"
            }
            else -> {
                lastDeathInfo = "未知死因"
            }
        }

        // 高分加成
        if (score > 5000) {
            aggression = (aggression * 1.06f).coerceAtMost(2.0f)
            shortcutBonus = (shortcutBonus * 1.06f).coerceAtMost(2.0f)
            lastDeathInfo += " | 高分奖励"
        }
        // 速死惩罚
        if (score < 200) {
            aggression = (aggression * 0.88f).coerceAtLeast(0.5f)
            lastDeathInfo += " | 速死惩罚"
        }

        totalGames++
        saveLearning()
    }

    // ============================================================
    // =============== 决策核心（使用学习参数）===============
    // ============================================================

    private fun analyzeAndDecide(head: Point): Decision {
        val snakeLen = snake.size
        val space = floodFill(head, snake)
        val spaceRatio = space.toFloat() / snakeLen

        // ★ 学习参数参与决策：安全余量越高，越早进入危险等级
        val danger = when {
            spaceRatio < 1.0f * safetyMargin -> 5
            spaceRatio < 1.4f * safetyMargin -> 4
            spaceRatio < 2.5f * safetyMargin -> 3
            spaceRatio < 4.0f * safetyMargin -> 2
            else -> 1
        }
        val hunger = when {
            hungerCounter > 15 -> 5
            hungerCounter > 10 -> 4
            hungerCounter > 6 -> 3
            hungerCounter > 3 -> 2
            else -> 1
        }
        val foodPath = bfsPath(head, food, snake, dir)
        val foodDist = foodPath?.size ?: 999
        val foodReachable = foodPath != null
        val foodState = when {
            !foodReachable && foodUnreachableStreak > 10 -> 5
            !foodReachable && foodUnreachableStreak > 5 -> 4
            !foodReachable -> 3
            foodDist < 8 -> 1
            foodDist < 15 -> 2
            else -> 3
        }
        val stage = when {
            snakeLen < 25 -> 0
            snakeLen < 50 -> 1
            snakeLen < 85 -> 2
            else -> 3
        }

        if (danger >= 5) return Decision(3, "空间${"%.1f".format(spaceRatio)}x 极危→纯HAM")
        if (hunger >= 5 && foodReachable) return Decision(0, "饿了${hungerCounter}步→BFS冲食")
        if (danger >= 4) return Decision(1, "空间${"%.1f".format(spaceRatio)}x 紧张→追尾")
        if (foodState >= 5 && danger >= 3) return Decision(1, "食物${foodUnreachableStreak}步不可达→追尾")
        if (stage >= 3) return Decision(3, "蛇长${snakeLen}→纯HAM")
        if (stage >= 2) return Decision(2, "中期${snakeLen}节→加权HAM")
        if (stage >= 1 && danger <= 2) return Decision(2, "30+节空闲→加权HAM")
        if (stage == 0 && danger <= 2 && hunger <= 2) return Decision(4, "前期空闲→深度Beam")
        if (danger <= 2) return Decision(0, "空间充裕→BFS吃食")
        return Decision(0, "默认BFS")
    }

    private fun canSafelyEnterHam(head: Point, validDirs: List<Point>): Pair<Boolean, String> {
        val pathPos = pathIndex[head.x][head.y]
        val pathPoint = pathSequence[pathPos]
        if (pathPoint.x != head.x || pathPoint.y != head.y) return Pair(false, "蛇头不在路径")

        val nextPos = (pathPos + 1) % pathSequence.size
        val nextPoint = pathSequence[nextPos]
        val pathDir = Point(nextPoint.x - head.x, nextPoint.y - head.y)
        if (abs(pathDir.x) + abs(pathDir.y) != 1) return Pair(false, "路径不连续")
        if (!validDirs.contains(pathDir)) return Pair(false, "路径被堵")

        val nh = Point(head.x + pathDir.x, head.y + pathDir.y)
        val sim = ArrayDeque(snake); sim.addFirst(nh); sim.removeLast()
        if (sim.dropLast(1).any { it.x == nh.x && it.y == nh.y }) return Pair(false, "会撞身体")
        return Pair(true, "安全")
    }

    private fun autoPilotBFS() {
        if (gameOver) return
        val head = snake.first()
        val validDirs = dirsList.filter { d ->
            val isRev = (d.x == -dir.x && d.y == -dir.y)
            val nh = Point(head.x + d.x, head.y + d.y)
            val isWall = nh.x !in 0 until cols || nh.y !in 0 until rows
            val isSelf = snake.dropLast(1).any { it.x == nh.x && it.y == nh.y }
            !isRev && !isWall && !isSelf
        }
        if (validDirs.isEmpty()) return

        val p = bfsPath(head, food, snake, dir)
        if (p != null) foodUnreachableStreak = 0 else foodUnreachableStreak++

        val decision = analyzeAndDecide(head)
        var wanted = if (forcedStrategy >= 0) forcedStrategy else decision.strategy
        var reason = if (forcedStrategy >= 0) "手动强制" else decision.reason

        if (wanted == 2 || wanted == 3) {
            val (ok, why) = canSafelyEnterHam(head, validDirs)
            if (!ok) { reason = "$reason ⚠$why"; wanted = 0 }
        }

        strategyMode = wanted
        lastReason = reason

        val chosen: Point? = when (strategyMode) {
            1 -> tailChaseStrategy(head, validDirs)
            2 -> weightedHamStrategy(head, validDirs)
            3 -> pureHamStrategy(head, validDirs)
            4 -> deepBeamStrategy(head, validDirs)
            else -> fastBfsStrategy(head, validDirs)
        }
        if (chosen != null) { directionQueue.clear(); directionQueue.add(chosen) }
    }

    private fun fastBfsStrategy(head: Point, validDirs: List<Point>): Point? {
        if (hungerCounter > 12) {
            val p = bfsPath(head, food, snake, dir)
            if (p != null && p.size > 1) {
                val nm = Point(p[1].x - p[0].x, p[1].y - p[0].y)
                if (validDirs.contains(nm)) return nm
            }
        }
        val fdx = food.x - head.x; val fdy = food.y - head.y
        if (abs(fdx) + abs(fdy) == 1) {
            val fd = Point(fdx, fdy)
            if (validDirs.contains(fd)) return fd
        }
        if (hungerCounter > 6) {
            val p = bfsPath(head, food, snake, dir)
            if (p != null && p.size > 1) {
                val nm = Point(p[1].x - p[0].x, p[1].y - p[0].y)
                if (validDirs.contains(nm) && isEatingSafeQuick(head, food)) return nm
            }
        }

        var bestDir: Point? = null; var bestScore = Int.MIN_VALUE
        for (d in validDirs) {
            val nh = Point(head.x + d.x, head.y + d.y)
            val sim = ArrayDeque(snake); sim.addFirst(nh)
            val ate = nh.x == food.x && nh.y == food.y
            if (!ate) sim.removeLast()
            val region = regionSize(nh, sim)
            val dist = abs(nh.x - food.x) + abs(nh.y - food.y)
            val canReachTail = bfsPath(nh, sim.last(), sim, Point(0, 0)) != null
            val canReachFood = bfsPath(nh, food, sim, Point(0, 0)) != null

            // ★ 学习参数影响打分
            var s = region * 15 - (dist * 4 / aggression).toInt()
            if (ate) s += (3000 * aggression).toInt()
            if (canReachTail) s += 2000
            if (canReachFood) s += 1000
            if (region < sim.size * safetyMargin) s -= 50000
            if (!canReachTail && !canReachFood) s -= 10000
            if (nh.x == 0 || nh.x == cols - 1 || nh.y == 0 || nh.y == rows - 1) s -= 100

            if (s > bestScore) { bestScore = s; bestDir = d }
        }
        return bestDir
    }

    private fun deepBeamStrategy(head: Point, validDirs: List<Point>): Point? {
        if (hungerCounter > 15) {
            val p = bfsPath(head, food, snake, dir)
            if (p != null && p.size > 1) {
                val nm = Point(p[1].x - p[0].x, p[1].y - p[0].y)
                if (validDirs.contains(nm)) return nm
            }
        }
        val fdx = food.x - head.x; val fdy = food.y - head.y
        if (abs(fdx) + abs(fdy) == 1) {
            val fd = Point(fdx, fdy)
            if (validDirs.contains(fd) && isEatingSafeQuick(head, food)) return fd
        }

        val beamWidth = 10; val depth = 5
        var beam = ArrayList<BeamNode>(validDirs.size)
        for (d in validDirs) {
            val nh = Point(head.x + d.x, head.y + d.y)
            val sim = ArrayDeque(snake); sim.addFirst(nh)
            val ate = nh.x == food.x && nh.y == food.y
            if (!ate) sim.removeLast()
            beam.add(BeamNode(d, sim, if (ate) 1 else 0))
        }
        if (beam.isEmpty()) return null

        for (step in 1 until depth) {
            val nextBeam = ArrayList<BeamNode>(beam.size * 4)
            for (node in beam) {
                val sh = node.simSnake.first()
                for (nd in dirsList) {
                    val snx = sh.x + nd.x; val sny = sh.y + nd.y
                    if (snx !in 0 until cols || sny !in 0 until rows) continue
                    val ate = snx == food.x && sny == food.y
                    val bodyCheck = if (ate) node.simSnake else node.simSnake.dropLast(1)
                    if (bodyCheck.any { it.x == snx && it.y == sny }) continue
                    val nsnake = ArrayDeque(node.simSnake); nsnake.addFirst(Point(snx, sny))
                    if (!ate) nsnake.removeLast()
                    nextBeam.add(BeamNode(node.firstDir, nsnake, node.foodCount + if (ate) 1 else 0))
                }
            }
            if (nextBeam.isEmpty()) break
            val scored = nextBeam.map { Pair(it, fullScoreNode(it)) }.sortedByDescending { it.second }.take(beamWidth)
            beam = ArrayList(beamWidth)
            for (i in 0 until scored.size) beam.add(scored[i].first)
        }

        var bestDir: Point? = null; var bestScore = Int.MIN_VALUE
        for (node in beam) { val s = fullScoreNode(node); if (s > bestScore) { bestScore = s; bestDir = node.firstDir } }
        return bestDir
    }

    private fun fullScoreNode(node: BeamNode): Int {
        val nh = node.simSnake.first()
        val region = regionSize(nh, node.simSnake)
        val reachTail = bfsPath(nh, node.simSnake.last(), node.simSnake, Point(0, 0)) != null
        val reachFood = bfsPath(nh, food, node.simSnake, Point(0, 0)) != null
        val distToFood = abs(nh.x - food.x) + abs(nh.y - food.y)
        var s = region * 12 - (distToFood * 3 / aggression).toInt()
        if (reachTail) s += 2500
        if (reachFood) s += (800 * aggression).toInt()
        s += (node.foodCount * 800 * aggression).toInt()
        if (region < node.simSnake.size * safetyMargin) s -= 100000
        return s
    }

    private fun tailChaseStrategy(head: Point, validDirs: List<Point>): Point? {
        val foodDist = abs(head.x - food.x) + abs(head.y - food.y)
        if (foodDist <= 4) {
            val p = bfsPath(head, food, snake, dir)
            if (p != null && p.size > 1) {
                val nm = Point(p[1].x - p[0].x, p[1].y - p[0].y)
                if (validDirs.contains(nm) && isEatingSafeQuick(head, food)) return nm
            }
        }
        var best: Point? = null; var bestScore = Int.MIN_VALUE
        for (d in validDirs) {
            val nh = Point(head.x + d.x, head.y + d.y)
            val sim = ArrayDeque(snake); sim.addFirst(nh); sim.removeLast()
            val canReachTail = bfsPath(nh, sim.last(), sim, Point(0, 0)) != null
            val region = regionSize(nh, sim)
            var s = region * 10
            if (canReachTail) s += 100000
            s -= abs(nh.x - food.x) + abs(nh.y - food.y)
            if (s > bestScore) { bestScore = s; best = d }
        }
        return best ?: validDirs.firstOrNull()
    }

    private fun weightedHamStrategy(head: Point, validDirs: List<Point>): Point? {
        val pathPos = pathIndex[head.x][head.y]
        val onPath = pathSequence[pathPos].x == head.x && pathSequence[pathPos].y == head.y
        if (!onPath) return returnToPath(head, validDirs)

        val snakeLen = snake.size
        val baseMaxShortcut = when {
            snakeLen < 20 -> 30
            snakeLen < 30 -> 25
            snakeLen < 45 -> 18
            snakeLen < 60 -> 12
            snakeLen < 85 -> 7
            else -> 4
        }
        // ★ 学习参数影响抄近道距离
        val maxShortcut = (baseMaxShortcut * shortcutBonus).toInt().coerceAtLeast(3)

        val pathToFood = bfsPath(head, food, snake, dir)
        if (pathToFood != null && pathToFood.size in 2..maxShortcut) {
            val nextMove = Point(pathToFood[1].x - pathToFood[0].x, pathToFood[1].y - pathToFood[0].y)
            if (validDirs.contains(nextMove) && isEatingSafeQuick(head, food)) {
                val sim = ArrayDeque(snake); sim.addFirst(food)
                if (canReturnToPath(sim)) return nextMove
            }
        }

        val nextPos = (pathPos + 1) % pathSequence.size
        val nextP = pathSequence[nextPos]
        val pathDir = Point(nextP.x - head.x, nextP.y - head.y)
        if (validDirs.contains(pathDir)) {
            val nh = Point(head.x + pathDir.x, head.y + pathDir.y)
            val sim = ArrayDeque(snake); sim.addFirst(nh); sim.removeLast()
            if (!sim.dropLast(1).any { it.x == nh.x && it.y == nh.y }) return pathDir
        }
        return safeFallback(head, validDirs)
    }

    private fun canReturnToPath(sim: ArrayDeque<Point>): Boolean {
        val sh = sim.first()
        val pathPos = pathIndex[sh.x][sh.y]
        val p = pathSequence[pathPos]
        return bfsPath(sh, p, sim, Point(0, 0)) != null
    }

    private fun pureHamStrategy(head: Point, validDirs: List<Point>): Point? {
        val pathPos = pathIndex[head.x][head.y]
        val onPath = pathSequence[pathPos].x == head.x && pathSequence[pathPos].y == head.y
        if (!onPath) return returnToPath(head, validDirs)

        val nextPos = (pathPos + 1) % pathSequence.size
        val nextP = pathSequence[nextPos]
        val pathDir = Point(nextP.x - head.x, nextP.y - head.y)
        if (!validDirs.contains(pathDir)) return safeFallback(head, validDirs)

        val nh = Point(head.x + pathDir.x, head.y + pathDir.y)
        val sim = ArrayDeque(snake); sim.addFirst(nh); sim.removeLast()
        if (sim.dropLast(1).any { it.x == nh.x && it.y == nh.y }) return safeFallback(head, validDirs)
        return pathDir
    }

    private fun returnToPath(head: Point, validDirs: List<Point>): Point? {
        var bestMove: Point? = null
        var bestScore = -1
        for (d in validDirs) {
            val nh = Point(head.x + d.x, head.y + d.y)
            val sim = ArrayDeque(snake); sim.addFirst(nh); sim.removeLast()
            val pathPos = pathIndex[nh.x][nh.y]
            val pathPoint = pathSequence[pathPos]
            if (pathPoint.x == nh.x && pathPoint.y == nh.y) {
                if (bestScore < 0) { bestScore = 0; bestMove = d }
                continue
            }
            val p = bfsPath(nh, pathPoint, sim, Point(0, 0))
            if (p != null) {
                val sc = 1000 - p.size
                if (sc > bestScore) { bestScore = sc; bestMove = d }
            }
        }
        return bestMove ?: safeFallback(head, validDirs)
    }

    private fun safeFallback(head: Point, validDirs: List<Point>): Point? {
        var best: Point? = null; var bestScore = Int.MIN_VALUE
        for (d in validDirs) {
            val nh = Point(head.x + d.x, head.y + d.y)
            val sim = ArrayDeque(snake); sim.addFirst(nh); sim.removeLast()
            val canReachTail = bfsPath(nh, sim.last(), sim, Point(0, 0)) != null
            val region = regionSize(nh, sim)
            var s = region
            if (canReachTail) s += 100000
            if (s > bestScore) { bestScore = s; best = d }
        }
        return best ?: validDirs.firstOrNull()
    }

    private fun isEatingSafeQuick(head: Point, foodPos: Point): Boolean {
        val sim = ArrayDeque(snake); sim.addFirst(foodPos)
        val region = regionSize(sim.first(), sim)
        if (region > sim.size * 1.3f) return true
        if (region < sim.size) return false
        return bfsPath(sim.first(), sim.last(), sim, Point(0, 0)) != null
    }

    private fun autoPilotHamiltonian() {
        if (gameOver) return
        val head = snake.first()
        if (head.x !in 0 until cols || head.y !in 0 until rows) return
        val cur = pathIndex[head.x][head.y]
        val nxt = (cur + 1) % pathSequence.size
        val np = pathSequence[nxt]
        val dx = np.x - head.x; val dy = np.y - head.y
        val nh = Point(head.x + dx, head.y + dy)
        if (snake.dropLast(1).any { it.x == nh.x && it.y == nh.y }) {
            val nn = (nxt + 1) % pathSequence.size
            val nnp = pathSequence[nn]
            val dx2 = nnp.x - head.x; val dy2 = nnp.y - head.y
            if (abs(dx2) + abs(dy2) == 1) { dir = Point(dx2, dy2); return }
            return
        }
        dir = Point(dx, dy)
    }

    private fun regionSize(start: Point, currentSnake: Collection<Point>): Int {
        for (x in 0 until cols) for (y in 0 until rows) ffVisited[x][y] = false
        for (p in currentSnake) ffVisited[p.x][p.y] = true
        var h = 0; var t = 0
        ffQueue[t++] = start.x * rows + start.y
        ffVisited[start.x][start.y] = true
        var cnt = 0
        while (h < t) {
            val c = ffQueue[h++]
            val cx = c / rows; val cy = c % rows
            cnt++
            if (cx > 0 && !ffVisited[cx - 1][cy]) { ffVisited[cx - 1][cy] = true; ffQueue[t++] = (cx - 1) * rows + cy }
            if (cx < cols - 1 && !ffVisited[cx + 1][cy]) { ffVisited[cx + 1][cy] = true; ffQueue[t++] = (cx + 1) * rows + cy }
            if (cy > 0 && !ffVisited[cx][cy - 1]) { ffVisited[cx][cy - 1] = true; ffQueue[t++] = cx * rows + (cy - 1) }
            if (cy < rows - 1 && !ffVisited[cx][cy + 1]) { ffVisited[cx][cy + 1] = true; ffQueue[t++] = cx * rows + (cy + 1) }
        }
        return cnt
    }

    private fun floodFill(start: Point, currentSnake: Collection<Point>): Int {
        return regionSize(start, currentSnake)
    }

    private fun bfsPath(start: Point, target: Point, currentSnake: Collection<Point>, reverseDir: Point): List<Point>? {
        for (x in 0 until cols) for (y in 0 until rows) bfsVisited[x][y] = false
        var h = 0; var t = 0
        bfsQueue[t++] = start.x * rows + start.y
        bfsVisited[start.x][start.y] = true
        bfsParentX[start.x][start.y] = -1
        bfsParentY[start.x][start.y] = -1
        var found = false
        while (h < t) {
            val c = bfsQueue[h++]
            val cx = c / rows; val cy = c % rows
            if (cx == target.x && cy == target.y) { found = true; break }
            for (d in dirsList) {
                if (cx == start.x && cy == start.y && d.x == reverseDir.x && d.y == reverseDir.y) continue
                val nx = cx + d.x; val ny = cy + d.y
                if (nx !in 0 until cols || ny !in 0 until rows) continue
                if (bfsVisited[nx][ny]) continue
                if (!(nx == target.x && ny == target.y) && currentSnake.any { it.x == nx && it.y == ny }) continue
                bfsVisited[nx][ny] = true
                bfsParentX[nx][ny] = cx; bfsParentY[nx][ny] = cy
                bfsQueue[t++] = nx * rows + ny
            }
        }
        if (!found) return null
        val path = mutableListOf<Point>()
        var cx = target.x; var cy = target.y
        while (!(cx == start.x && cy == start.y)) {
            path.add(0, Point(cx, cy))
            val px = bfsParentX[cx][cy]; val py = bfsParentY[cx][cy]
            if (px == -1) break
            cx = px; cy = py
        }
        return path
    }

    private fun update() {
        if (gameOver) return
        when (aiMode) {
            1 -> {
                autoPilotBFS()
                if (directionQueue.isNotEmpty()) {
                    val next = directionQueue.removeFirst()
                    if (dir.x == 0 && dir.y == 0) dir = next
                    else if (dir.x != -next.x || dir.y != -next.y) dir = next
                }
            }
            2 -> autoPilotHamiltonian()
            else -> if (directionQueue.isNotEmpty()) {
                val next = directionQueue.removeFirst()
                if (dir.x == 0 && dir.y == 0) dir = next
                else if (dir.x != -next.x || dir.y != -next.y) dir = next
            }
        }
        if (dir.x == 0 && dir.y == 0) return

        val head = snake.first()
        val newHead = Point(head.x + dir.x, head.y + dir.y)

        // ★ 撞墙：越界 → 100% 是 WALL
        if (newHead.x !in 0 until cols || newHead.y !in 0 until rows) {
            gameOver = true
            onDeath("WALL")
            return
        }

        val isEating = newHead.x == food.x && newHead.y == food.y
        val tail = snake.last()
        val collided = if (newHead.x == tail.x && newHead.y == tail.y) isEating
        else snake.any { it.x == newHead.x && it.y == newHead.y }

        // ★ 撞身体：根据剩余空间再细分 TRAP / SELF
        if (collided) {
            gameOver = true
            val space = regionSize(head, snake)
            val cause = if (space < snake.size * 1.2f) "TRAP" else "SELF"
            onDeath(cause)
            return
        }

        val tailX = offsetX + tail.x * cellSize + cellSize / 2
        val tailY = offsetY + tail.y * cellSize + cellSize / 2
        val trailColor = if (isRainbowSkin)
            Color.HSVToColor(floatArrayOf((System.currentTimeMillis() / 10f) % 360f, 1f, 1f))
        else bodyColor
        particles.add(Particle(tailX + (Random.nextFloat() - 0.5f) * cellSize * 0.5f,
            tailY + (Random.nextFloat() - 0.5f) * cellSize * 0.5f,
            (Random.nextFloat() - 0.5f) * 1.5f, (Random.nextFloat() - 0.5f) * 1.5f,
            1.0f, trailColor, Random.nextFloat() * 0.8f + 0.5f, 0.003f, true))

        snake.addFirst(newHead)
        if (isEating) {
            hungerCounter = 0; comboCount++
            val base = 10 + (comboCount - 1) * 5
            val mult = when { score >= 1000 -> 3.0f; score >= 500 -> 2.0f; score >= 200 -> 1.5f; else -> 1.0f }
            val earned = (base * mult).toInt()
            score += earned
            onScoreChanged?.invoke(score)
            eatEffect(earned)
            placeFood()
            gameSpeed = max(70L, gameSpeed - 3L)
        } else { hungerCounter++; snake.removeLast() }
    }

    private fun eatEffect(scoreGained: Int) {
        vibrate(35)
        val cx = offsetX + food.x * cellSize + cellSize / 2
        val cy = offsetY + food.y * cellSize + cellSize / 2
        val colors = intArrayOf(Color.rgb(231, 76, 60), Color.rgb(241, 196, 15),
            Color.rgb(46, 204, 113), Color.rgb(52, 152, 219), Color.WHITE, Color.CYAN)
        for (i in 0 until 15) {
            val a = Random.nextFloat() * 6.2832f
            val sp = Random.nextFloat() * 8f + 2f
            particles.add(Particle(cx, cy, cos(a) * sp, sin(a) * sp, 1.0f,
                colors[Random.nextInt(colors.size)], Random.nextFloat() * 1.5f + 0.5f, 0.0015f))
        }
        floats.add(FloatText(cx, cy, 1.0f, "+$scoreGained"))
    }

    private fun onDeath(cause: String) {
        vibrate(300); shakeTime = 400f; deathFlashAlpha = 255f
        val hx = offsetX + snake.first().x * cellSize + cellSize / 2
        val hy = offsetY + snake.first().y * cellSize + cellSize / 2
        shockwaveX = hx; shockwaveY = hy; shockwaveRadius = cellSize; shockwaveAlpha = 255f
        paintSnakeBody.color = Color.rgb(200, 50, 50)
        paintSnakeBody.setShadowLayer(20f, 0f, 0f, Color.rgb(200, 50, 50))
        paintSnakeHead.color = Color.rgb(150, 0, 0)
        paintSnakeHead.setShadowLayer(15f, 0f, 0f, Color.rgb(150, 0, 0))
        for (i in 0 until 40) {
            val a = Random.nextFloat() * 6.2832f
            val sp = Random.nextFloat() * 12f + 3f
            particles.add(Particle(hx, hy, cos(a) * sp, sin(a) * sp, 1.5f,
                Color.rgb(255, 50, 50), Random.nextFloat() * 2f + 1f, 0.002f))
        }
        if (score > highScore) { highScore = score; prefs.edit().putInt("high_score", highScore).apply() }
        val cm = prefs.getInt("money", 0) + score
        prefs.edit().putInt("money", cm).apply()
        onMoneyChanged?.invoke(cm)

        // ★ 使用传入的明确死因更新学习参数
        analyzeAndLearn(cause)

        aiMode = 0
    }

    override fun onDraw(canvas: Canvas) {
        super.onDraw(canvas)
        cellSize = minOf(width / cols.toFloat(), height / rows.toFloat())
        offsetX = (width - cellSize * cols) / 2f
        offsetY = (height - cellSize * rows) / 2f

        if (paintBoardBg.shader != null) {
            val t = System.currentTimeMillis() % 5000L
            boardMatrix.setTranslate(t * 0.15f, t * 0.15f)
            paintBoardBg.shader?.setLocalMatrix(boardMatrix)
            canvas.drawRect(offsetX, offsetY, offsetX + cols * cellSize, offsetY + rows * cellSize, paintBoardBg)
        } else canvas.drawColor(bgColor)

        canvas.save()
        if (gameOver && shakeTime > 0) canvas.translate(shakeOffsetX, shakeOffsetY)

        val breath = (sin(System.currentTimeMillis() / 400.0).toFloat() + 1f) / 2f
        paintGrid.alpha = (60 + 195 * breath).toInt()
        paintGrid.color = gridColor
        for (i in 0..cols) { val x = offsetX + i * cellSize; canvas.drawLine(x, offsetY, x, offsetY + rows * cellSize, paintGrid) }
        for (i in 0..rows) { val y = offsetY + i * cellSize; canvas.drawLine(offsetX, y, offsetX + cols * cellSize, y, paintGrid) }

        if (aiMode == 2 && !gameOver) {
            for (i in 0 until pathSequence.size - 1) {
                val p1 = pathSequence[i]; val p2 = pathSequence[i + 1]
                canvas.drawLine(offsetX + p1.x * cellSize + cellSize / 2, offsetY + p1.y * cellSize + cellSize / 2,
                    offsetX + p2.x * cellSize + cellSize / 2, offsetY + p2.y * cellSize + cellSize / 2, paintHamPath)
            }
        }

        val fx = offsetX + food.x * cellSize + cellSize / 2
        val fy = offsetY + food.y * cellSize + cellSize / 2
        val pulse = 1f + 0.25f * sin(System.currentTimeMillis() / 150.0).toFloat()
        val fr = cellSize * 0.4f * pulse
        paintFoodGlow.shader = RadialGradient(fx, fy, fr * 2.2f,
            intArrayOf(Color.argb(200, 0, 255, 255), Color.argb(100, 0, 200, 255), Color.argb(0, 0, 0, 0)),
            floatArrayOf(0f, 0.5f, 1f), Shader.TileMode.CLAMP)
        canvas.drawCircle(fx, fy, fr * 2.2f, paintFoodGlow)
        canvas.save()
        canvas.rotate((System.currentTimeMillis() % 3600) / 10f, fx, fy)
        paintFoodCross.alpha = 220
        val cl = fr * 1.6f
        canvas.drawLine(fx - cl, fy, fx + cl, fy, paintFoodCross)
        canvas.drawLine(fx, fy - cl, fx, fy + cl, paintFoodCross)
        canvas.rotate(45f, fx, fy)
        canvas.drawLine(fx - cl * 0.7f, fy, fx + cl * 0.7f, fy, paintFoodCross)
        canvas.drawLine(fx, fy - cl * 0.7f, fx, fy + cl * 0.7f, paintFoodCross)
        canvas.restore()
        paintFoodCore.alpha = 255
        canvas.drawCircle(fx, fy, fr * 0.35f, paintFoodCore)

        if (snake.isNotEmpty()) {
            val progress = if (gameOver) 0f else (timeAccumulator.toFloat() / gameSpeed).coerceIn(0f, 1f)
            pathBuf.reset()
            val count = snake.size
            var idx = 0
            for (p in snake) {
                var bx = offsetX + p.x * cellSize + cellSize / 2
                var by = offsetY + p.y * cellSize + cellSize / 2
                if (idx == 0 && !gameOver) {
                    val prevP = if (count > 1) snake.elementAt(1) else Point(snake.first().x - dir.x, snake.first().y - dir.y)
                    val prevX = offsetX + prevP.x * cellSize + cellSize / 2
                    val prevY = offsetY + prevP.y * cellSize + cellSize / 2
                    bx = prevX + (bx - prevX) * progress
                    by = prevY + (by - prevY) * progress
                }
                val t = System.currentTimeMillis() / 200.0
                val amp = if (dir.x != 0) cellSize * 0.1f else cellSize * 0.05f
                val pf = pointsBuf[idx.coerceAtMost(pointsBuf.size - 1)]
                pf.x = bx + sin(t + idx * 0.5).toFloat() * amp
                pf.y = by + cos(t + idx * 0.5).toFloat() * amp
                idx++
            }
            pathBuf.moveTo(pointsBuf[0].x, pointsBuf[0].y)
            for (i in 1 until count) {
                val prev = pointsBuf[i - 1]; val curr = pointsBuf[i]
                pathBuf.quadTo(prev.x, prev.y, (prev.x + curr.x) / 2f, (prev.y + curr.y) / 2f)
            }
            if (count > 1) pathBuf.lineTo(pointsBuf[count - 1].x, pointsBuf[count - 1].y)

            if (isRainbowSkin) {
                val hp = pointsBuf[0]; val tp = pointsBuf[count - 1]
                val angle = atan2(tp.y - hp.y, tp.x - hp.x)
                val to = (System.currentTimeMillis() % 3000) / 3000f
                val fd = cellSize * 6 * to
                paintSnakeBody.shader = LinearGradient(
                    hp.x - cos(angle) * fd, hp.y - sin(angle) * fd,
                    tp.x - cos(angle) * fd, tp.y - sin(angle) * fd,
                    rainbow, null, Shader.TileMode.MIRROR)
                paintSnakeHead.color = Color.WHITE
                paintSnakeBody.alpha = 255
                paintSnakeBody.setShadowLayer(35f, 0f, 0f, Color.WHITE)
            } else {
                paintSnakeBody.shader = null; paintSnakeBody.color = bodyColor
                paintSnakeBody.alpha = 255
                paintSnakeBody.setShadowLayer(20f, 0f, 0f, bodyColor)
            }
            paintSnakeBody.strokeWidth = cellSize * 0.8f
            paintSnakeBody.alpha = if (isRainbowSkin) 150 else 120
            canvas.drawPath(pathBuf, paintSnakeBody)
            paintSnakeBody.strokeWidth = cellSize * 0.65f
            paintSnakeBody.alpha = 255
            canvas.drawPath(pathBuf, paintSnakeBody)

            val hp = pointsBuf[0]
            canvas.drawCircle(hp.x, hp.y, cellSize * 0.5f, paintSnakeHead)
            canvas.drawCircle(hp.x - cellSize * 0.1f, hp.y - cellSize * 0.1f, cellSize * 0.15f, paintHighlight)
            val cd = if (dir.x == 0 && dir.y == 0) Point(1, 0) else dir
            val eo = cellSize * 0.2f
            val poX = -cd.y * (cellSize * 0.2f); val poY = cd.x * (cellSize * 0.2f)
            canvas.drawCircle(hp.x + cd.x * eo + poX, hp.y + cd.y * eo + poY, cellSize * 0.12f, paintEyeW)
            canvas.drawCircle(hp.x + cd.x * eo - poX, hp.y + cd.y * eo - poY, cellSize * 0.12f, paintEyeW)
            canvas.drawCircle(hp.x + cd.x * eo * 1.2f + poX, hp.y + cd.y * eo * 1.2f + poY, cellSize * 0.06f, paintEyeB)
            canvas.drawCircle(hp.x + cd.x * eo * 1.2f - poX, hp.y + cd.y * eo * 1.2f - poY, cellSize * 0.06f, paintEyeB)
        }

        particles.forEach { p ->
            paintParticle.color = p.color
            paintParticle.alpha = (p.life * 255).toInt().coerceIn(0, 255)
            if (p.isTrail) canvas.drawCircle(p.x, p.y, cellSize * 0.1f * p.life * p.size, paintParticle)
            else canvas.drawCircle(p.x, p.y, cellSize * 0.15f * p.life * p.size, paintParticle)
        }
        if (shockwaveAlpha > 0) {
            paintShock.alpha = shockwaveAlpha.toInt().coerceIn(0, 255)
            canvas.drawCircle(shockwaveX, shockwaveY, shockwaveRadius, paintShock)
        }
        floats.forEach { t ->
            paintFloat.alpha = (t.life * 255).toInt().coerceIn(0, 255)
            canvas.drawText(t.text, t.x, t.y, paintFloat)
        }
        canvas.restore()

        if (gameOver) {
            canvas.drawColor(Color.argb(deathFlashAlpha.toInt().coerceIn(0, 255), 180, 0, 0))
            paintText.textSize = 80f; paintText.color = Color.RED
            paintText.setShadowLayer(20f, 0f, 0f, Color.BLACK)
            canvas.drawText("GAME OVER", width / 2f, height / 2f - 100, paintText)
            paintText.textSize = 34f; paintText.color = Color.WHITE
            canvas.drawText("得分: $score  最高: $highScore", width / 2f, height / 2f - 40, paintText)
            // ★ 显示学习信息 ★
            paintLearn.color = Color.rgb(120, 255, 180)
            paintLearn.textSize = 16f
            canvas.drawText("AI学习: $lastDeathInfo", width / 2f, height / 2f + 10, paintLearn)
            paintLearn.textSize = 14f
            paintLearn.color = Color.rgb(255, 200, 100)
            canvas.drawText("参数 → 激进:${"%.2f".format(aggression)} 安全:${"%.2f".format(safetyMargin)} 抄近道:${"%.2f".format(shortcutBonus)}", width / 2f, height / 2f + 40, paintLearn)
            paintLearn.textSize = 13f
            paintLearn.color = Color.rgb(200, 200, 200)
            canvas.drawText("已训练 ${totalGames} 局 | 撞墙:${deathByWall} 撞自己:${deathBySelf} 被围:${deathByTrap}", width / 2f, height / 2f + 70, paintLearn)
            if ((System.currentTimeMillis() / 500) % 2 == 0L) {
                paintSubText.textSize = 28f; paintSubText.color = Color.WHITE
                canvas.drawText("点击屏幕重新开始", width / 2f, height / 2f + 130, paintSubText)
            }
        } else if (dir.x == 0 && dir.y == 0) {
            paintSubText.textSize = 32f; paintSubText.color = Color.WHITE
            canvas.drawText("滑动屏幕开始", width / 2f, height / 2f, paintSubText)
            paintSubText.textSize = 20f; paintSubText.color = Color.LTGRAY
            canvas.drawText("(AI会从每局死亡中学习)", width / 2f, height / 2f + 50, paintSubText)
        } else if (aiMode == 1) {
            val modeName: String; val modeDesc: String; val modeColor: Int
            when (strategyMode) {
                1 -> { modeName = "🔄 追尾保命"; modeDesc = "沿身体循环，等待食物"; modeColor = Color.rgb(241, 196, 15) }
                2 -> { modeName = "🛤 加权汉密尔顿"; modeDesc = "动态抄近道：学习参数 ${"%.1f".format(shortcutBonus)}x"; modeColor = Color.rgb(52, 152, 219) }
                3 -> { modeName = "🛡 纯汉密尔顿"; modeDesc = "严格沿固定路径，绝对不死"; modeColor = Color.rgb(46, 204, 113) }
                4 -> { modeName = "🧠 深度 Beam"; modeDesc = "深度5+宽度10+分区评估"; modeColor = Color.rgb(155, 89, 182) }
                else -> { modeName = "🎯 BFS + Beam"; modeDesc = "全方向分区评估，防隔离"; modeColor = Color.rgb(231, 76, 60) }
            }
            val panelX = width / 2f; val panelY = height - 110f
            val panelW = 660f; val panelH = 125f
            canvas.drawRoundRect(panelX - panelW / 2, panelY - panelH / 2,
                panelX + panelW / 2, panelY + panelH / 2, 15f, 15f, paintPanelBg)
            paintPanelBorder.color = modeColor
            canvas.drawRoundRect(panelX - panelW / 2, panelY - panelH / 2,
                panelX + panelW / 2, panelY + panelH / 2, 15f, 15f, paintPanelBorder)
            paintModeName.color = modeColor
            canvas.drawText(modeName, panelX, panelY - 35f, paintModeName)
            canvas.drawText(modeDesc, panelX, panelY - 12f, paintModeDesc)
            paintReason.textSize = 12f
            canvas.drawText("💡 $lastReason", panelX - panelW / 2 + 15f, panelY + 10f, paintReason)
            paintLearn.textSize = 12f
            paintLearn.color = Color.rgb(120, 255, 180)
            canvas.drawText("🧬 激进:${"%.2f".format(aggression)} 安全:${"%.2f".format(safetyMargin)} 抄近道:${"%.2f".format(shortcutBonus)}", panelX - panelW / 2 + 15f, panelY + 30f, paintLearn)
            val snakeLen = snake.size
            val freeSpace = cols * rows - snakeLen
            paintLearn.color = Color.rgb(180, 180, 180)
            paintLearn.textSize = 11f
            canvas.drawText("LEN:$snakeLen SPACE:$freeSpace HUNGER:$hungerCounter STRK:$foodUnreachableStreak", panelX - panelW / 2 + 15f, panelY + 48f, paintLearn)
        }
    }

    private var touchStartX = 0f
    private var touchStartY = 0f

    override fun onTouchEvent(event: MotionEvent): Boolean {
        if (aiMode != 0 && event.action == MotionEvent.ACTION_UP) {
            if (gameOver) { reset(); return true }
            return true
        }
        when (event.action) {
            MotionEvent.ACTION_DOWN -> { touchStartX = event.x; touchStartY = event.y; return true }
            MotionEvent.ACTION_UP -> {
                if (gameOver) { reset(); return true }
                val dx = event.x - touchStartX; val dy = event.y - touchStartY
                if (abs(dx) < 15 && abs(dy) < 15) return true
                val lastDir = if (directionQueue.isNotEmpty()) directionQueue.last() else dir
                if (abs(dx) > abs(dy)) {
                    val nd = if (dx > 0) Point(1, 0) else Point(-1, 0)
                    if (nd.x != -lastDir.x || nd.y != -lastDir.y) {
                        if (directionQueue.size < 2 && (lastDir.x != nd.x || lastDir.y != nd.y)) directionQueue.add(nd)
                    }
                } else {
                    val nd = if (dy > 0) Point(0, 1) else Point(0, -1)
                    if (nd.x != -lastDir.x || nd.y != -lastDir.y) {
                        if (directionQueue.size < 2 && (lastDir.x != nd.x || lastDir.y != nd.y)) directionQueue.add(nd)
                    }
                }
                return true
            }
        }
        return super.onTouchEvent(event)
    }
}
