package com.myjoe.snake.ui.theme

import android.content.Context
import android.graphics.Canvas
import android.graphics.Paint
import android.graphics.Color
import android.graphics.RadialGradient
import android.graphics.Shader
import android.util.AttributeSet
import android.view.MotionEvent
import android.view.View
import android.os.Vibrator
import android.os.VibrationEffect
import android.os.Build
import com.myjoe.snake.R
import kotlin.math.min
import kotlin.random.Random

// ====================== 常量配置 ======================
private const val BOARD_COLS = 15
private const val BOARD_ROWS = 15
private const val INITIAL_TICK_MS = 180L
private const val MIN_TICK_MS = 70L
private const val SPEEDUP_STEP_MS = 3L
private const val MAX_DIRECTION_QUEUE = 3
private const val MAX_PARTICLES = 200
private const val DEATH_PARTICLE_COUNT = 60
private const val FOOD_PARTICLE_COUNT = 25
private const val TRAIL_PARTICLE_INTERVAL = 3
private const val SCORE_TIER_1 = 1000
private const val SCORE_TIER_2 = 500
private const val SCORE_TIER_3 = 200
private const val MONEY_PER_TIER1 = 10
private const val MONEY_PER_TIER2 = 5
private const val MONEY_PER_TIER3 = 1
private const val VIBRATE_SHORT_MS = 80L
private const val VIBRATE_LONG_MS = 300L
private const val HIGHSCORE_PREFS = "GamePrefs"
private const val HIGHSCORE_KEY = "HighScore"
private const val MONEY_PREFS = "GamePrefs"
private const val MONEY_KEY = "Money"

// ====================== 数据结构 ======================
private data class Point(val x: Int, val y: Int)

// ====================== 主 View ======================
class SnakeView @JvmOverloads constructor(
    context: Context,
    attrs: AttributeSet? = null
) : View(context, attrs) {

    private val cols = BOARD_COLS
    private val rows = BOARD_ROWS
    private var cellSize = 0f
    private var offsetX = 0f
    private var offsetY = 0f

    private var snake = ArrayDeque<Point>()
    private var dir = Point(1, 0)
    private var directionQueue = ArrayDeque<Point>()

    private val bodyGrid = Array(cols) { BooleanArray(rows) }

    private lateinit var food: Point
    private var score = 0
    private var highScore = 0
    private var money = 0
    private var isGameOver = false
    private var isRunning = true

    // 连击系统
    private var comboCount = 0

    private var tickMs = INITIAL_TICK_MS
    private var lastUpdateTime = 0L

    private var skinIndex = 0
    private val normalSkinColors = intArrayOf(
        Color.parseColor("#00E676"),
        Color.parseColor("#FF4081"),
        Color.parseColor("#7C4DFF"),
        Color.parseColor("#00E5FF"),
        Color.parseColor("#FFD600")
    )
    private val normalHeadColors = intArrayOf(
        Color.parseColor("#00C853"),
        Color.parseColor("#F50057"),
        Color.parseColor("#651FFF"),
        Color.parseColor("#00B8D4"),
        Color.parseColor("#FFAB00")
    )
    private var currentBodyColor = normalSkinColors[0]
    private var currentHeadColor = normalHeadColors[0]

    private var rainbowPhase = 0f
    private var rainbowColors = IntArray(361)
    private var boardMatrix = Array(cols) { FloatArray(rows) }

    // AI 模式：0=手动, 1=BFS, 2=HAM
    private var aiMode = 0
    private var aiLevel = 0
    private val hamiltonianPath = mutableListOf<Point>()
    private var hamiltonianIndex = 0
    private var consecutiveDeaths = 0

    private var hungerCounter = 0
    private var lastFoodTime = 0L

    private data class Particle(
        var x: Float, var y: Float,
        var vx: Float, var vy: Float,
        var alpha: Int, val color: Int,
        val size: Float
    )
    private val particles = mutableListOf<Particle>()

    private val paintBackground = Paint().apply { color = Color.parseColor("#111111"); style = Paint.Style.FILL }
    private val paintBoard = Paint().apply { color = Color.parseColor("#1B1B1B"); style = Paint.Style.FILL }
    private val paintGrid = Paint().apply { color = Color.parseColor("#2C2C2C"); style = Paint.Style.STROKE; strokeWidth = 2f }
    private val paintSnakeHead = Paint().apply { color = currentHeadColor; style = Paint.Style.FILL }
    private val paintSnakeBody = Paint().apply { color = currentBodyColor; style = Paint.Style.FILL }
    private val paintFood = Paint().apply { color = Color.RED; style = Paint.Style.FILL }
    private val paintText = Paint().apply { color = Color.WHITE; textSize = 60f; textAlign = Paint.Align.CENTER; isAntiAlias = true }
    private val paintTextSmall = Paint().apply { color = Color.parseColor("#AAAAAA"); textSize = 36f; textAlign = Paint.Align.CENTER; isAntiAlias = true }
    private val paintParticles = Paint().apply { style = Paint.Style.FILL; isAntiAlias = true }
    private val paintEyes = Paint().apply { color = Color.WHITE; style = Paint.Style.FILL }
    private val paintPupils = Paint().apply { color = Color.BLACK; style = Paint.Style.FILL }

    private val vibrator: Vibrator = context.getSystemService(Context.VIBRATOR_SERVICE) as Vibrator

    init {
        isFocusable = true
        isFocusableInTouchMode = true
        loadPrefs()
        initRainbowColors()
        initBoardMatrix()
        initHamiltonianPath()
        reset()
    }

    private fun loadPrefs() {
        val sharedPrefs = context.getSharedPreferences(HIGHSCORE_PREFS, Context.MODE_PRIVATE)
        highScore = sharedPrefs.getInt(HIGHSCORE_KEY, 0)
        money = context.getSharedPreferences(MONEY_PREFS, Context.MODE_PRIVATE).getInt(MONEY_KEY, 0)
    }

    private fun saveHighScore() {
        context.getSharedPreferences(HIGHSCORE_PREFS, Context.MODE_PRIVATE).edit()
            .putInt(HIGHSCORE_KEY, highScore).apply()
    }

    private fun saveMoney() {
        context.getSharedPreferences(MONEY_PREFS, Context.MODE_PRIVATE).edit()
            .putInt(MONEY_KEY, money).apply()
    }

    private fun initRainbowColors() {
        for (i in 0..360) {
            rainbowColors[i] = Color.HSVToColor(floatArrayOf(i.toFloat(), 1f, 1f))
        }
    }

    private fun initBoardMatrix() {
        for (x in 0 until cols) {
            for (y in 0 until rows) {
                boardMatrix[x][y] = (x + y).toFloat() / (cols + rows - 2).toFloat()
            }
        }
    }

    private fun initHamiltonianPath() {
        hamiltonianPath.clear()
        for (x in 0 until cols) {
            if (x % 2 == 0) {
                for (y in 0 until rows) hamiltonianPath.add(Point(x, y))
            } else {
                for (y in rows - 1 downTo 0) hamiltonianPath.add(Point(x, y))
            }
        }
    }

    private fun reset() {
        snake.clear()
        if (aiMode == 2) {
            snake.add(Point(0, 0))
            dir = Point(0, 1)
        } else {
            snake.addFirst(Point(0, 0))
            snake.addFirst(Point(1, 0))
            snake.addFirst(Point(2, 0))
            dir = Point(1, 0)
        }
        directionQueue.clear()
        tickMs = INITIAL_TICK_MS
        score = 0
        comboCount = 0
        hungerCounter = 0
        isGameOver = false
        isRunning = true
        particles.clear()
        rebuildBodyGrid()
        applySkin()
        hamiltonianIndex = 0
        lastFoodTime = System.currentTimeMillis()
        spawnFood()
        invalidate()
    }

    private fun rebuildBodyGrid() {
        for (x in 0 until cols) for (y in 0 until rows) bodyGrid[x][y] = false
        for (p in snake) {
            if (p.x in 0 until cols && p.y in 0 until rows) {
                bodyGrid[p.x][p.y] = true
            }
        }
    }

    private fun isOnBody(x: Int, y: Int): Boolean {
        return x in 0 until cols && y in 0 until rows && bodyGrid[x][y]
    }

    private fun applySkin() {
        currentBodyColor = normalSkinColors[skinIndex.coerceIn(0, 4)]
        currentHeadColor = normalHeadColors[skinIndex.coerceIn(0, 4)]
        paintSnakeBody.color = currentBodyColor
        paintSnakeHead.color = currentHeadColor
        paintSnakeBody.clearShadowLayer()
        paintSnakeHead.clearShadowLayer()
    }

    private fun spawnFood() {
        var newX: Int
        var newY: Int
        var attempts = 0
        do {
            newX = Random.nextInt(cols)
            newY = Random.nextInt(rows)
            attempts++
        } while (isOnBody(newX, newY) && attempts < 500)

        if (isOnBody(newX, newY)) {
            outer@ for (x in 0 until cols) {
                for (y in 0 until rows) {
                    if (!isOnBody(x, y)) { newX = x; newY = y; break@outer }
                }
            }
        }
        food = Point(newX, newY)
        lastFoodTime = System.currentTimeMillis()
    }

    // ====================== 更新逻辑 ======================

    fun update() {
        if (!isRunning || isGameOver) return

        val currentTime = System.currentTimeMillis()
        if (currentTime - lastUpdateTime < tickMs) return
        lastUpdateTime = currentTime

        when (aiMode) {
            1 -> autoPilotBFS()
            2 -> autoPilotHamiltonian()
        }

        if (directionQueue.isNotEmpty()) {
            dir = directionQueue.removeFirst()
        }

        val head = snake.first()
        val newHead = Point(head.x + dir.x, head.y + dir.y)

        if (newHead.x < 0 || newHead.x >= cols || newHead.y < 0 || newHead.y >= rows) {
            triggerDeath(); return
        }

        val willEat = (newHead == food)
        val bodyToCheck = if (willEat) snake else snake.dropLast(1)
        if (bodyToCheck.any { it == newHead }) {
            triggerDeath(); return
        }

        snake.addFirst(newHead)
        bodyGrid[newHead.x][newHead.y] = true

        if (willEat) {
            comboCount++
            // 连击倍率：基础分 10 + 连击加成（每个额外的食物 +5 分）
            val basePoints = 10 + (comboCount - 1) * 5
            // 高分倍率：>=1000 分 ×3，>=500 分 ×2，>=200 分 ×1.5
            val multiplier = when {
                score >= 1000 -> 3.0f
                score >= 500 -> 2.0f
                score >= 200 -> 1.5f
                else -> 1.0f
            }
            score += (basePoints * multiplier).toInt()

            when {
                score >= SCORE_TIER_1 -> money += MONEY_PER_TIER1
                score >= SCORE_TIER_2 -> money += MONEY_PER_TIER2
                else -> money += MONEY_PER_TIER3
            }
            if (score > highScore) highScore = score
            spawnFoodParticles(newHead)
            tickMs = (tickMs - SPEEDUP_STEP_MS).coerceAtLeast(MIN_TICK_MS)
            vibrate(VIBRATE_SHORT_MS)
            spawnFood()
            hungerCounter = 0
        } else {
            val tail = snake.removeLast()
            bodyGrid[tail.x][tail.y] = false
            hungerCounter++
        }

        invalidate()
    }

    // ====================== AI: 4 层决策 BFS ======================

    private data class MoveInfo(
        val dir: Point,
        val next: Point,
        val willEat: Boolean,
        val canReachTail: Boolean,     // 走完后能追到尾巴
        val foodReachable: Boolean,    // 走完后食物可达
        val space: Int,                // 走完后可达空间
        val distToFood: Int,           // 走完后到食物的 BFS 距离
        val eatSafe: Boolean           // 如果吃到食物，吃完后是否能追到尾巴
    )

    private fun autoPilotBFS() {
        val head = snake.first()
        val directions = listOf(Point(1, 0), Point(-1, 0), Point(0, 1), Point(0, -1))
        directionQueue.clear()

        // ---- 收集所有物理安全方向的所有指标 ----
        val moves = mutableListOf<MoveInfo>()

        for (d in directions) {
            if (d.x == -dir.x && d.y == -dir.y) continue
            val next = Point(head.x + d.x, head.y + d.y)
            if (next.x !in 0 until cols || next.y !in 0 until rows) continue

            val willEat = next == food
            val body = if (willEat) snake else snake.dropLast(1)
            if (body.any { it == next }) continue

            // 模拟：普通移动（尾巴会移开）
            val simNormal = ArrayDeque(snake)
            simNormal.addFirst(next)
            simNormal.removeLast()

            val canReachTailNormal = bfsPathWithSnake(next, simNormal.last(), simNormal).isNotEmpty()
            val reachable = getReachableCells(next, simNormal)
            val foodReachable = reachable.contains(food)
            val space = reachable.size
            val distPath = bfsPathWithSnake(next, food, simNormal)
            val dist = if (distPath.isNotEmpty()) distPath.size else 9999

            // 模拟：如果吃到食物（尾巴不移开，身体变长）
            var eatSafe = true
            if (willEat) {
                val simEat = ArrayDeque(snake)
                simEat.addFirst(next)
                // 尾巴不移开
                eatSafe = bfsPathWithSnake(next, simEat.last(), simEat).isNotEmpty()
            }

            moves.add(
                MoveInfo(
                    dir = d,
                    next = next,
                    willEat = willEat,
                    canReachTail = canReachTailNormal,
                    foodReachable = foodReachable,
                    space = space,
                    distToFood = dist,
                    eatSafe = eatSafe
                )
            )
        }

        if (moves.isEmpty()) return

        // ========== 第 1 层：食物贴脸 + 吃完安全 ==========
        moves.firstOrNull { it.willEat && it.eatSafe }?.let {
            directionQueue.add(it.dir)
            return
        }

        // ========== 第 2 层：极度饥饿（>15步）+ 物理安全 ==========
        if (hungerCounter > 15) {
            val best = moves
                .filter { it.foodReachable || it.willEat }
                .minByOrNull { it.distToFood }
            if (best != null) {
                directionQueue.add(best.dir)
                return
            }
        }

        // ========== 第 3 层：在"能追到尾巴"的方向中选最优 ==========
        // 这是老版本能跑17万的核心：只走安全方向
        val tailSafeMoves = moves.filter { it.canReachTail }
        if (tailSafeMoves.isNotEmpty()) {
            // 排序：食物可达 > 距离近 > 空间大
            val best = tailSafeMoves.minWithOrNull(
                compareByDescending<MoveInfo> { if (it.foodReachable) 1 else 0 }
                    .thenBy { it.distToFood }
                    .thenByDescending { it.space }
            )
            if (best != null) {
                directionQueue.add(best.dir)
                return
            }
        }

        // ========== 第 4 层：所有方向都追不到尾巴（死局）==========
        // 这是新版本的修正点：不绕圈等死，直接搏一把去吃
        // 因为如果所有方向都追不到尾巴，早晚都要死，不如去搏分数
        val foodHunting = moves
            .filter { it.foodReachable || it.willEat }
            .minByOrNull { it.distToFood }

        if (foodHunting != null) {
            directionQueue.add(foodHunting.dir)
            return
        }

        // 兜底：连食物都不可达，选空间最大的
        val bestSpace = moves.maxByOrNull { it.space }
        if (bestSpace != null) {
            directionQueue.add(bestSpace.dir)
            return
        }

        // 真·绝境：随便走一个（理论上不会到这）
        moves.firstOrNull()?.let { directionQueue.add(it.dir) }
    }

    private fun bfsPathWithSnake(start: Point, target: Point, customSnake: ArrayDeque<Point>): List<Point> {
        val queue = ArrayDeque<Point>()
        val visited = HashSet<Point>()
        val parent = HashMap<Point, Point>()
        queue.add(start); visited.add(start)

        while (queue.isNotEmpty()) {
            val current = queue.removeFirst()
            if (current == target) {
                val path = mutableListOf<Point>()
                var p: Point? = current
                while (p != null && p != start) { path.add(p!!); p = parent[p] }
                return path.reversed()
            }
            for (d in listOf(Point(1, 0), Point(-1, 0), Point(0, 1), Point(0, -1))) {
                val next = Point(current.x + d.x, current.y + d.y)
                if (next.x < 0 || next.x >= cols || next.y < 0 || next.y >= rows) continue
                if (visited.contains(next)) continue
                if (next != target) {
                    val bodyToCheck = if (next == customSnake.last()) customSnake.dropLast(1) else customSnake
                    if (bodyToCheck.any { it == next }) continue
                }
                visited.add(next); parent[next] = current; queue.add(next)
            }
        }
        return emptyList()
    }

    private fun getReachableCells(start: Point, customSnake: ArrayDeque<Point>): Set<Point> {
        val queue = ArrayDeque<Point>()
        val visited = HashSet<Point>()
        queue.add(start); visited.add(start)
        while (queue.isNotEmpty()) {
            val current = queue.removeFirst()
            for (d in listOf(Point(1, 0), Point(-1, 0), Point(0, 1), Point(0, -1))) {
                val next = Point(current.x + d.x, current.y + d.y)
                if (next.x < 0 || next.x >= cols || next.y < 0 || next.y >= rows) continue
                if (visited.contains(next)) continue
                if (next != customSnake.last() && customSnake.any { it == next }) continue
                visited.add(next); queue.add(next)
            }
        }
        return visited
    }

    // ====================== AI: 汉密尔顿回路 ======================

    private fun autoPilotHamiltonian() {
        val head = snake.first()
        var idx = hamiltonianPath.indexOf(head)
        if (idx == -1) {
            var minDist = Int.MAX_VALUE
            var closest = 0
            for (i in hamiltonianPath.indices) {
                val p = hamiltonianPath[i]
                val d = kotlin.math.abs(p.x - head.x) + kotlin.math.abs(p.y - head.y)
                if (d < minDist) { minDist = d; closest = i }
            }
            idx = closest
        }
        val nextIdx = (idx + 1) % hamiltonianPath.size
        val nextPoint = hamiltonianPath[nextIdx]
        val dx = nextPoint.x - head.x
        val dy = nextPoint.y - head.y

        if (kotlin.math.abs(dx) + kotlin.math.abs(dy) != 1) {
            autoPilotBFS()
            return
        }

        directionQueue.clear()
        directionQueue.add(Point(dx, dy))
        hamiltonianIndex = nextIdx
    }

    // ====================== 死亡处理 ======================

    private fun triggerDeath() {
        isGameOver = true
        isRunning = false
        triggerDeathEffects()
        vibrate(VIBRATE_LONG_MS)
        consecutiveDeaths++
        saveScoreAndMoney()
        invalidate()
    }

    private fun triggerDeathEffects() {
        aiMode = 0
        paintSnakeBody.color = Color.RED
        paintSnakeHead.color = Color.RED
        paintSnakeBody.clearShadowLayer()
        paintSnakeHead.clearShadowLayer()
        val head = snake.first()
        val centerX = offsetX + head.x * cellSize + cellSize / 2
        val centerY = offsetY + head.y * cellSize + cellSize / 2
        repeat(DEATH_PARTICLE_COUNT) { spawnParticle(centerX, centerY, Color.RED) }
    }

    private fun saveScoreAndMoney() {
        if (score > highScore) { highScore = score; saveHighScore() }
        saveMoney()
        if (consecutiveDeaths >= 3 && aiLevel > 0) { aiLevel--; consecutiveDeaths = 0 }
        else if (score > SCORE_TIER_1 && aiLevel < 3) { aiLevel++; consecutiveDeaths = 0 }
    }

    // ====================== 粒子系统 ======================

    private fun spawnFoodParticles(at: Point) {
        val cx = offsetX + at.x * cellSize + cellSize / 2
        val cy = offsetY + at.y * cellSize + cellSize / 2
        repeat(FOOD_PARTICLE_COUNT) { spawnParticle(cx, cy, Color.YELLOW) }
    }

    private fun spawnParticle(x: Float, y: Float, color: Int) {
        if (particles.size >= MAX_PARTICLES) particles.removeAt(0)
        val angle = Random.nextFloat() * 360f
        val speed = Random.nextFloat() * 5f + 1f
        particles.add(
            Particle(
                x, y,
                Math.cos(Math.toRadians(angle.toDouble())).toFloat() * speed,
                Math.sin(Math.toRadians(angle.toDouble())).toFloat() * speed,
                255, color,
                Random.nextFloat() * 8f + 4f
            )
        )
    }

    private fun updateParticles() {
        val it = particles.iterator()
        while (it.hasNext()) {
            val p = it.next()
            p.x += p.vx; p.y += p.vy; p.vy += 0.2f; p.alpha -= 8
            if (p.alpha <= 0) it.remove()
        }
    }

    // ====================== 绘制 ======================

    override fun onSizeChanged(w: Int, h: Int, oldw: Int, oldh: Int) {
        super.onSizeChanged(w, h, oldw, oldh)
        cellSize = minOf(w / cols.toFloat(), h / rows.toFloat())
        offsetX = (w - cellSize * cols) / 2f
        offsetY = (h - cellSize * rows) / 2f
    }

    override fun onDraw(canvas: Canvas) {
        super.onDraw(canvas)
        canvas.drawRect(0f, 0f, width.toFloat(), height.toFloat(), paintBackground)
        canvas.drawRect(offsetX, offsetY, offsetX + cellSize * cols, offsetY + cellSize * rows, paintBoard)

        for (x in 0..cols) canvas.drawLine(offsetX + x * cellSize, offsetY, offsetX + x * cellSize, offsetY + rows * cellSize, paintGrid)
        for (y in 0..rows) canvas.drawLine(offsetX, offsetY + y * cellSize, offsetX + cols * cellSize, offsetY + y * cellSize, paintGrid)

        if (skinIndex == 5) {
            rainbowPhase = (rainbowPhase + 0.5f) % 360f
            for (x in 0 until cols) for (y in 0 until rows) {
                val ci = ((boardMatrix[x][y] * 360 + rainbowPhase).toInt() % 360)
                paintGrid.color = rainbowColors[ci]
                canvas.drawRect(offsetX + x * cellSize, offsetY + y * cellSize, offsetX + (x + 1) * cellSize, offsetY + (y + 1) * cellSize, paintGrid)
            }
        }

        val foodCX = offsetX + food.x * cellSize + cellSize / 2
        val foodCY = offsetY + food.y * cellSize + cellSize / 2
        paintFood.shader = RadialGradient(foodCX, foodCY, cellSize / 2, Color.RED, Color.parseColor("#FFEB3B"), Shader.TileMode.CLAMP)
        canvas.drawCircle(foodCX, foodCY, cellSize / 2.5f, paintFood)

        for (i in snake.size - 1 downTo 1) {
            val p = snake[i]
            if (skinIndex == 5) paintSnakeBody.color = rainbowColors[((i * 12 + rainbowPhase).toInt() % 360)]
            canvas.drawRoundRect(offsetX + p.x * cellSize + 2, offsetY + p.y * cellSize + 2, offsetX + (p.x + 1) * cellSize - 2, offsetY + (p.y + 1) * cellSize - 2, 10f, 10f, paintSnakeBody)
        }

        val head = snake.first()
        if (skinIndex == 5) paintSnakeHead.color = Color.WHITE
        canvas.drawRoundRect(offsetX + head.x * cellSize + 1, offsetY + head.y * cellSize + 1, offsetX + (head.x + 1) * cellSize - 1, offsetY + (head.y + 1) * cellSize - 1, 12f, 12f, paintSnakeHead)

        val eOff = cellSize / 4; val eR = cellSize / 10
        val hL = offsetX + head.x * cellSize + 1; val hT = offsetY + head.y * cellSize + 1
        val hR = offsetX + (head.x + 1) * cellSize - 1; val hB = offsetY + (head.y + 1) * cellSize - 1
        when {
            dir.x == 1 -> {
                canvas.drawCircle(hR - eOff, hT + eOff, eR, paintEyes); canvas.drawCircle(hR - eOff, hB - eOff, eR, paintEyes)
                canvas.drawCircle(hR - eOff + 2, hT + eOff, eR / 2, paintPupils); canvas.drawCircle(hR - eOff + 2, hB - eOff, eR / 2, paintPupils)
            }
            dir.x == -1 -> {
                canvas.drawCircle(hL + eOff, hT + eOff, eR, paintEyes); canvas.drawCircle(hL + eOff, hB - eOff, eR, paintEyes)
                canvas.drawCircle(hL + eOff - 2, hT + eOff, eR / 2, paintPupils); canvas.drawCircle(hL + eOff - 2, hB - eOff, eR / 2, paintPupils)
            }
            dir.y == 1 -> {
                canvas.drawCircle(hL + eOff, hB - eOff, eR, paintEyes); canvas.drawCircle(hR - eOff, hB - eOff, eR, paintEyes)
                canvas.drawCircle(hL + eOff, hB - eOff + 2, eR / 2, paintPupils); canvas.drawCircle(hR - eOff, hB - eOff + 2, eR / 2, paintPupils)
            }
            else -> {
                canvas.drawCircle(hL + eOff, hT + eOff, eR, paintEyes); canvas.drawCircle(hR - eOff, hT + eOff, eR, paintEyes)
                canvas.drawCircle(hL + eOff, hT + eOff - 2, eR / 2, paintPupils); canvas.drawCircle(hR - eOff, hT + eOff - 2, eR / 2, paintPupils)
            }
        }

        if (snake.size > 1 && !isGameOver && snake.size % TRAIL_PARTICLE_INTERVAL == 0) {
            val tail = snake.last()
            spawnParticle(offsetX + tail.x * cellSize + cellSize / 2, offsetY + tail.y * cellSize + cellSize / 2, currentBodyColor)
        }

        updateParticles()
        for (p in particles) {
            paintParticles.color = p.color; paintParticles.alpha = p.alpha
            canvas.drawCircle(p.x, p.y, p.size, paintParticles)
        }
        paintParticles.alpha = 255

        canvas.drawText("Score: $score", (width / 2).toFloat(), 100f, paintText)
        canvas.drawText("High: $highScore", (width / 2).toFloat(), 150f, paintTextSmall)
        canvas.drawText("Money: $money", (width / 2).toFloat(), 190f, paintTextSmall)

        if (isGameOver) {
            paintText.textSize = 80f
            canvas.drawText("GAME OVER", (width / 2).toFloat(), (height / 2 - 50).toFloat(), paintText)
            paintText.textSize = 40f
            canvas.drawText("Tap to Restart", (width / 2).toFloat(), (height / 2 + 20).toFloat(), paintText)
            paintText.textSize = 60f
        }
    }

    // ====================== 触摸控制 ======================

    override fun onTouchEvent(event: MotionEvent): Boolean {
        if (event.action == MotionEvent.ACTION_DOWN) {
            if (isGameOver) { reset(); return true }
            val dx = event.x - width / 2f
            val dy = event.y - height / 2f
            val newDir = when {
                Math.abs(dx) > Math.abs(dy) -> if (dx > 0) Point(1, 0) else Point(-1, 0)
                else -> if (dy > 0) Point(0, 1) else Point(0, -1)
            }
            if (!(newDir.x == -dir.x && newDir.y == -dir.y) && directionQueue.size < MAX_DIRECTION_QUEUE) {
                directionQueue.add(newDir)
            }
            performClick(); return true
        }
        return super.onTouchEvent(event)
    }

    override fun performClick(): Boolean { super.performClick(); return true }

    // ====================== 震动 ======================

    private fun vibrate(duration: Long) {
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            vibrator.vibrate(VibrationEffect.createOneShot(duration, VibrationEffect.DEFAULT_AMPLITUDE))
        } else {
            @Suppress("DEPRECATION") vibrator.vibrate(duration)
        }
    }

    // ====================== 外部接口 ======================

    fun setSkin(index: Int) { skinIndex = index; applySkin(); invalidate() }
    fun setAiMode(mode: Int) {
        aiMode = mode
        directionQueue.clear()
        reset()
    }
    fun getScore(): Int = score
    fun getHighScore(): Int = highScore
    fun getMoney(): Int = money
    fun isGameOver(): Boolean = isGameOver
}
