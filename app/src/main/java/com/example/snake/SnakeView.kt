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
import android.view.Choreographer
import android.view.MotionEvent
import android.view.View
import kotlin.math.abs
import kotlin.math.max
import kotlin.math.sin
import kotlin.math.cos
import kotlin.math.atan2
import kotlin.math.PI
import kotlin.random.Random

class SnakeView(context: Context) : View(context) {

    private val cols = 15
    private val rows = 15

    private var cellSize = 0f
    private var offsetX = 0f
    private var offsetY = 0f

    private data class Point(val x: Int, val y: Int)
    private val snake = ArrayDeque<Point>()
    private val directionQueue = ArrayDeque<Point>()

    private var dir = Point(0, 0)
    private var nextDir = Point(0, 0)

    private var food = Point(5, 5)
    private var score = 0
    private var highScore = 0
    private var gameOver = false
    private var running = false

    private var gameSpeed = 180L

    // AI 模式：0 = 手动, 1 = BFS, 2 = HAM
    private var aiMode = 0

    var onScoreChanged: ((Int) -> Unit)? = null
    var onMoneyChanged: ((Int) -> Unit)? = null
    var onAIModeChanged: ((Int) -> Unit)? = null

    private val prefs = context.getSharedPreferences("snake_prefs", Context.MODE_PRIVATE)

    private var aiLevel = 1
    private var aiBestScore = 0
    private var comboCount = 0
    private var currentMultiplier = 1.0f
    private var hungerCounter = 0
    private var consecutiveDeaths = 0

    private val pathIndex = Array(cols) { IntArray(rows) }
    private val pathSequence = mutableListOf<Point>()

    private var currentSkinBodyColor = Color.rgb(46, 204, 113)
    private var currentSkinHeadColor = Color.rgb(39, 174, 96)
    private var currentBoardBgColor = Color.BLACK
    private var currentBoardGridColor = Color.rgb(0, 255, 255)

    private var isRainbowSkin = false

    private val rainbowColors = IntArray(361) { i ->
        Color.HSVToColor(floatArrayOf(i.toFloat(), 1f, 1f))
    }

    private val vibrator: Vibrator? = if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
        val vibratorManager = context.getSystemService(Context.VIBRATOR_MANAGER_SERVICE) as? VibratorManager
        vibratorManager?.defaultVibrator
    } else {
        @Suppress("DEPRECATION")
        context.getSystemService(Context.VIBRATOR_SERVICE) as? Vibrator
    }

    private var deathFlashAlpha = 0f
    private var shakeTime = 0f
    private var shakeOffsetX = 0f
    private var shakeOffsetY = 0f

    private var shockwaveX = 0f
    private var shockwaveY = 0f
    private var shockwaveRadius = 0f
    private var shockwaveAlpha = 0f

    private data class Particle(
        var x: Float, var y: Float,
        var vx: Float, var vy: Float,
        var life: Float, val color: Int,
        var size: Float = 1f,
        var decay: Float = 0.002f,
        var isTrail: Boolean = false
    )

    private data class FloatingText(
        var x: Float, var y: Float,
        var life: Float, val text: String
    )

    private val particles = mutableListOf<Particle>()
    private val floatingTexts = mutableListOf<FloatingText>()

    private val paintSnakeBody = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = currentSkinBodyColor
        style = Paint.Style.STROKE
        strokeCap = Paint.Cap.ROUND
        strokeJoin = Paint.Join.ROUND
        pathEffect = CornerPathEffect(30f)
        setShadowLayer(20f, 0f, 0f, currentSkinBodyColor)
    }

    private val paintSnakeHead = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = currentSkinHeadColor
        style = Paint.Style.FILL
        setShadowLayer(15f, 0f, 0f, currentSkinHeadColor)
    }

    private val paintSnakeHighlight = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.WHITE
        style = Paint.Style.FILL
        alpha = 100
    }

    private val paintEyeWhite = Paint(Paint.ANTI_ALIAS_FLAG).apply { color = Color.WHITE }
    private val paintEyeBlack = Paint(Paint.ANTI_ALIAS_FLAG).apply { color = Color.BLACK }

    private val paintFoodGlow = Paint(Paint.ANTI_ALIAS_FLAG).apply { style = Paint.Style.FILL }
    private val paintFoodCore = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.WHITE
        style = Paint.Style.FILL
    }
    private val paintFoodCross = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.WHITE
        style = Paint.Style.STROKE
        strokeWidth = 3f
        setShadowLayer(15f, 0f, 0f, Color.CYAN)
    }

    private val paintParticle = Paint(Paint.ANTI_ALIAS_FLAG).apply { style = Paint.Style.FILL }
    private val paintFloatingText = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.rgb(241, 196, 15)
        textSize = 45f
        textAlign = Paint.Align.CENTER
        setShadowLayer(10f, 0f, 0f, Color.BLACK)
    }

    private val paintGrid = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        strokeWidth = 2f
        setShadowLayer(8f, 0f, 0f, Color.CYAN)
    }

    private val paintShockwave = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        style = Paint.Style.STROKE
        strokeWidth = 8f
        color = Color.RED
    }

    private val paintText = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.WHITE
        textAlign = Paint.Align.CENTER
    }
    private val paintSubText = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.LTGRAY
        textAlign = Paint.Align.CENTER
    }

    private val paintHamPath = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        style = Paint.Style.STROKE
        strokeWidth = 3f
        color = Color.argb(60, 255, 255, 255)
    }

    private var isRainbowBoard = false
    private val paintBoardBg = Paint(Paint.ANTI_ALIAS_FLAG).apply { style = Paint.Style.FILL }
    private val boardMatrix = Matrix()

    private var lastFrameTime = 0L
    private var timeAccumulator = 0L

    private val frameCallback = object : Choreographer.FrameCallback {
        override fun doFrame(frameTimeNanos: Long) {
            if (!running) return
            val currentTime = System.nanoTime()
            if (lastFrameTime == 0L) lastFrameTime = currentTime
            val deltaTime = (currentTime - lastFrameTime) / 1_000_000f
            lastFrameTime = currentTime
            timeAccumulator += deltaTime.toLong()
            if (timeAccumulator >= gameSpeed) {
                update()
                timeAccumulator -= gameSpeed
            }
            updateEffects(deltaTime)
            invalidate()
            Choreographer.getInstance().postFrameCallback(this)
        }
    }

    init {
        initHamiltonianPath()
        aiBestScore = prefs.getInt("ai_best_score", 0)
        aiLevel = prefs.getInt("ai_level", 1)
        consecutiveDeaths = prefs.getInt("consecutive_deaths", 0)
        highScore = prefs.getInt("high_score", 0)
        updateCurrentSkin()
        updateCurrentBoard()
        reset()
    }

    private fun initHamiltonianPath() {
        pathSequence.clear()
        for (c in 0 until cols) {
            if (c % 2 == 0) {
                for (r in 0 until rows) {
                    pathIndex[c][r] = pathSequence.size
                    pathSequence.add(Point(c, r))
                }
            } else {
                for (r in rows - 1 downTo 0) {
                    pathIndex[c][r] = pathSequence.size
                    pathSequence.add(Point(c, r))
                }
            }
        }
    }

    fun getAIMode(): Int = aiMode

    fun setAIMode(mode: Int) {
        aiMode = mode
        onAIModeChanged?.invoke(aiMode)
        reset()
    }

    fun updateCurrentSkin() {
        val currentSkinId = prefs.getString("equipped_skin", "green") ?: "green"
        isRainbowSkin = false
        when (currentSkinId) {
            "blue" -> {
                currentSkinBodyColor = Color.rgb(52, 152, 219)
                currentSkinHeadColor = Color.rgb(41, 128, 185)
            }
            "red" -> {
                currentSkinBodyColor = Color.rgb(231, 76, 60)
                currentSkinHeadColor = Color.rgb(192, 57, 43)
            }
            "purple" -> {
                currentSkinBodyColor = Color.rgb(155, 89, 182)
                currentSkinHeadColor = Color.rgb(142, 68, 173)
            }
            "gold" -> {
                currentSkinBodyColor = Color.rgb(241, 196, 15)
                currentSkinHeadColor = Color.rgb(243, 156, 18)
            }
            "rainbow" -> {
                isRainbowSkin = true
                currentSkinBodyColor = Color.WHITE
                currentSkinHeadColor = Color.WHITE
                paintSnakeBody.setShadowLayer(35f, 0f, 0f, Color.WHITE)
            }
            else -> {
                currentSkinBodyColor = Color.rgb(46, 204, 113)
                currentSkinHeadColor = Color.rgb(39, 174, 96)
            }
        }
        if (!isRainbowSkin) {
            paintSnakeBody.shader = null
            paintSnakeBody.color = currentSkinBodyColor
            paintSnakeBody.setShadowLayer(20f, 0f, 0f, currentSkinBodyColor)
            paintSnakeHead.color = currentSkinHeadColor
            paintSnakeHead.setShadowLayer(15f, 0f, 0f, currentSkinHeadColor)
        }
        invalidate()
    }

    fun updateCurrentBoard() {
        val currentBoardId = prefs.getString("equipped_board", "dark") ?: "dark"
        when (currentBoardId) {
            "light" -> {
                isRainbowBoard = false
                paintBoardBg.shader = null
                currentBoardBgColor = Color.rgb(240, 240, 240)
                currentBoardGridColor = Color.rgb(200, 200, 200)
                paintGrid.setShadowLayer(0f, 0f, 0f, Color.TRANSPARENT)
            }
            "neon" -> {
                isRainbowBoard = false
                paintBoardBg.shader = null
                currentBoardBgColor = Color.rgb(10, 25, 47)
                currentBoardGridColor = Color.rgb(0, 255, 255)
                paintGrid.setShadowLayer(8f, 0f, 0f, Color.CYAN)
            }
            "forest" -> {
                isRainbowBoard = false
                paintBoardBg.shader = null
                currentBoardBgColor = Color.rgb(27, 46, 26)
                currentBoardGridColor = Color.rgb(46, 74, 45)
                paintGrid.setShadowLayer(0f, 0f, 0f, Color.TRANSPARENT)
            }
            "cyberpunk" -> {
                isRainbowBoard = false
                paintBoardBg.shader = null
                currentBoardBgColor = Color.rgb(43, 15, 59)
                currentBoardGridColor = Color.rgb(200, 0, 255)
                paintGrid.setShadowLayer(8f, 0f, 0f, Color.MAGENTA)
            }
            "rainbow_board" -> {
                isRainbowBoard = true
                currentBoardBgColor = Color.BLACK
                currentBoardGridColor = Color.WHITE
                paintGrid.setShadowLayer(6f, 0f, 0f, Color.WHITE)
                val shader = LinearGradient(0f, 0f, 2000f, 2000f, rainbowColors, null, Shader.TileMode.MIRROR)
                paintBoardBg.shader = shader
            }
            else -> {
                isRainbowBoard = false
                paintBoardBg.shader = null
                currentBoardBgColor = Color.BLACK
                currentBoardGridColor = Color.rgb(0, 255, 255)
                paintGrid.setShadowLayer(8f, 0f, 0f, Color.CYAN)
            }
        }
        invalidate()
    }

    fun reset() {
        snake.clear()
        if (aiMode == 2) {
            snake.add(Point(0, 0))
            dir = Point(0, 1)
        } else {
            snake.add(Point(10, 10))
            dir = Point(0, 0)
        }
        nextDir = Point(0, 0)
        directionQueue.clear()
        score = 0
        comboCount = 0
        hungerCounter = 0
        currentMultiplier = 1.0f
        gameOver = false
        gameSpeed = 180L
        lastFrameTime = 0L
        timeAccumulator = 0L
        deathFlashAlpha = 0f
        shakeTime = 0f
        shakeOffsetX = 0f
        shakeOffsetY = 0f
        shockwaveRadius = 0f
        shockwaveAlpha = 0f
        particles.clear()
        floatingTexts.clear()

        if (isRainbowSkin) {
            paintSnakeBody.setShadowLayer(35f, 0f, 0f, Color.WHITE)
        } else {
            paintSnakeBody.color = currentSkinBodyColor
            paintSnakeBody.setShadowLayer(20f, 0f, 0f, currentSkinBodyColor)
            paintSnakeHead.color = currentSkinHeadColor
            paintSnakeHead.setShadowLayer(15f, 0f, 0f, currentSkinHeadColor)
        }

        placeFood()
        onScoreChanged?.invoke(score)
        invalidate()
    }

    fun resume() {
        if (!running) {
            running = true
            lastFrameTime = 0L
            timeAccumulator = 0L
            Choreographer.getInstance().postFrameCallback(frameCallback)
        }
    }

    fun pause() {
        running = false
        Choreographer.getInstance().removeFrameCallback(frameCallback)
    }

    private fun placeFood() {
        while (true) {
            val p = Point(Random.nextInt(cols), Random.nextInt(rows))
            if (snake.none { it == p }) {
                food = p
                return
            }
        }
    }

    private fun vibrate(duration: Long, amplitude: Int = VibrationEffect.DEFAULT_AMPLITUDE) {
        vibrator?.let {
            if (!it.hasVibrator()) return
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
                it.vibrate(VibrationEffect.createOneShot(duration, amplitude))
            } else {
                @Suppress("DEPRECATION")
                it.vibrate(duration)
            }
        }
    }

    private fun updateEffects(deltaTime: Float) {
        if (gameOver) {
            deathFlashAlpha = 120f + 60f * sin(System.currentTimeMillis() / 150.0).toFloat()
            if (shockwaveAlpha > 0) {
                shockwaveRadius += deltaTime * 1.5f
                shockwaveAlpha -= deltaTime * 0.15f
            }
        } else {
            if (deathFlashAlpha > 0) deathFlashAlpha = max(0f, deathFlashAlpha - deltaTime * 0.5f)
        }
        if (shakeTime > 0) {
            shakeTime -= deltaTime
            shakeOffsetX = (Random.nextFloat() - 0.5f) * 30f * (shakeTime / 400f)
            shakeOffsetY = (Random.nextFloat() - 0.5f) * 30f * (shakeTime / 400f)
        } else {
            shakeOffsetX = 0f
            shakeOffsetY = 0f
        }
        val iterator = particles.iterator()
        while (iterator.hasNext()) {
            val p = iterator.next()
            p.x += p.vx * (deltaTime / 16f)
            p.y += p.vy * (deltaTime / 16f)
            if (!p.isTrail) p.vy += 0.4f
            p.life -= deltaTime * p.decay
            if (p.life <= 0) iterator.remove()
        }
        val textIterator = floatingTexts.iterator()
        while (textIterator.hasNext()) {
            val t = textIterator.next()
            t.y -= 2.5f * (deltaTime / 16f)
            t.life -= deltaTime * 0.001f
            if (t.life <= 0) textIterator.remove()
        }
    }

    // ================== 最终版 BFS：多维度评估 + 四重安全网 ==================
    private fun autoPilotBFS() {
        if (gameOver) return
        val head = snake.first()

        // 第一步：物理安全方向
        val allDirs = listOf(Point(0, -1), Point(0, 1), Point(-1, 0), Point(1, 0))
        val validDirs = allDirs.filter { d ->
            val isReverse = (d.x == -dir.x && d.y == -dir.y)
            val newHead = Point(head.x + d.x, head.y + d.y)
            val isWall = newHead.x !in 0 until cols || newHead.y !in 0 until rows
            val isSelf = snake.dropLast(1).any { it == newHead }
            !isReverse && !isWall && !isSelf
        }
        if (validDirs.isEmpty()) return

        // 优先级 1：食物贴脸，且物理安全 → 直接吃
        val foodDx = food.x - head.x
        val foodDy = food.y - head.y
        if (abs(foodDx) + abs(foodDy) == 1) {
            val foodDir = Point(foodDx, foodDy)
            if (validDirs.contains(foodDir)) {
                directionQueue.clear()
                directionQueue.add(foodDir)
                return
            }
        }

        // 优先级 2：极度饥饿（>15步没吃到）→ 强制直奔食物，不管安全模拟
        if (hungerCounter > 15) {
            val pathToFood = bfsPathWithSnake(head, food, snake, dir)
            if (pathToFood != null && pathToFood.size > 1) {
                val nextMove = Point(pathToFood[1].x - pathToFood[0].x, pathToFood[1].y - pathToFood[0].y)
                if (validDirs.contains(nextMove)) {
                    directionQueue.clear()
                    directionQueue.add(nextMove)
                    return
                }
            }
        }

        // 优先级 3：对所有合法方向进行多维度评估打分
        var bestDir: Point? = null
        var bestScoreVal = Int.MIN_VALUE
        var bestDist = Int.MAX_VALUE

        for (d in validDirs) {
            val newHead = Point(head.x + d.x, head.y + d.y)
            val simSnake = ArrayDeque(snake)
            simSnake.addFirst(newHead)
            simSnake.removeLast()

            // 评估项 A：走完后食物可达吗？
            val foodPath = bfsPathWithSnake(newHead, food, simSnake, Point(0, 0))
            val foodReachable = foodPath != null
            val distToFood = foodPath?.size ?: Int.MAX_VALUE

            // 评估项 B：走完后能追到尾巴吗？
            val canReachTail = bfsPathWithSnake(newHead, simSnake.last(), simSnake, Point(0, 0)) != null

            // 评估项 C：走完后活动空间有多大？
            val space = floodFillWithSnake(newHead, simSnake)

            // 综合打分
            var localScore = 0
            if (foodReachable) localScore += 40
            if (canReachTail) localScore += 30
            if (space > snake.size * 1.5f) localScore += 30

            // 饥饿程度越高，越重视"离食物更近"
            if (hungerCounter > 8) {
                if (distToFood < 10) localScore += 20
                else if (distToFood < 20) localScore += 10
            }

            // 极端危险方向（食物不可达 + 追不到尾巴 + 空间小）：直接排除
            val isDeadEnd = !foodReachable && !canReachTail && space < snake.size
            if (isDeadEnd) continue

            // 比较：优先总分高，其次离食物近
            val better = when {
                localScore > bestScoreVal -> true
                localScore < bestScoreVal -> false
                distToFood < bestDist -> true
                else -> false
            }
            if (better) {
                bestScoreVal = localScore
                bestDir = d
                bestDist = distToFood
            }
        }

        if (bestDir != null) {
            directionQueue.clear()
            directionQueue.add(bestDir)
            return
        }

        // 兜底：如果所有方向都被评估为"死路"，选空间最大的那个拖延时间
        var fallbackMove: Point? = null
        var maxSpace = -1
        for (d in validDirs) {
            val newHead = Point(head.x + d.x, head.y + d.y)
            val simSnake = ArrayDeque(snake)
            simSnake.addFirst(newHead)
            simSnake.removeLast()
            val space = floodFillWithSnake(newHead, simSnake)
            if (space > maxSpace) {
                maxSpace = space
                fallbackMove = d
            }
        }
        if (fallbackMove != null) {
            directionQueue.clear()
            directionQueue.add(fallbackMove)
        }
    }
    // =======================================================

    // 吃完食物后是否安全（用于"食物贴脸"时的二次验证——只在蛇很长时用）
    private fun isEatingSafe(head: Point, foodPos: Point): Boolean {
        val simSnake = ArrayDeque(snake)
        simSnake.addFirst(foodPos)

        val newHead = simSnake.first()
        val newTail = simSnake.last()

        val spaceAfterEating = floodFillWithSnake(newHead, simSnake)
        if (spaceAfterEating > simSnake.size * 1.2f) return true
        if (spaceAfterEating < simSnake.size * 0.7f) return false
        return bfsPathWithSnake(newHead, newTail, simSnake, Point(0, 0)) != null
    }

    // ================== 汉密尔顿路径跟随 ==================
    private fun autoPilotHamiltonian() {
        if (gameOver) return
        val head = snake.first()
        if (head.x !in 0 until cols || head.y !in 0 until rows) return

        val currentIndex = pathIndex[head.x][head.y]
        val nextIndex = (currentIndex + 1) % pathSequence.size
        val nextPoint = pathSequence[nextIndex]

        val dx = nextPoint.x - head.x
        val dy = nextPoint.y - head.y

        val newHead = Point(head.x + dx, head.y + dy)
        val isSelfCollision = snake.dropLast(1).any { it == newHead }

        if (isSelfCollision) {
            val nextNextIndex = (nextIndex + 1) % pathSequence.size
            val nextNextPoint = pathSequence[nextNextIndex]
            val dx2 = nextNextPoint.x - head.x
            val dy2 = nextNextPoint.y - head.y
            if (abs(dx2) + abs(dy2) == 1) {
                dir = Point(dx2, dy2)
                return
            }
            return
        }

        dir = Point(dx, dy)
    }
    // =======================================================

    private fun floodFillWithSnake(start: Point, currentSnake: Collection<Point>): Int {
        val queue = ArrayDeque<Point>()
        val visited = mutableSetOf<Point>()
        queue.add(start)
        visited.add(start)
        while (queue.isNotEmpty()) {
            val curr = queue.removeFirst()
            for (d in listOf(Point(0, -1), Point(0, 1), Point(-1, 0), Point(1, 0))) {
                val next = Point(curr.x + d.x, curr.y + d.y)
                if (next.x !in 0 until cols || next.y !in 0 until rows) continue
                if (currentSnake.any { it == next }) continue
                if (visited.contains(next)) continue
                visited.add(next)
                queue.add(next)
            }
        }
        return visited.size
    }

    private fun bfsPathWithSnake(start: Point, target: Point, customSnake: Collection<Point>, reverseDir: Point): List<Point>? {
        val queue = ArrayDeque<Point>()
        val visited = mutableSetOf<Point>()
        val parent = mutableMapOf<Point, Point>()
        queue.add(start)
        visited.add(start)

        while (queue.isNotEmpty()) {
            val curr = queue.removeFirst()
            if (curr == target) {
                val path = mutableListOf<Point>()
                var node = curr
                while (node != start) {
                    path.add(0, node)
                    node = parent[node]!!
                }
                return path
            }
            for (d in listOf(Point(0, -1), Point(0, 1), Point(-1, 0), Point(1, 0))) {
                if (curr == start && d.x == reverseDir.x && d.y == reverseDir.y) continue
                val next = Point(curr.x + d.x, curr.y + d.y)
                if (next.x !in 0 until cols || next.y !in 0 until rows) continue
                if (customSnake.any { it == next } && next != target) continue
                if (visited.contains(next)) continue
                visited.add(next)
                parent[next] = curr
                queue.add(next)
            }
        }
        return null
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
            2 -> {
                autoPilotHamiltonian()
            }
            else -> {
                if (directionQueue.isNotEmpty()) {
                    val next = directionQueue.removeFirst()
                    if (dir.x == 0 && dir.y == 0) dir = next
                    else if (dir.x != -next.x || dir.y != -next.y) dir = next
                }
            }
        }

        if (dir.x == 0 && dir.y == 0) return

        val head = snake.first()
        val newHead = Point(head.x + dir.x, head.y + dir.y)

        if (newHead.x < 0 || newHead.x >= cols || newHead.y < 0 || newHead.y >= rows) {
            gameOver = true
            triggerDeathEffects()
            saveScoreAndMoney()
            return
        }

        val isEating = newHead == food
        val tail = snake.last()
        val collidedWithSelf = if (newHead == tail) isEating else snake.any { it == newHead }

        if (collidedWithSelf) {
            gameOver = true
            triggerDeathEffects()
            saveScoreAndMoney()
            return
        }

        // 拖尾粒子
        val tailX = offsetX + tail.x * cellSize + cellSize / 2
        val tailY = offsetY + tail.y * cellSize + cellSize / 2

        val trailColor = if (isRainbowSkin) {
            Color.HSVToColor(floatArrayOf((System.currentTimeMillis() / 10f) % 360f, 1f, 1f))
        } else {
            currentSkinBodyColor
        }

        particles.add(
            Particle(
                x = tailX + (Random.nextFloat() - 0.5f) * cellSize * 0.5f,
                y = tailY + (Random.nextFloat() - 0.5f) * cellSize * 0.5f,
                vx = (Random.nextFloat() - 0.5f) * 1.5f,
                vy = (Random.nextFloat() - 0.5f) * 1.5f,
                life = 1.0f, color = trailColor,
                size = Random.nextFloat() * 0.8f + 0.5f,
                decay = 0.003f,
                isTrail = true
            )
        )

        snake.addFirst(newHead)
        if (isEating) {
            hungerCounter = 0
            comboCount++
            val basePoints = 10 + (comboCount - 1) * 5
            currentMultiplier = when {
                score >= 1000 -> 3.0f
                score >= 500 -> 2.0f
                score >= 200 -> 1.5f
                else -> 1.0f
            }
            val earnedPoints = (basePoints * currentMultiplier).toInt()
            score += earnedPoints
            onScoreChanged?.invoke(score)
            triggerEatEffects(earnedPoints)
            placeFood()
            gameSpeed = max(70L, gameSpeed - 3L)
        } else {
            hungerCounter++
            snake.removeLast()
        }
    }

    private fun triggerEatEffects(scoreGained: Int) {
        vibrate(35, 100)
        val foodCenterX = offsetX + food.x * cellSize + cellSize / 2
        val foodCenterY = offsetY + food.y * cellSize + cellSize / 2
        val colors = intArrayOf(
            Color.rgb(231, 76, 60), Color.rgb(241, 196, 15),
            Color.rgb(46, 204, 113), Color.rgb(52, 152, 219),
            Color.WHITE, Color.CYAN
        )
        for (i in 0 until 25) {
            val angle = Random.nextFloat() * 2 * PI
            val speed = Random.nextFloat() * 8f + 2f
            particles.add(
                Particle(
                    x = foodCenterX, y = foodCenterY,
                    vx = cos(angle).toFloat() * speed,
                    vy = sin(angle).toFloat() * speed,
                    life = 1.0f, color = colors[Random.nextInt(colors.size)],
                    size = Random.nextFloat() * 1.5f + 0.5f,
                    decay = 0.0015f
                )
            )
        }
        floatingTexts.add(FloatingText(foodCenterX, foodCenterY, 1.0f, "+$scoreGained"))
    }

    private fun triggerDeathEffects() {
        vibrate(35, 100)
        vibrator?.let {
            if (it.hasVibrator()) {
                if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
                    val timings = longArrayOf(0, 100, 50, 200, 50, 300, 100, 400)
                    val amplitudes = intArrayOf(0, 255, 0, 200, 0, 150, 0, 80)
                    it.vibrate(VibrationEffect.createWaveform(timings, amplitudes, -1))
                } else {
                    @Suppress("DEPRECATION")
                    it.vibrate(longArrayOf(0, 100, 50, 200, 50, 300, 100, 400), -1)
                }
            }
        }
        shakeTime = 400f
        deathFlashAlpha = 255f

        val headX = offsetX + snake.first().x * cellSize + cellSize / 2
        val headY = offsetY + snake.first().y * cellSize + cellSize / 2
        shockwaveX = headX
        shockwaveY = headY
        shockwaveRadius = cellSize
        shockwaveAlpha = 255f

        paintSnakeBody.color = Color.rgb(200, 50, 50)
        paintSnakeBody.setShadowLayer(20f, 0f, 0f, Color.rgb(200, 50, 50))
        paintSnakeHead.color = Color.rgb(150, 0, 0)
        paintSnakeHead.setShadowLayer(15f, 0f, 0f, Color.rgb(150, 0, 0))

        for (i in 0 until 60) {
            val angle = Random.nextFloat() * 2 * PI
            val speed = Random.nextFloat() * 12f + 3f
            particles.add(
                Particle(
                    x = headX, y = headY,
                    vx = cos(angle).toFloat() * speed,
                    vy = sin(angle).toFloat() * speed,
                    life = 1.5f, color = Color.rgb(255, 50, 50),
                    size = Random.nextFloat() * 2f + 1f,
                    decay = 0.002f
                )
            )
        }

        if (aiMode != 0) {
            aiMode = 0
            onAIModeChanged?.invoke(aiMode)
        }
    }

    private fun saveScoreAndMoney() {
        if (score > highScore) {
            highScore = score
            prefs.edit().putInt("high_score", highScore).apply()
        }
        var currentMoney = prefs.getInt("money", 0)
        currentMoney += score
        prefs.edit().putInt("money", currentMoney).apply()
        onMoneyChanged?.invoke(currentMoney)

        if (score > aiBestScore) {
            aiBestScore = score
            prefs.edit().putInt("ai_best_score", aiBestScore).apply()
            if (score > 100) {
                aiLevel = (aiLevel + 1).coerceAtMost(10)
                prefs.edit().putInt("ai_level", aiLevel).apply()
            }
            consecutiveDeaths = 0
            prefs.edit().putInt("consecutive_deaths", 0).apply()
        } else {
            if (score < 50) {
                consecutiveDeaths++
                prefs.edit().putInt("consecutive_deaths", consecutiveDeaths).apply()
                if (consecutiveDeaths >= 2 || score < aiBestScore * 0.3) {
                    aiLevel = (aiLevel - 1).coerceAtLeast(1)
                    prefs.edit().putInt("ai_level", aiLevel).apply()
                    consecutiveDeaths = 0
                    prefs.edit().putInt("consecutive_deaths", 0).apply()
                }
            } else {
                consecutiveDeaths = 0
                prefs.edit().putInt("consecutive_deaths", 0).apply()
            }
        }
    }

    override fun onDraw(canvas: Canvas) {
        super.onDraw(canvas)

        cellSize = minOf(width / cols.toFloat(), height / rows.toFloat())
        offsetX = (width - cellSize * cols) / 2f
        offsetY = (height - cellSize * rows) / 2f

        if (isRainbowBoard) {
            val time = System.currentTimeMillis() % 5000L
            boardMatrix.setTranslate(time * 0.15f, time * 0.15f)
            paintBoardBg.shader?.setLocalMatrix(boardMatrix)
            canvas.drawRect(offsetX, offsetY, offsetX + cols * cellSize, offsetY + rows * cellSize, paintBoardBg)
        } else {
            canvas.drawColor(currentBoardBgColor)
        }

        canvas.save()
        if (gameOver && shakeTime > 0) canvas.translate(shakeOffsetX, shakeOffsetY)

        val breath = (sin(System.currentTimeMillis() / 400.0).toFloat() + 1f) / 2f
        val gridAlpha = (60 + 195 * breath).toInt()
        paintGrid.alpha = gridAlpha
        paintGrid.color = currentBoardGridColor

        for (i in 0..cols) {
            val x = offsetX + i * cellSize
            canvas.drawLine(x, offsetY, x, offsetY + rows * cellSize, paintGrid)
        }
        for (i in 0..rows) {
            val y = offsetY + i * cellSize
            canvas.drawLine(offsetX, y, offsetX + cols * cellSize, y, paintGrid)
        }

        if (aiMode == 2 && !gameOver) {
            for (i in 0 until pathSequence.size - 1) {
                val p1 = pathSequence[i]
                val p2 = pathSequence[i + 1]
                val x1 = offsetX + p1.x * cellSize + cellSize / 2
                val y1 = offsetY + p1.y * cellSize + cellSize / 2
                val x2 = offsetX + p2.x * cellSize + cellSize / 2
                val y2 = offsetY + p2.y * cellSize + cellSize / 2
                canvas.drawLine(x1, y1, x2, y2, paintHamPath)
            }
        }

        val foodCenterX = offsetX + food.x * cellSize + cellSize / 2
        val foodCenterY = offsetY + food.y * cellSize + cellSize / 2
        val pulse = 1f + 0.25f * sin(System.currentTimeMillis() / 150.0).toFloat()
        val foodRadius = cellSize * 0.4f * pulse

        val glowColors = intArrayOf(
            Color.argb(200, 0, 255, 255),
            Color.argb(100, 0, 200, 255),
            Color.argb(0, 0, 0, 0)
        )
        val glowPositions = floatArrayOf(0.0f, 0.5f, 1.0f)
        val radialGradient = RadialGradient(
            foodCenterX, foodCenterY, foodRadius * 2.2f,
            glowColors, glowPositions, Shader.TileMode.CLAMP
        )
        paintFoodGlow.shader = radialGradient
        canvas.drawCircle(foodCenterX, foodCenterY, foodRadius * 2.2f, paintFoodGlow)

        val rotation = (System.currentTimeMillis() % 3600) / 10f
        canvas.save()
        canvas.rotate(rotation, foodCenterX, foodCenterY)
        paintFoodCross.alpha = 220
        val crossLength = foodRadius * 1.6f
        canvas.drawLine(foodCenterX - crossLength, foodCenterY, foodCenterX + crossLength, foodCenterY, paintFoodCross)
        canvas.drawLine(foodCenterX, foodCenterY - crossLength, foodCenterX, foodCenterY + crossLength, paintFoodCross)
        canvas.rotate(45f, foodCenterX, foodCenterY)
        canvas.drawLine(foodCenterX - crossLength * 0.7f, foodCenterY, foodCenterX + crossLength * 0.7f, foodCenterY, paintFoodCross)
        canvas.drawLine(foodCenterX, foodCenterY - crossLength * 0.7f, foodCenterX, foodCenterY + crossLength * 0.7f, paintFoodCross)
        canvas.restore()

        paintFoodCore.alpha = 255
        canvas.drawCircle(foodCenterX, foodCenterY, foodRadius * 0.35f, paintFoodCore)

        if (snake.isNotEmpty()) {
            val progress = if (gameOver) 0f else (timeAccumulator.toFloat() / gameSpeed).coerceIn(0f, 1f)
            val path = Path()
            val points = snake.mapIndexed { index, p ->
                var baseX = offsetX + p.x * cellSize + cellSize / 2
                var baseY = offsetY + p.y * cellSize + cellSize / 2
                if (index == 0 && !gameOver) {
                    val prevP = if (snake.size > 1) snake[1] else Point(snake[0].x - dir.x, snake[0].y - dir.y)
                    val prevX = offsetX + prevP.x * cellSize + cellSize / 2
                    val prevY = offsetY + prevP.y * cellSize + cellSize / 2
                    baseX = prevX + (baseX - prevX) * progress
                    baseY = prevY + (baseY - prevY) * progress
                }
                val t = System.currentTimeMillis() / 200.0
                val swingAmplitude = if (dir.x != 0) cellSize * 0.1f else cellSize * 0.05f
                val swingX = sin(t + index * 0.5).toFloat() * swingAmplitude
                val swingY = cos(t + index * 0.5).toFloat() * swingAmplitude
                PointF(baseX + swingX, baseY + swingY)
            }
            path.moveTo(points[0].x, points[0].y)
            for (i in 1 until points.size) {
                val prev = points[i - 1]
                val curr = points[i]
                path.quadTo(prev.x, prev.y, (prev.x + curr.x) / 2f, (prev.y + curr.y) / 2f)
            }
            if (points.size > 1) path.lineTo(points.last().x, points.last().y)

            if (isRainbowSkin) {
                val headX = points.first().x
                val headY = points.first().y
                val tailX = points.last().x
                val tailY = points.last().y

                val angle = atan2(tailY - headY, tailX - headX)
                val timeOffset = (System.currentTimeMillis() % 3000) / 3000f
                val flowDistance = cellSize * 6 * timeOffset

                val startX = headX - cos(angle) * flowDistance
                val startY = headY - sin(angle) * flowDistance
                val endX = tailX - cos(angle) * flowDistance
                val endY = tailY - sin(angle) * flowDistance

                val shader = LinearGradient(
                    startX, startY,
                    endX, endY,
                    rainbowColors, null, Shader.TileMode.MIRROR
                )
                paintSnakeBody.shader = shader
                paintSnakeHead.color = Color.WHITE
                paintSnakeBody.alpha = 255
                paintSnakeBody.setShadowLayer(35f, 0f, 0f, Color.WHITE)
            } else {
                paintSnakeBody.shader = null
                paintSnakeBody.color = currentSkinBodyColor
                paintSnakeBody.alpha = 255
                paintSnakeBody.setShadowLayer(20f, 0f, 0f, currentSkinBodyColor)
            }

            paintSnakeBody.strokeWidth = cellSize * 0.8f
            paintSnakeBody.alpha = if (isRainbowSkin) 150 else 120
            canvas.drawPath(path, paintSnakeBody)

            paintSnakeBody.strokeWidth = cellSize * 0.65f
            paintSnakeBody.alpha = 255
            canvas.drawPath(path, paintSnakeBody)

            val headPoint = points.first()
            canvas.drawCircle(headPoint.x, headPoint.y, cellSize * 0.5f, paintSnakeHead)
            canvas.drawCircle(headPoint.x - cellSize * 0.1f, headPoint.y - cellSize * 0.1f, cellSize * 0.15f, paintSnakeHighlight)

            val currentDir = if (dir.x == 0 && dir.y == 0) Point(1, 0) else dir
            val eyeOffset = cellSize * 0.2f
            val perpOffsetX = -currentDir.y * (cellSize * 0.2f)
            val perpOffsetY = currentDir.x * (cellSize * 0.2f)

            canvas.drawCircle(headPoint.x + currentDir.x * eyeOffset + perpOffsetX, headPoint.y + currentDir.y * eyeOffset + perpOffsetY, cellSize * 0.12f, paintEyeWhite)
            canvas.drawCircle(headPoint.x + currentDir.x * eyeOffset - perpOffsetX, headPoint.y + currentDir.y * eyeOffset - perpOffsetY, cellSize * 0.12f, paintEyeWhite)
            canvas.drawCircle(headPoint.x + currentDir.x * eyeOffset * 1.2f + perpOffsetX, headPoint.y + currentDir.y * eyeOffset * 1.2f + perpOffsetY, cellSize * 0.06f, paintEyeBlack)
            canvas.drawCircle(headPoint.x + currentDir.x * eyeOffset * 1.2f - perpOffsetX, headPoint.y + currentDir.y * eyeOffset * 1.2f - perpOffsetY, cellSize * 0.06f, paintEyeBlack)
        }

        particles.forEach { p ->
            paintParticle.color = p.color
            paintParticle.alpha = (p.life * 255).toInt().coerceIn(0, 255)
            if (p.isTrail) {
                canvas.drawCircle(p.x, p.y, cellSize * 0.1f * p.life * p.size, paintParticle)
            } else {
                canvas.drawCircle(p.x, p.y, cellSize * 0.15f * p.life * p.size, paintParticle)
            }
        }

        if (shockwaveAlpha > 0) {
            paintShockwave.alpha = shockwaveAlpha.toInt().coerceIn(0, 255)
            canvas.drawCircle(shockwaveX, shockwaveY, shockwaveRadius, paintShockwave)
        }

        floatingTexts.forEach { t ->
            paintFloatingText.alpha = (t.life * 255).toInt().coerceIn(0, 255)
            canvas.drawText(t.text, t.x, t.y, paintFloatingText)
        }
        canvas.restore()

        if (gameOver) {
            canvas.drawColor(Color.argb(deathFlashAlpha.toInt().coerceIn(0, 255), 180, 0, 0))
            paintText.textSize = 80f
            paintText.color = Color.RED
            paintText.setShadowLayer(20f, 0f, 0f, Color.BLACK)
            canvas.drawText("GAME OVER", width / 2f, height / 2f - 60, paintText)

            paintText.textSize = 40f
            paintText.color = Color.WHITE
            canvas.drawText("最终得分: $score", width / 2f, height / 2f + 10, paintText)

            paintSubText.textSize = 30f
            paintSubText.color = Color.rgb(241, 196, 15)
            canvas.drawText("最高分: $highScore", width / 2f, height / 2f + 60, paintSubText)

            val blink = (System.currentTimeMillis() / 500) % 2 == 0L
            if (blink) {
                paintSubText.textSize = 32f
                paintSubText.color = Color.WHITE
                canvas.drawText("点击屏幕重新开始", width / 2f, height / 2f + 150, paintSubText)
            }
        } else if (dir.x == 0 && dir.y == 0) {
            paintSubText.textSize = 32f
            paintSubText.color = if (isRainbowBoard) Color.WHITE else if (currentBoardBgColor == Color.BLACK) Color.WHITE else Color.DKGRAY
            canvas.drawText("滑动屏幕开始", width / 2f, height / 2f, paintSubText)
            paintSubText.textSize = 20f
            paintSubText.color = if (isRainbowBoard) Color.LTGRAY else if (currentBoardBgColor == Color.BLACK) Color.LTGRAY else Color.GRAY
            canvas.drawText("(滑动控制方向)", width / 2f, height / 2f + 50, paintSubText)
        }
    }

    private var touchStartX = 0f
    private var touchStartY = 0f

    override fun onTouchEvent(event: MotionEvent): Boolean {
        if (aiMode != 0 && event.action == MotionEvent.ACTION_UP) {
            if (gameOver) {
                reset()
                return true
            }
            return true
        }
        when (event.action) {
            MotionEvent.ACTION_DOWN -> {
                touchStartX = event.x
                touchStartY = event.y
                return true
            }
            MotionEvent.ACTION_UP -> {
                if (gameOver) {
                    reset()
                    return true
                }
                val dx = event.x - touchStartX
                val dy = event.y - touchStartY
                if (abs(dx) < 15 && abs(dy) < 15) return true
                val lastDir = if (directionQueue.isNotEmpty()) directionQueue.last() else dir
                if (abs(dx) > abs(dy)) {
                    val newDir = if (dx > 0) Point(1, 0) else Point(-1, 0)
                    if (newDir.x != -lastDir.x || newDir.y != -lastDir.y) {
                        if (directionQueue.size < 2 && (lastDir.x != newDir.x || lastDir.y != newDir.y)) directionQueue.add(newDir)
                    }
                } else {
                    val newDir = if (dy > 0) Point(0, 1) else Point(0, -1)
                    if (newDir.x != -lastDir.x || newDir.y != -lastDir.y) {
                        if (directionQueue.size < 2 && (lastDir.x != newDir.x || lastDir.y != newDir.y)) directionQueue.add(newDir)
                    }
                }
                return true
            }
        }
        return super.onTouchEvent(event)
    }
}
