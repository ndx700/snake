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
import kotlin.math.PI
import kotlin.random.Random

class SnakeView @JvmOverloads constructor(
    context: Context,
    attrs: AttributeSet? = null
) : View(context, attrs) {

    private val cols = 15
    private val rows = 15

    private var cellSize = 0f
    private var offsetX = 0f
    private var offsetY = 0f

    private data class Point(val x: Int, val y: Int)
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

    // 强制策略：-1=自动 0=BFS 1=追尾 2=加权HAM 3=纯HAM 4=MCTS
    private var forcedStrategy = -1
    private var strategyMode = 0

    private val pathIndex = Array(cols) { IntArray(rows) }
    private val pathSequence = mutableListOf<Point>()

    private var bodyColor = Color.rgb(46, 204, 113)
    private var headColor = Color.rgb(39, 174, 96)
    private var bgColor = Color.BLACK
    private var gridColor = Color.rgb(0, 255, 255)
    private var isRainbowSkin = false
    private val rainbow = IntArray(361) { Color.HSVToColor(floatArrayOf(it.toFloat(), 1f, 1f)) }

    private val vibrator: Vibrator? = if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
        val vm = context.getSystemService(Context.VIBRATOR_MANAGER_SERVICE) as? VibratorManager
        vm?.defaultVibrator
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
        var x: Float, var y: Float,
        var vx: Float, var vy: Float,
        var life: Float, val color: Int,
        var size: Float, var decay: Float, var isTrail: Boolean
    )
    private data class FloatText(var x: Float, var y: Float, var life: Float, val text: String)

    private val particles = mutableListOf<Particle>()
    private val floats = mutableListOf<FloatText>()

    private val paintSnakeBody = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = bodyColor
        style = Paint.Style.STROKE
        strokeCap = Paint.Cap.ROUND
        strokeJoin = Paint.Join.ROUND
        pathEffect = CornerPathEffect(30f)
        setShadowLayer(20f, 0f, 0f, bodyColor)
    }
    private val paintSnakeHead = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = headColor
        style = Paint.Style.FILL
        setShadowLayer(15f, 0f, 0f, headColor)
    }
    private val paintHighlight = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.WHITE; style = Paint.Style.FILL; alpha = 100
    }
    private val paintEyeW = Paint(Paint.ANTI_ALIAS_FLAG).apply { color = Color.WHITE }
    private val paintEyeB = Paint(Paint.ANTI_ALIAS_FLAG).apply { color = Color.BLACK }
    private val paintFoodGlow = Paint(Paint.ANTI_ALIAS_FLAG).apply { style = Paint.Style.FILL }
    private val paintFoodCore = Paint(Paint.ANTI_ALIAS_FLAG).apply { color = Color.WHITE; style = Paint.Style.FILL }
    private val paintFoodCross = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.WHITE; style = Paint.Style.STROKE; strokeWidth = 3f
        setShadowLayer(15f, 0f, 0f, Color.CYAN)
    }
    private val paintParticle = Paint(Paint.ANTI_ALIAS_FLAG).apply { style = Paint.Style.FILL }
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
        style = Paint.Style.STROKE; strokeWidth = 3f
        color = Color.argb(60, 255, 255, 255)
    }
    private val paintPanelBg = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.argb(180, 0, 0, 0); style = Paint.Style.FILL
    }
    private val paintPanelBorder = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        style = Paint.Style.STROKE; strokeWidth = 3f
    }
    private val paintModeName = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        textSize = 30f; textAlign = Paint.Align.CENTER; isFakeBoldText = true
    }
    private val paintModeDesc = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.WHITE; textSize = 20f; textAlign = Paint.Align.CENTER
    }
    private val paintModeInfo = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.rgb(180, 180, 180); textSize = 18f; textAlign = Paint.Align.LEFT
    }
    private val paintBoardBg = Paint(Paint.ANTI_ALIAS_FLAG).apply { style = Paint.Style.FILL }
    private val boardMatrix = Matrix()

    private var lastFrameTime = 0L
    private var timeAccumulator = 0L

    private val frameCallback = object : Choreographer.FrameCallback {
        override fun doFrame(frameTimeNanos: Long) {
            if (!running) return
            val currentTime = System.nanoTime()
            if (lastFrameTime == 0L) lastFrameTime = currentTime
            val dt = (currentTime - lastFrameTime) / 1_000_000f
            lastFrameTime = currentTime
            timeAccumulator += dt.toLong()
            if (timeAccumulator >= gameSpeed) {
                update()
                timeAccumulator -= gameSpeed
            }
            updateEffects(dt)
            invalidate()
            Choreographer.getInstance().postFrameCallback(this)
        }
    }

    init {
        initHamPath()
        highScore = prefs.getInt("high_score", 0)
        updateCurrentSkin()
        updateCurrentBoard()
        reset()
    }

    private fun initHamPath() {
        pathSequence.clear()
        for (c in 0 until cols) {
            if (c % 2 == 0) {
                for (r in 0 until rows) { pathIndex[c][r] = pathSequence.size; pathSequence.add(Point(c, r)) }
            } else {
                for (r in rows - 1 downTo 0) { pathIndex[c][r] = pathSequence.size; pathSequence.add(Point(c, r)) }
            }
        }
    }

    fun getAIMode(): Int = aiMode
    fun setAIMode(mode: Int) { aiMode = mode; reset() }
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
                isRainbowSkin = true
                bodyColor = Color.WHITE; headColor = Color.WHITE
                paintSnakeBody.setShadowLayer(35f, 0f, 0f, Color.WHITE)
            }
            else -> { bodyColor = Color.rgb(46, 204, 113); headColor = Color.rgb(39, 174, 96) }
        }
        if (!isRainbowSkin) {
            paintSnakeBody.shader = null
            paintSnakeBody.color = bodyColor
            paintSnakeBody.setShadowLayer(20f, 0f, 0f, bodyColor)
            paintSnakeHead.color = headColor
            paintSnakeHead.setShadowLayer(15f, 0f, 0f, headColor)
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
        if (aiMode == 2) {
            snake.add(Point(0, 0)); dir = Point(0, 1)
        } else {
            snake.add(Point(10, 10)); dir = Point(0, 0)
        }
        directionQueue.clear()
        score = 0; comboCount = 0; hungerCounter = 0
        foodUnreachableStreak = 0
        gameOver = false
        gameSpeed = 180L
        lastFrameTime = 0L; timeAccumulator = 0L
        deathFlashAlpha = 0f; shakeTime = 0f
        shakeOffsetX = 0f; shakeOffsetY = 0f
        shockwaveRadius = 0f; shockwaveAlpha = 0f
        strategyMode = 0
        particles.clear(); floats.clear()

        if (isRainbowSkin) {
            paintSnakeBody.setShadowLayer(35f, 0f, 0f, Color.WHITE)
        } else {
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
        var attempts = 0
        while (attempts < 1000) {
            val p = Point(Random.nextInt(cols), Random.nextInt(rows))
            if (snake.none { it == p }) { food = p; return }
            attempts++
        }
    }

    private fun vibrate(ms: Long) {
        vibrator?.let {
            if (!it.hasVibrator()) return
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
                it.vibrate(VibrationEffect.createOneShot(ms, VibrationEffect.DEFAULT_AMPLITUDE))
            } else {
                @Suppress("DEPRECATION")
                it.vibrate(ms)
            }
        }
    }

    private fun updateEffects(deltaTime: Float) {
        if (gameOver) {
            deathFlashAlpha = 120f + 60f * sin(System.currentTimeMillis() / 150.0).toFloat()
            if (shockwaveAlpha > 0) { shockwaveRadius += deltaTime * 1.5f; shockwaveAlpha -= deltaTime * 0.15f }
        } else if (deathFlashAlpha > 0) deathFlashAlpha = max(0f, deathFlashAlpha - deltaTime * 0.5f)

        if (shakeTime > 0) {
            shakeTime -= deltaTime
            shakeOffsetX = (Random.nextFloat() - 0.5f) * 30f * (shakeTime / 400f)
            shakeOffsetY = (Random.nextFloat() - 0.5f) * 30f * (shakeTime / 400f)
        } else { shakeOffsetX = 0f; shakeOffsetY = 0f }

        val it = particles.iterator()
        while (it.hasNext()) {
            val p = it.next()
            p.x += p.vx * (deltaTime / 16f); p.y += p.vy * (deltaTime / 16f)
            if (!p.isTrail) p.vy += 0.4f
            p.life -= deltaTime * p.decay
            if (p.life <= 0) it.remove()
        }
        val ti = floats.iterator()
        while (ti.hasNext()) {
            val t = ti.next()
            t.y -= 2.5f * (deltaTime / 16f); t.life -= deltaTime * 0.001f
            if (t.life <= 0) ti.remove()
        }
    }

    private fun autoPilotBFS() {
        if (gameOver) return
        val head = snake.first()

        val allDirs = listOf(Point(0, -1), Point(0, 1), Point(-1, 0), Point(1, 0))
        val validDirs = allDirs.filter { d ->
            val isRev = (d.x == -dir.x && d.y == -dir.y)
            val nh = Point(head.x + d.x, head.y + d.y)
            val isWall = nh.x !in 0 until cols || nh.y !in 0 until rows
            val isSelf = snake.dropLast(1).any { it == nh }
            !isRev && !isWall && !isSelf
        }
        if (validDirs.isEmpty()) return

        val testFoodPath = bfsPath(head, food, snake, dir)
        if (testFoodPath != null) foodUnreachableStreak = 0 else foodUnreachableStreak++

        val snakeLen = snake.size
        val freeSpace = cols * rows - snakeLen

        strategyMode = if (forcedStrategy >= 0) {
            forcedStrategy
        } else {
            when {
                score >= 150000 || freeSpace < snakeLen / 3 -> 3
                score >= 80000 || (snakeLen > 100 && freeSpace < snakeLen) -> 2
                snakeLen > 70 && foodUnreachableStreak > 10 -> 1
                snakeLen in 15..40 && gameSpeed > 120 && score < 30000 -> 4
                else -> 0
            }
        }

        val chosenDir: Point? = when (strategyMode) {
            1 -> tailChaseStrategy(head, validDirs)
            2 -> weightedHamStrategy(head, validDirs)
            3 -> pureHamStrategy(head, validDirs)
            4 -> mctsStrategy(head, validDirs)
            else -> bfsBeamStrategy(head, validDirs)
        }

        if (chosenDir != null) {
            directionQueue.clear()
            directionQueue.add(chosenDir)
        }
    }

    private fun bfsBeamStrategy(head: Point, validDirs: List<Point>): Point? {
        if (hungerCounter > 15) {
            val p = bfsPath(head, food, snake, dir)
            if (p != null && p.size > 1) {
                val nm = Point(p[1].x - p[0].x, p[1].y - p[0].y)
                if (validDirs.contains(nm)) return nm
            }
        }
        val fdx = food.x - head.x
        val fdy = food.y - head.y
        if (abs(fdx) + abs(fdy) == 1) {
            val fd = Point(fdx, fdy)
            if (validDirs.contains(fd) && isEatingSafe(head, food)) return fd
        }
        if (hungerCounter > 8) {
            val p = bfsPath(head, food, snake, dir)
            if (p != null && p.size > 1) {
                val nm = Point(p[1].x - p[0].x, p[1].y - p[0].y)
                if (validDirs.contains(nm) && isEatingSafe(head, food)) return nm
            }
        }

        var bestDir: Point? = null
        var bestScore = Int.MIN_VALUE

        for (d in validDirs) {
            var totalScore = 0
            var beam = mutableListOf<Pair<Point, ArrayDeque<Point>>>()
            val nh = Point(head.x + d.x, head.y + d.y)
            val simSnake = ArrayDeque(snake)
            simSnake.addFirst(nh)
            val willEat = nh == food
            if (!willEat) simSnake.removeLast()
            beam.add(Pair(d, simSnake))

            for (step in 1..3) {
                val nextBeam = mutableListOf<Pair<Point, ArrayDeque<Point>>>()
                for ((_, bs) in beam) {
                    val bh = bs.first()
                    for (cd in listOf(Point(0, -1), Point(0, 1), Point(-1, 0), Point(1, 0))) {
                        val bnh = Point(bh.x + cd.x, bh.y + cd.y)
                        if (bnh.x !in 0 until cols || bnh.y !in 0 until rows) continue
                        val be = bnh == food
                        val bcc = if (be) bs else bs.dropLast(1)
                        if (bcc.any { it == bnh }) continue
                        val nbs = ArrayDeque(bs)
                        nbs.addFirst(bnh)
                        if (!be) nbs.removeLast()
                        nextBeam.add(Pair(cd, nbs))
                    }
                }
                val pruned = nextBeam.sortedByDescending { floodFill(it.second.first(), it.second) }.take(3)
                beam = pruned.toMutableList()
                if (beam.isEmpty()) break
            }

            for ((_, fs) in beam) {
                val space = floodFill(fs.first(), fs)
                val reachFood = bfsPath(fs.first(), food, fs, Point(0, 0))
                totalScore += space * 10
                if (reachFood != null) totalScore += 500
                totalScore -= (reachFood?.size ?: 999) * 5
            }
            if (totalScore > bestScore) { bestScore = totalScore; bestDir = d }
        }
        return bestDir
    }

    private fun tailChaseStrategy(head: Point, validDirs: List<Point>): Point? {
        var best: Point? = null
        var bestSpace = -1
        for (d in validDirs) {
            val nh = Point(head.x + d.x, head.y + d.y)
            val sim = ArrayDeque(snake); sim.addFirst(nh); sim.removeLast()
            val canReach = bfsPath(nh, sim.last(), sim, Point(0, 0)) != null
            if (!canReach) continue
            val space = floodFill(nh, sim)
            if (space > bestSpace) { bestSpace = space; best = d }
        }
        if (best != null) return best
        return validDirs.maxByOrNull {
            val nh = Point(head.x + it.x, head.y + it.y)
            val sim = ArrayDeque(snake); sim.addFirst(nh); sim.removeLast()
            floodFill(nh, sim)
        }
    }

    private fun weightedHamStrategy(head: Point, validDirs: List<Point>): Point? {
        val pathPos = pathIndex[head.x][head.y]
        val pathNext = pathSequence[(pathPos + 1) % pathSequence.size]
        val pathDx = pathNext.x - head.x
        val pathDy = pathNext.y - head.y
        val pathDir = Point(pathDx, pathDy)

        val foodDist = abs(head.x - food.x) + abs(head.y - food.y)
        if (foodDist <= 3) {
            val p = bfsPath(head, food, snake, dir)
            if (p != null && p.size > 1) {
                val nm = Point(p[1].x - p[0].x, p[1].y - p[0].y)
                if (validDirs.contains(nm) && isEatingSafe(head, food)) return nm
            }
        }

        if (validDirs.contains(pathDir)) return pathDir
        return validDirs.maxByOrNull {
            val nh = Point(head.x + it.x, head.y + it.y)
            val sim = ArrayDeque(snake); sim.addFirst(nh); sim.removeLast()
            floodFill(nh, sim)
        }
    }

    private fun pureHamStrategy(head: Point, validDirs: List<Point>): Point? {
        val pathPos = pathIndex[head.x][head.y]
        val pathNext = pathSequence[(pathPos + 1) % pathSequence.size]
        val pathDx = pathNext.x - head.x
        val pathDy = pathNext.y - head.y
        val pathDir = Point(pathDx, pathDy)
        if (validDirs.contains(pathDir)) return pathDir
        return validDirs.maxByOrNull {
            val nh = Point(head.x + it.x, head.y + it.y)
            val sim = ArrayDeque(snake); sim.addFirst(nh); sim.removeLast()
            floodFill(nh, sim)
        }
    }

    private fun mctsStrategy(head: Point, validDirs: List<Point>): Point? {
        if (hungerCounter > 15) {
            val p = bfsPath(head, food, snake, dir)
            if (p != null && p.size > 1) {
                val nm = Point(p[1].x - p[0].x, p[1].y - p[0].y)
                if (validDirs.contains(nm)) return nm
            }
        }

        val rolloutCount = 6
        val maxRolloutSteps = 30

        var bestDir: Point? = null
        var bestAvgScore = -1e9

        for (d in validDirs) {
            var total = 0.0
            for (r in 0 until rolloutCount) {
                total += simulateRollout(d, maxRolloutSteps)
            }
            val avg = total / rolloutCount
            if (avg > bestAvgScore) {
                bestAvgScore = avg
                bestDir = d
            }
        }
        return bestDir
    }

    private fun simulateRollout(firstDir: Point, maxSteps: Int): Double {
        val sim = ArrayDeque(snake)
        val nh = Point(snake.first().x + firstDir.x, snake.first().y + firstDir.y)
        if (nh.x !in 0 until cols || nh.y !in 0 until rows) return -1000.0
        if (sim.any { it == nh }) return -1000.0
        sim.addFirst(nh)
        val ateFirst = nh == food
        if (!ateFirst) sim.removeLast()

        var simFood = if (ateFirst) Point(Random.nextInt(cols), Random.nextInt(rows)) else food
        var simDir = firstDir
        var scoreGain = 0.0

        for (step in 0 until maxSteps) {
            val sh = sim.first()
            val dirs = listOf(Point(0, -1), Point(0, 1), Point(-1, 0), Point(1, 0))
            val valid = dirs.filter { sd ->
                val isRev = (sd.x == -simDir.x && sd.y == -simDir.y)
                val snh = Point(sh.x + sd.x, sh.y + sd.y)
                val isW = snh.x !in 0 until cols || snh.y !in 0 until rows
                val isS = sim.dropLast(1).any { it == snh }
                !isRev && !isW && !isS
            }
            if (valid.isEmpty()) { scoreGain -= 500.0; break }

            val next = valid.minByOrNull { sd ->
                val snh = Point(sh.x + sd.x, sh.y + sd.y)
                abs(snh.x - simFood.x) + abs(snh.y - simFood.y)
            } ?: valid.first()

            val snh = Point(sh.x + next.x, sh.y + next.y)
            val ate = snh == simFood
            sim.addFirst(snh)
            if (ate) {
                scoreGain += 10.0
                var att = 0
                while (att < 500) {
                    val np = Point(Random.nextInt(cols), Random.nextInt(rows))
                    if (sim.none { it == np }) { simFood = np; break }
                    att++
                }
            } else {
                sim.removeLast()
            }
            simDir = next

            val space = floodFill(sim.first(), sim)
            scoreGain += space * 0.1
            if (space < sim.size) scoreGain -= 200.0
        }
        return scoreGain
    }

    private fun isEatingSafe(head: Point, foodPos: Point): Boolean {
        val simSnake = ArrayDeque(snake)
        simSnake.addFirst(foodPos)
        val newHead = simSnake.first()
        val newTail = simSnake.last()
        val spaceAfterEating = floodFill(newHead, simSnake)
        if (spaceAfterEating > simSnake.size * 1.2f) return true
        if (spaceAfterEating < simSnake.size * 0.7f) return false
        return bfsPath(newHead, newTail, simSnake, Point(0, 0)) != null
    }

    private fun autoPilotHamiltonian() {
        if (gameOver) return
        val head = snake.first()
        if (head.x !in 0 until cols || head.y !in 0 until rows) return
        val currentIndex = pathIndex[head.x][head.y]
        val nextIndex = (currentIndex + 1) % pathSequence.size
        val nextPoint = pathSequence[nextIndex]
        val dx = nextPoint.x - head.x
        val dy = nextPoint.y - head.y
        val nh = Point(head.x + dx, head.y + dy)
        val isSelfCollision = snake.dropLast(1).any { it == nh }
        if (isSelfCollision) {
            val nni = (nextIndex + 1) % pathSequence.size
            val nnp = pathSequence[nni]
            val dx2 = nnp.x - head.x
            val dy2 = nnp.y - head.y
            if (abs(dx2) + abs(dy2) == 1) { dir = Point(dx2, dy2); return }
            return
        }
        dir = Point(dx, dy)
    }

    private fun floodFill(start: Point, currentSnake: Collection<Point>): Int {
        val queue = ArrayDeque<Point>()
        val visited = mutableSetOf<Point>()
        queue.add(start); visited.add(start)
        while (queue.isNotEmpty()) {
            val curr = queue.removeFirst()
            for (d in listOf(Point(0, -1), Point(0, 1), Point(-1, 0), Point(1, 0))) {
                val next = Point(curr.x + d.x, curr.y + d.y)
                if (next.x !in 0 until cols || next.y !in 0 until rows) continue
                if (currentSnake.any { it == next }) continue
                if (visited.contains(next)) continue
                visited.add(next); queue.add(next)
            }
        }
        return visited.size
    }

    private fun bfsPath(start: Point, target: Point, customSnake: Collection<Point>, reverseDir: Point): List<Point>? {
        val queue = ArrayDeque<Point>()
        val visited = mutableSetOf<Point>()
        val parent = mutableMapOf<Point, Point>()
        queue.add(start); visited.add(start)
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
                visited.add(next); parent[next] = curr; queue.add(next)
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
            2 -> autoPilotHamiltonian()
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
            gameOver = true; onDeath(); return
        }

        val isEating = newHead == food
        val tail = snake.last()
        val collidedWithSelf = if (newHead == tail) isEating else snake.any { it == newHead }
        if (collidedWithSelf) {
            gameOver = true; onDeath(); return
        }

        val tailX = offsetX + tail.x * cellSize + cellSize / 2
        val tailY = offsetY + tail.y * cellSize + cellSize / 2
        val trailColor = if (isRainbowSkin) Color.HSVToColor(floatArrayOf((System.currentTimeMillis() / 10f) % 360f, 1f, 1f)) else bodyColor
        particles.add(Particle(
            x = tailX + (Random.nextFloat() - 0.5f) * cellSize * 0.5f,
            y = tailY + (Random.nextFloat() - 0.5f) * cellSize * 0.5f,
            vx = (Random.nextFloat() - 0.5f) * 1.5f,
            vy = (Random.nextFloat() - 0.5f) * 1.5f,
            life = 1.0f, color = trailColor,
            size = Random.nextFloat() * 0.8f + 0.5f,
            decay = 0.003f, isTrail = true
        ))

        snake.addFirst(newHead)
        if (isEating) {
            hungerCounter = 0
            comboCount++
            val basePoints = 10 + (comboCount - 1) * 5
            val mult = when {
                score >= 1000 -> 3.0f
                score >= 500 -> 2.0f
                score >= 200 -> 1.5f
                else -> 1.0f
            }
            val earned = (basePoints * mult).toInt()
            score += earned
            onScoreChanged?.invoke(score)
            eatEffect(earned)
            placeFood()
            gameSpeed = max(70L, gameSpeed - 3L)
        } else {
            hungerCounter++
            snake.removeLast()
        }
    }

    private fun eatEffect(scoreGained: Int) {
        vibrate(35)
        val cx = offsetX + food.x * cellSize + cellSize / 2
        val cy = offsetY + food.y * cellSize + cellSize / 2
        val colors = intArrayOf(
            Color.rgb(231, 76, 60), Color.rgb(241, 196, 15),
            Color.rgb(46, 204, 113), Color.rgb(52, 152, 219),
            Color.WHITE, Color.CYAN
        )
        for (i in 0 until 25) {
            val angle = Random.nextFloat() * 2 * PI
            val speed = Random.nextFloat() * 8f + 2f
            particles.add(Particle(
                x = cx, y = cy,
                vx = cos(angle).toFloat() * speed,
                vy = sin(angle).toFloat() * speed,
                life = 1.0f, color = colors[Random.nextInt(colors.size)],
                size = Random.nextFloat() * 1.5f + 0.5f, decay = 0.0015f
            ))
        }
        floats.add(FloatText(cx, cy, 1.0f, "+$scoreGained"))
    }

    private fun onDeath() {
        vibrate(300)
        shakeTime = 400f
        deathFlashAlpha = 255f
        val hx = offsetX + snake.first().x * cellSize + cellSize / 2
        val hy = offsetY + snake.first().y * cellSize + cellSize / 2
        shockwaveX = hx; shockwaveY = hy; shockwaveRadius = cellSize; shockwaveAlpha = 255f
        paintSnakeBody.color = Color.rgb(200, 50, 50)
        paintSnakeBody.setShadowLayer(20f, 0f, 0f, Color.rgb(200, 50, 50))
        paintSnakeHead.color = Color.rgb(150, 0, 0)
        paintSnakeHead.setShadowLayer(15f, 0f, 0f, Color.rgb(150, 0, 0))
        for (i in 0 until 60) {
            val angle = Random.nextFloat() * 2 * PI
            val speed = Random.nextFloat() * 12f + 3f
            particles.add(Particle(
                x = hx, y = hy,
                vx = cos(angle).toFloat() * speed,
                vy = sin(angle).toFloat() * speed,
                life = 1.5f, color = Color.rgb(255, 50, 50),
                size = Random.nextFloat() * 2f + 1f, decay = 0.002f
            ))
        }
        if (score > highScore) { highScore = score; prefs.edit().putInt("high_score", highScore).apply() }
        val cm = prefs.getInt("money", 0) + score
        prefs.edit().putInt("money", cm).apply()
        onMoneyChanged?.invoke(cm)
        aiMode = 0
    }

    override fun onDraw(canvas: Canvas) {
        super.onDraw(canvas)
        cellSize = minOf(width / cols.toFloat(), height / rows.toFloat())
        offsetX = (width - cellSize * cols) / 2f
        offsetY = (height - cellSize * rows) / 2f

        if (paintBoardBg.shader != null) {
            val time = System.currentTimeMillis() % 5000L
            boardMatrix.setTranslate(time * 0.15f, time * 0.15f)
            paintBoardBg.shader?.setLocalMatrix(boardMatrix)
            canvas.drawRect(offsetX, offsetY, offsetX + cols * cellSize, offsetY + rows * cellSize, paintBoardBg)
        } else {
            canvas.drawColor(bgColor)
        }

        canvas.save()
        if (gameOver && shakeTime > 0) canvas.translate(shakeOffsetX, shakeOffsetY)

        val breath = (sin(System.currentTimeMillis() / 400.0).toFloat() + 1f) / 2f
        val gridAlpha = (60 + 195 * breath).toInt()
        paintGrid.alpha = gridAlpha
        paintGrid.color = gridColor
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
                val p1 = pathSequence[i]; val p2 = pathSequence[i + 1]
                canvas.drawLine(
                    offsetX + p1.x * cellSize + cellSize / 2, offsetY + p1.y * cellSize + cellSize / 2,
                    offsetX + p2.x * cellSize + cellSize / 2, offsetY + p2.y * cellSize + cellSize / 2,
                    paintHamPath
                )
            }
        }

        val fx = offsetX + food.x * cellSize + cellSize / 2
        val fy = offsetY + food.y * cellSize + cellSize / 2
        val pulse = 1f + 0.25f * sin(System.currentTimeMillis() / 150.0).toFloat()
        val fr = cellSize * 0.4f * pulse
        paintFoodGlow.shader = RadialGradient(fx, fy, fr * 2.2f,
            intArrayOf(
                Color.argb(200, 0, 255, 255),
                Color.argb(100, 0, 200, 255),
                Color.argb(0, 0, 0, 0)
            ), floatArrayOf(0.0f, 0.5f, 1.0f), Shader.TileMode.CLAMP)
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
            val path = Path()
            val points = snake.mapIndexed { index, p ->
                var bx = offsetX + p.x * cellSize + cellSize / 2
                var by = offsetY + p.y * cellSize + cellSize / 2
                if (index == 0 && !gameOver) {
                    val prevP = if (snake.size > 1) snake[1] else Point(snake[0].x - dir.x, snake[0].y - dir.y)
                    val prevX = offsetX + prevP.x * cellSize + cellSize / 2
                    val prevY = offsetY + prevP.y * cellSize + cellSize / 2
                    bx = prevX + (bx - prevX) * progress
                    by = prevY + (by - prevY) * progress
                }
                val t = System.currentTimeMillis() / 200.0
                val amp = if (dir.x != 0) cellSize * 0.1f else cellSize * 0.05f
                PointF(bx + sin(t + index * 0.5).toFloat() * amp, by + cos(t + index * 0.5).toFloat() * amp)
            }
            path.moveTo(points[0].x, points[0].y)
            for (i in 1 until points.size) {
                val prev = points[i - 1]; val curr = points[i]
                path.quadTo(prev.x, prev.y, (prev.x + curr.x) / 2f, (prev.y + curr.y) / 2f)
            }
            if (points.size > 1) path.lineTo(points.last().x, points.last().y)

            if (isRainbowSkin) {
                val hp = points.first(); val tp = points.last()
                val angle = atan2(tp.y - hp.y, tp.x - hp.x)
                val to = (System.currentTimeMillis() % 3000) / 3000f
                val fd = cellSize * 6 * to
                paintSnakeBody.shader = LinearGradient(
                    hp.x - cos(angle) * fd, hp.y - sin(angle) * fd,
                    tp.x - cos(angle) * fd, tp.y - sin(angle) * fd,
                    rainbow, null, Shader.TileMode.MIRROR
                )
                paintSnakeHead.color = Color.WHITE
                paintSnakeBody.alpha = 255
                paintSnakeBody.setShadowLayer(35f, 0f, 0f, Color.WHITE)
            } else {
                paintSnakeBody.shader = null
                paintSnakeBody.color = bodyColor
                paintSnakeBody.alpha = 255
                paintSnakeBody.setShadowLayer(20f, 0f, 0f, bodyColor)
            }
            paintSnakeBody.strokeWidth = cellSize * 0.8f
            paintSnakeBody.alpha = if (isRainbowSkin) 150 else 120
            canvas.drawPath(path, paintSnakeBody)
            paintSnakeBody.strokeWidth = cellSize * 0.65f
            paintSnakeBody.alpha = 255
            canvas.drawPath(path, paintSnakeBody)

            val hp = points.first()
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
            canvas.drawText("GAME OVER", width / 2f, height / 2f - 60, paintText)
            paintText.textSize = 40f; paintText.color = Color.WHITE
            canvas.drawText("最终得分: $score", width / 2f, height / 2f + 10, paintText)
            paintSubText.textSize = 30f; paintSubText.color = Color.rgb(241, 196, 15)
            canvas.drawText("最高分: $highScore", width / 2f, height / 2f + 60, paintSubText)
            if ((System.currentTimeMillis() / 500) % 2 == 0L) {
                paintSubText.textSize = 32f; paintSubText.color = Color.WHITE
                canvas.drawText("点击屏幕重新开始", width / 2f, height / 2f + 150, paintSubText)
            }
        } else if (dir.x == 0 && dir.y == 0) {
            paintSubText.textSize = 32f
            paintSubText.color = Color.WHITE
            canvas.drawText("滑动屏幕开始", width / 2f, height / 2f, paintSubText)
            paintSubText.textSize = 20f
            paintSubText.color = Color.LTGRAY
            canvas.drawText("(滑动控制方向)", width / 2f, height / 2f + 50, paintSubText)
        } else if (aiMode == 1) {
            val modeName: String
            val modeDesc: String
            val modeColor: Int
            when (strategyMode) {
                1 -> {
                    modeName = "🔄 追尾保命"
                    modeDesc = "长蛇优先追尾，等待食物刷到嘴边"
                    modeColor = Color.rgb(241, 196, 15)
                }
                2 -> {
                    modeName = "🛤 加权汉密尔顿"
                    modeDesc = "沿路径走，允许3格内抄近道吃食物"
                    modeColor = Color.rgb(52, 152, 219)
                }
                3 -> {
                    modeName = "🛡 纯汉密尔顿"
                    modeDesc = "严格沿固定路径，理论上永不死亡"
                    modeColor = Color.rgb(46, 204, 113)
                }
                4 -> {
                    modeName = "🧠 MCTS 深推"
                    modeDesc = "每方向6次rollout，深度30步"
                    modeColor = Color.rgb(155, 89, 182)
                }
                else -> {
                    modeName = "🎯 BFS + Beam"
                    modeDesc = "3步前瞻，每条分支保留空间最大方向"
                    modeColor = Color.rgb(231, 76, 60)
                }
            }

            val panelX = width / 2f
            val panelY = height - 90f
            val panelW = 620f
            val panelH = 90f

            canvas.drawRoundRect(
                panelX - panelW / 2, panelY - panelH / 2,
                panelX + panelW / 2, panelY + panelH / 2,
                15f, 15f, paintPanelBg
            )
            paintPanelBorder.color = modeColor
            canvas.drawRoundRect(
                panelX - panelW / 2, panelY - panelH / 2,
                panelX + panelW / 2, panelY + panelH / 2,
                15f, 15f, paintPanelBorder
            )

            paintModeName.color = modeColor
            canvas.drawText(modeName, panelX, panelY - 10f, paintModeName)
            canvas.drawText(modeDesc, panelX, panelY + 25f, paintModeDesc)

            val snakeLen = snake.size
            val freeSpace = cols * rows - snakeLen
            val forceTag = if (forcedStrategy >= 0) " [强制]" else ""
            val infoText = "LEN:$snakeLen  SPACE:$freeSpace  HUNGER:$hungerCounter  STRK:$foodUnreachableStreak$forceTag"
            canvas.drawText(infoText, panelX - panelW / 2 + 15f, panelY + 42f, paintModeInfo)
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
            MotionEvent.ACTION_DOWN -> {
                touchStartX = event.x; touchStartY = event.y; return true
            }
            MotionEvent.ACTION_UP -> {
                if (gameOver) { reset(); return true }
                val dx = event.x - touchStartX; val dy = event.y - touchStartY
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
