package com.example.snake

import android.content.Context
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Paint
import android.graphics.Path
import android.graphics.PointF
import android.graphics.CornerPathEffect
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
import kotlin.math.PI
import kotlin.random.Random

class SnakeView(context: Context) : View(context) {

    // 1. 棋盘放大：从 20x20 改为 15x15
    private val cols = 15
    private val rows = 15

    private var cellSize = 0f
    private var offsetX = 0f
    private var offsetY = 0f

    private data class Point(val x: Int, val y: Int)
    private val snake = ArrayDeque<Point>()
    private var dir = Point(0, 0)
    private var nextDir = Point(0, 0)

    private var food = Point(5, 5)
    private var score = 0
    private var highScore = 0
    private var gameOver = false
    private var running = false
    private var gameSpeed = 160L

    var onScoreChanged: ((Int) -> Unit)? = null
    var onMoneyChanged: ((Int) -> Unit)? = null
    
    private val prefs = context.getSharedPreferences("snake_prefs", Context.MODE_PRIVATE)

    private var currentSkinBodyColor = Color.rgb(46, 204, 113)
    private var currentSkinHeadColor = Color.rgb(39, 174, 96)

    private var currentBoardBgColor = Color.rgb(17, 17, 17)
    private var currentBoardGridColor = Color.rgb(30, 30, 30)

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

    private data class Particle(
        var x: Float, var y: Float,
        var vx: Float, var vy: Float,
        var life: Float, val color: Int
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
        pathEffect = CornerPathEffect(20f)
        setShadowLayer(10f, 0f, 0f, currentSkinBodyColor)
    }

    private val paintSnakeHead = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = currentSkinHeadColor
        style = Paint.Style.FILL
    }

    private val paintEyeWhite = Paint(Paint.ANTI_ALIAS_FLAG).apply { color = Color.WHITE }
    private val paintEyeBlack = Paint(Paint.ANTI_ALIAS_FLAG).apply { color = Color.BLACK }

    private val paintFood = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.rgb(231, 76, 60)
        style = Paint.Style.FILL
        setShadowLayer(15f, 0f, 0f, Color.rgb(231, 76, 60))
    }

    private val paintParticle = Paint(Paint.ANTI_ALIAS_FLAG).apply { style = Paint.Style.FILL }
    private val paintFloatingText = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.rgb(241, 196, 15)
        textSize = 40f
        textAlign = Paint.Align.CENTER
        setShadowLayer(8f, 0f, 0f, Color.BLACK)
    }

    private val paintGrid = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = currentBoardGridColor
        strokeWidth = 1f
    }

    private val paintText = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.WHITE
        textAlign = Paint.Align.CENTER
    }

    private val paintSubText = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.LTGRAY
        textAlign = Paint.Align.CENTER
    }

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
        setLayerType(LAYER_TYPE_SOFTWARE, null)
        highScore = prefs.getInt("high_score", 0)
        updateCurrentSkin()
        updateCurrentBoard()
        reset()
    }

    fun updateCurrentSkin() {
        val currentSkinId = prefs.getString("equipped_skin", "green") ?: "green"
        when (currentSkinId) {
            "blue" -> { currentSkinBodyColor = Color.rgb(52, 152, 219); currentSkinHeadColor = Color.rgb(41, 128, 185) }
            "red" -> { currentSkinBodyColor = Color.rgb(231, 76, 60); currentSkinHeadColor = Color.rgb(192, 57, 43) }
            "purple" -> { currentSkinBodyColor = Color.rgb(155, 89, 182); currentSkinHeadColor = Color.rgb(142, 68, 173) }
            "gold" -> { currentSkinBodyColor = Color.rgb(241, 196, 15); currentSkinHeadColor = Color.rgb(243, 156, 18) }
            else -> { currentSkinBodyColor = Color.rgb(46, 204, 113); currentSkinHeadColor = Color.rgb(39, 174, 96) }
        }
        paintSnakeBody.color = currentSkinBodyColor
        paintSnakeBody.setShadowLayer(10f, 0f, 0f, currentSkinBodyColor)
        paintSnakeHead.color = currentSkinHeadColor
        invalidate()
    }

    fun updateCurrentBoard() {
        val currentBoardId = prefs.getString("equipped_board", "dark") ?: "dark"
        when (currentBoardId) {
            "light" -> { currentBoardBgColor = Color.rgb(240, 240, 240); currentBoardGridColor = Color.rgb(220, 220, 220) }
            "neon" -> { currentBoardBgColor = Color.rgb(10, 25, 47); currentBoardGridColor = Color.rgb(23, 58, 94) }
            "forest" -> { currentBoardBgColor = Color.rgb(27, 46, 26); currentBoardGridColor = Color.rgb(46, 74, 45) }
            "cyberpunk" -> { currentBoardBgColor = Color.rgb(43, 15, 59); currentBoardGridColor = Color.rgb(74, 30, 92) }
            else -> { currentBoardBgColor = Color.rgb(17, 17, 17); currentBoardGridColor = Color.rgb(30, 30, 30) }
        }
        paintGrid.color = currentBoardGridColor
        invalidate()
    }

    fun reset() {
        snake.clear()
        snake.add(Point(10, 10))
        dir = Point(0, 0)
        nextDir = Point(0, 0)
        score = 0
        gameOver = false
        gameSpeed = 160L
        lastFrameTime = 0L
        timeAccumulator = 0L

        deathFlashAlpha = 0f
        shakeTime = 0f
        shakeOffsetX = 0f
        shakeOffsetY = 0f

        particles.clear()
        floatingTexts.clear()

        paintSnakeBody.color = currentSkinBodyColor
        paintSnakeBody.setShadowLayer(10f, 0f, 0f, currentSkinBodyColor)
        paintSnakeHead.color = currentSkinHeadColor

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
            p.vy += 0.3f
            p.life -= deltaTime * 0.002f
            if (p.life <= 0) iterator.remove()
        }

        val textIterator = floatingTexts.iterator()
        while (textIterator.hasNext()) {
            val t = textIterator.next()
            t.y -= 2f * (deltaTime / 16f)
            t.life -= deltaTime * 0.001f
            if (t.life <= 0) textIterator.remove()
        }
    }

    private fun update() {
        if (gameOver) return

        if (nextDir.x != 0 || nextDir.y != 0) {
            if (dir.x == 0 && dir.y == 0) dir = nextDir
            else if (dir.x != 0 && nextDir.y != 0) dir = nextDir
            else if (dir.y != 0 && nextDir.x != 0) dir = nextDir
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

        if (snake.any { it == newHead }) {
            gameOver = true
            triggerDeathEffects()
            saveScoreAndMoney()
            return
        }

        snake.addFirst(newHead)

        if (newHead == food) {
            score += 10
            onScoreChanged?.invoke(score)
            triggerEatEffects()
            placeFood()
            gameSpeed = max(70L, gameSpeed - 4L)
        } else {
            snake.removeLast()
        }
    }

    private fun triggerEatEffects() {
        vibrate(35, 100)
        val foodCenterX = offsetX + food.x * cellSize + cellSize / 2
        val foodCenterY = offsetY + food.y * cellSize + cellSize / 2

        val colors = intArrayOf(
            Color.rgb(231, 76, 60), Color.rgb(241, 196, 15),
            Color.rgb(46, 204, 113), Color.rgb(52, 152, 219)
        )
        for (i in 0 until 15) {
            val angle = Random.nextFloat() * 2 * PI
            val speed = Random.nextFloat() * 6f + 2f
            particles.add(
                Particle(
                    x = foodCenterX, y = foodCenterY,
                    vx = cos(angle).toFloat() * speed,
                    vy = sin(angle).toFloat() * speed,
                    life = 1.0f, color = colors[Random.nextInt(colors.size)]
                )
            )
        }
        floatingTexts.add(FloatingText(foodCenterX, foodCenterY, 1.0f, "+10"))
    }

    private fun triggerDeathEffects() {
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

        paintSnakeBody.color = Color.rgb(200, 50, 50)
        paintSnakeBody.setShadowLayer(10f, 0f, 0f, Color.rgb(200, 50, 50))
        paintSnakeHead.color = Color.rgb(150, 0, 0)

        val headX = offsetX + snake.first().x * cellSize + cellSize / 2
        val headY = offsetY + snake.first().y * cellSize + cellSize / 2

        for (i in 0 until 40) {
            val angle = Random.nextFloat() * 2 * PI
            val speed = Random.nextFloat() * 8f + 3f
            particles.add(
                Particle(
                    x = headX, y = headY,
                    vx = cos(angle).toFloat() * speed,
                    vy = sin(angle).toFloat() * speed,
                    life = 1.5f, color = Color.rgb(255, 50, 50)
                )
            )
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
    }

    override fun onDraw(canvas: Canvas) {
        super.onDraw(canvas)

        canvas.drawColor(currentBoardBgColor)

        cellSize = minOf(width / cols.toFloat(), height / rows.toFloat())
        offsetX = (width - cellSize * cols) / 2f
        offsetY = (height - cellSize * rows) / 2f

        canvas.save()
        if (gameOver && shakeTime > 0) {
            canvas.translate(shakeOffsetX, shakeOffsetY)
        }

        for (i in 0..cols) {
            val x = offsetX + i * cellSize
            canvas.drawLine(x, offsetY, x, offsetY + rows * cellSize, paintGrid)
        }
        for (i in 0..rows) {
            val y = offsetY + i * cellSize
            canvas.drawLine(offsetX, y, offsetX + cols * cellSize, y, paintGrid)
        }

        val pulse = 1f + 0.15f * sin(System.currentTimeMillis() / 150.0).toFloat()
        canvas.drawCircle(
            offsetX + food.x * cellSize + cellSize / 2,
            offsetY + food.y * cellSize + cellSize / 2,
            cellSize * 0.35f * pulse,
            paintFood
        )

        // 2. 丝滑插值核心逻辑
        if (snake.isNotEmpty()) {
            // 计算当前时间进度 (0.0 到 1.0)
            val progress = if (gameOver) 0f else (timeAccumulator.toFloat() / gameSpeed).coerceIn(0f, 1f)
            
            val path = Path()
            val points = snake.mapIndexed { index, p ->
                var baseX = offsetX + p.x * cellSize + cellSize / 2
                var baseY = offsetY + p.y * cellSize + cellSize / 2

                // 对蛇头进行平滑插值：让它从上一帧位置平滑滑动到当前位置
                if (index == 0 && !gameOver) {
                    val prevP = if (snake.size > 1) snake[1] else Point(snake[0].x - dir.x, snake[0].y - dir.y)
                    val prevX = offsetX + prevP.x * cellSize + cellSize / 2
                    val prevY = offsetY + prevP.y * cellSize + cellSize / 2
                    baseX = prevX + (baseX - prevX) * progress
                    baseY = prevY + (baseY - prevY) * progress
                }

                // 摆动幅度稍微调小一点点，配合大格子更自然
                val t = System.currentTimeMillis() / 200.0
                val swingAmplitude = if (dir.x != 0) cellSize * 0.08f else cellSize * 0.04f
                val swingX = sin(t + index * 0.5).toFloat() * swingAmplitude
                val swingY = cos(t + index * 0.5).toFloat() * swingAmplitude

                PointF(baseX + swingX, baseY + swingY)
            }

            path.moveTo(points[0].x, points[0].y)
            for (i in 1 until points.size) {
                val prev = points[i - 1]
                val curr = points[i]
                val midX = (prev.x + curr.x) / 2f
                val midY = (prev.y + curr.y) / 2f
                path.quadTo(prev.x, prev.y, midX, midY)
            }
            if (points.size > 1) {
                path.lineTo(points.last().x, points.last().y)
            }

            paintSnakeBody.strokeWidth = cellSize * 0.75f
            canvas.drawPath(path, paintSnakeBody)

            val headPoint = points.first()
            canvas.drawCircle(headPoint.x, headPoint.y, cellSize * 0.5f, paintSnakeHead)

            val currentDir = if (dir.x == 0 && dir.y == 0) Point(1, 0) else dir
            val eyeOffset = cellSize * 0.2f
            val perpOffsetX = -currentDir.y * (cellSize * 0.2f)
            val perpOffsetY = currentDir.x * (cellSize * 0.2f)

            canvas.drawCircle(headPoint.x + currentDir.x * eyeOffset + perpOffsetX, headPoint.y + currentDir.y * eyeOffset + perpOffsetY, cellSize * 0.1f, paintEyeWhite)
            canvas.drawCircle(headPoint.x + currentDir.x * eyeOffset - perpOffsetX, headPoint.y + currentDir.y * eyeOffset - perpOffsetY, cellSize * 0.1f, paintEyeWhite)
            canvas.drawCircle(headPoint.x + currentDir.x * eyeOffset * 1.2f + perpOffsetX, headPoint.y + currentDir.y * eyeOffset * 1.2f + perpOffsetY, cellSize * 0.05f, paintEyeBlack)
            canvas.drawCircle(headPoint.x + currentDir.x * eyeOffset * 1.2f - perpOffsetX, headPoint.y + currentDir.y * eyeOffset * 1.2f - perpOffsetY, cellSize * 0.05f, paintEyeBlack)
        }

        particles.forEach { p ->
            paintParticle.color = p.color
            paintParticle.alpha = (p.life * 255).toInt().coerceIn(0, 255)
            canvas.drawCircle(p.x, p.y, cellSize * 0.15f * p.life, paintParticle)
        }

        floatingTexts.forEach { t ->
            paintFloatingText.alpha = (t.life * 255).toInt().coerceIn(0, 255)
            canvas.drawText(t.text, t.x, t.y, paintFloatingText)
        }

        canvas.restore()

        if (gameOver) {
            canvas.drawColor(Color.argb(deathFlashAlpha.toInt().coerceIn(0, 255), 180, 0, 0))
        }

        if (gameOver) {
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
            paintSubText.color = if (currentBoardBgColor == Color.rgb(240, 240, 240)) Color.DKGRAY else Color.WHITE
            canvas.drawText("滑动屏幕开始", width / 2f, height / 2f, paintSubText)
            paintSubText.textSize = 20f
            paintSubText.color = if (currentBoardBgColor == Color.rgb(240, 240, 240)) Color.GRAY else Color.LTGRAY
            canvas.drawText("(滑动控制方向)", width / 2f, height / 2f + 50, paintSubText)
        }
    }

    private var touchStartX = 0f
    private var touchStartY = 0f

    override fun onTouchEvent(event: MotionEvent): Boolean {
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
                if (abs(dx) < 20 && abs(dy) < 20) return true
                if (abs(dx) > abs(dy)) {
                    nextDir = if (dx > 0) Point(1, 0) else Point(-1, 0)
                } else {
                    nextDir = if (dy > 0) Point(0, 1) else Point(0, -1)
                }
                return true
            }
        }
        return super.onTouchEvent(event)
    }
}
