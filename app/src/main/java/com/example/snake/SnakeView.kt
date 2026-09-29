package com.example.snake

import android.content.Context
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Paint
import android.graphics.RectF
import android.os.Handler
import android.os.Looper
import android.view.Choreographer
import android.view.MotionEvent
import android.view.View
import kotlin.math.abs
import kotlin.math.max
import kotlin.math.sin
import kotlin.random.Random

class SnakeView(context: Context) : View(context) {

    private val cols = 20
    private val rows = 20

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

    // 逻辑移动速度（毫秒），初始 160ms，最低 70ms（越快越难）
    private var gameSpeed = 160L

    var onScoreChanged: ((Int) -> Unit)? = null

    private val prefs = context.getSharedPreferences("snake_prefs", Context.MODE_PRIVATE)

    private val paintSnake = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.rgb(46, 204, 113)
    }

    private val paintHead = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.rgb(39, 174, 96)
    }

    private val paintFood = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.rgb(231, 76, 60)
        setShadowLayer(15f, 0f, 0f, Color.rgb(231, 76, 60))
    }

    private val paintGrid = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.rgb(30, 30, 30)
        strokeWidth = 1f
    }

    private val paintText = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.WHITE
        textSize = 48f
        textAlign = Paint.Align.CENTER
    }

    private val paintSubText = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.LTGRAY
        textSize = 28f
        textAlign = Paint.Align.CENTER
    }

    // --- 高帧率渲染核心逻辑 ---
    private var lastFrameTime = 0L
    private var timeAccumulator = 0L

    private val frameCallback = object : Choreographer.FrameCallback {
        override fun doFrame(frameTimeNanos: Long) {
            if (!running) return

            val currentTime = System.nanoTime()
            if (lastFrameTime == 0L) lastFrameTime = currentTime

            val deltaTime = (currentTime - lastFrameTime) / 1_000_000 // 转毫秒
            lastFrameTime = currentTime
            timeAccumulator += deltaTime

            // 只有当累计时间达到游戏速度时，才更新一次逻辑（蛇移动）
            if (timeAccumulator >= gameSpeed) {
                update()
                timeAccumulator -= gameSpeed
            }

            // 每一帧都强制重绘画面（约 60/90/120 帧每秒）
            invalidate()

            // 注册下一帧
            Choreographer.getInstance().postFrameCallback(this)
        }
    }

    init {
        highScore = prefs.getInt("high_score", 0)
        reset()
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

    private fun update() {
        if (gameOver) return

        if (nextDir.x != 0 || nextDir.y != 0) {
            if (dir.x == 0 && dir.y == 0) {
                dir = nextDir
            } else if (dir.x != 0 && nextDir.y != 0) {
                dir = nextDir
            } else if (dir.y != 0 && nextDir.x != 0) {
                dir = nextDir
            }
        }

        if (dir.x == 0 && dir.y == 0) return

        val head = snake.first()
        val newHead = Point(head.x + dir.x, head.y + dir.y)

        if (newHead.x < 0 || newHead.x >= cols || newHead.y < 0 || newHead.y >= rows) {
            gameOver = true
            saveHighScore()
            return
        }

        if (snake.any { it == newHead }) {
            gameOver = true
            saveHighScore()
            return
        }

        snake.addFirst(newHead)

        if (newHead == food) {
            score += 10
            onScoreChanged?.invoke(score)
            placeFood()
            // 动态加速
            gameSpeed = max(70L, gameSpeed - 4L)
        } else {
            snake.removeLast()
        }
    }

    private fun saveHighScore() {
        if (score > highScore) {
            highScore = score
            prefs.edit().putInt("high_score", highScore).apply()
        }
    }

    override fun onDraw(canvas: Canvas) {
        super.onDraw(canvas)

        canvas.drawColor(Color.rgb(17, 17, 17))

        cellSize = minOf(width / cols.toFloat(), height / rows.toFloat())
        offsetX = (width - cellSize * cols) / 2f
        offsetY = (height - cellSize * rows) / 2f

        for (i in 0..cols) {
            val x = offsetX + i * cellSize
            canvas.drawLine(x, offsetY, x, offsetY + rows * cellSize, paintGrid)
        }
        for (i in 0..rows) {
            val y = offsetY + i * cellSize
            canvas.drawLine(offsetX, y, offsetX + cols * cellSize, y, paintGrid)
        }

        // 食物发光呼吸动画（由高帧率驱动，现在会非常丝滑）
        val pulse = 1f + 0.15f * sin(System.currentTimeMillis() / 150.0).toFloat()
        canvas.drawCircle(
            offsetX + food.x * cellSize + cellSize / 2,
            offsetY + food.y * cellSize + cellSize / 2,
            cellSize * 0.35f * pulse,
            paintFood
        )

        val rectF = RectF()
        snake.forEachIndexed { index, p ->
            val left = offsetX + p.x * cellSize + 2
            val top = offsetY + p.y * cellSize + 2
            val right = left + cellSize - 4
            val bottom = top + cellSize - 4

            rectF.set(left, top, right, bottom)
            canvas.drawRoundRect(rectF, 8f, 8f, if (index == 0) paintHead else paintSnake)
        }

        if (gameOver) {
            canvas.drawColor(0xBB000000.toInt())
            paintText.textSize = 52f
            paintText.color = Color.rgb(231, 76, 60)
            canvas.drawText("游戏结束", width / 2f, height / 2f - 60, paintText)

            paintText.textSize = 32f
            paintText.color = Color.WHITE
            canvas.drawText("本局得分: $score", width / 2f, height / 2f + 10, paintText)

            paintSubText.color = Color.rgb(241, 196, 15)
            canvas.drawText("最高分: $highScore", width / 2f, height / 2f + 60, paintSubText)

            paintSubText.color = Color.LTGRAY
            canvas.drawText("点击屏幕重新开始", width / 2f, height / 2f + 130, paintSubText)
        } else if (dir.x == 0 && dir.y == 0) {
            paintSubText.textSize = 32f
            paintSubText.color = Color.WHITE
            canvas.drawText("滑动屏幕开始", width / 2f, height / 2f, paintSubText)
            paintSubText.textSize = 20f
            paintSubText.color = Color.GRAY
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
