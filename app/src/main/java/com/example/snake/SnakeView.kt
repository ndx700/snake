package com.example.snake

import android.content.Context
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Paint
import android.os.Handler
import android.os.Looper
import android.view.MotionEvent
import android.view.View
import kotlin.math.abs
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
    private var gameOver = false
    private var running = false

    var onScoreChanged: ((Int) -> Unit)? = null

    private val paintSnake = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.rgb(46, 204, 113)
    }

    private val paintHead = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.rgb(39, 174, 96)
    }

    private val paintFood = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.rgb(231, 76, 60)
    }

    private val paintText = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.WHITE
        textSize = 48f
        textAlign = Paint.Align.CENTER
    }

    private val handler = Handler(Looper.getMainLooper())

    private val tick = object : Runnable {
        override fun run() {
            if (running) {
                update()
                invalidate()
                handler.postDelayed(this, 120L)
            }
        }
    }

    init {
        reset()
    }

    fun reset() {
        snake.clear()
        snake.add(Point(10, 10))

        dir = Point(0, 0)
        nextDir = Point(0, 0)

        score = 0
        gameOver = false

        placeFood()

        onScoreChanged?.invoke(score)
        invalidate()
    }

    fun resume() {
        if (!running) {
            running = true
            handler.post(tick)
        }
    }

    fun pause() {
        running = false
        handler.removeCallbacks(tick)
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

        // 修复后的方向控制逻辑：防止瞬间掉头撞到自己
        if (nextDir.x != 0 || nextDir.y != 0) {
            if (dir.x == 0 && dir.y == 0) {
                dir = nextDir // 初始状态，允许开始
            } else if (dir.x != 0 && nextDir.y != 0) {
                dir = nextDir // 水平移动中，只能上下转弯
            } else if (dir.y != 0 && nextDir.x != 0) {
                dir = nextDir // 垂直移动中，只能左右转弯
            }
        }

        if (dir.x == 0 && dir.y == 0) return

        val head = snake.first()
        val newHead = Point(head.x + dir.x, head.y + dir.y)

        if (newHead.x < 0 || newHead.x >= cols || newHead.y < 0 || newHead.y >= rows) {
            gameOver = true
            return
        }

        if (snake.any { it == newHead }) {
            gameOver = true
            return
        }

        snake.addFirst(newHead)

        if (newHead == food) {
            score++
            onScoreChanged?.invoke(score)
            placeFood()
        } else {
            snake.removeLast()
        }
    }

    override fun onDraw(canvas: Canvas) {
        super.onDraw(canvas)

        canvas.drawColor(Color.rgb(17, 17, 17))

        cellSize = minOf(width / cols.toFloat(), height / rows.toFloat())
        offsetX = (width - cellSize * cols) / 2f
        offsetY = (height - cellSize * rows) / 2f

        // 食物
        canvas.drawCircle(
            offsetX + food.x * cellSize + cellSize / 2,
            offsetY + food.y * cellSize + cellSize / 2,
            cellSize * 0.4f,
            paintFood
        )

        // 蛇
        snake.forEachIndexed { index, p ->
            val left = offsetX + p.x * cellSize + 2
            val top = offsetY + p.y * cellSize + 2
            val right = left + cellSize - 4
            val bottom = top + cellSize - 4

            canvas.drawRect(
                left,
                top,
                right,
                bottom,
                if (index == 0) paintHead else paintSnake
            )
        }

        // 游戏结束
        if (gameOver) {
            canvas.drawColor(0xAA000000.toInt())

            paintText.textSize = 48f
            canvas.drawText("游戏结束", width / 2f, height / 2f - 20, paintText)

            paintText.textSize = 28f
            canvas.drawText("点击屏幕重新开始", width / 2f, height / 2f + 40, paintText)
        } else if (dir.x == 0 && dir.y == 0) {
            paintText.textSize = 28f
            canvas.drawText("滑动屏幕开始", width / 2f, height / 2f, paintText)
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
