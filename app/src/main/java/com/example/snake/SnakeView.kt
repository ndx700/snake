package com.example.snake

import android.content.Context
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.LinearGradient
import android.graphics.Paint
import android.graphics.Path
import android.graphics.PointF
import android.graphics.RadialGradient
import android.graphics.Shader
import android.util.AttributeSet
import android.view.MotionEvent
import android.view.View
import android.os.Vibrator
import android.os.VibrationEffect
import android.os.Build
import kotlin.math.abs
import kotlin.math.atan2
import kotlin.math.cos
import kotlin.math.max
import kotlin.math.min
import kotlin.math.sin
import kotlin.random.Random

private const val COLS = 15
private const val ROWS = 15
private const val INIT_TICK = 180L
private const val MIN_TICK = 70L
private const val SPEED_STEP = 3L

private data class Point(val x: Int, val y: Int)

class SnakeView @JvmOverloads constructor(
    context: Context, attrs: AttributeSet? = null
) : View(context, attrs) {

    private var cellSize = 0f
    private var offX = 0f
    private var offY = 0f

    private val snake = ArrayDeque<Point>()
    private var dir = Point(1, 0)
    private val queue = ArrayDeque<Point>()
    private val bodyGrid = Array(COLS) { BooleanArray(ROWS) }
    private var food = Point(5, 5)

    private var score = 0
    private var high = 0
    private var money = 0
    private var gameOver = false
    private var running = true
    private var combo = 0
    private var hunger = 0
    private var tick = INIT_TICK
    private var lastUpdate = 0L

    private var skin = 0
    private val bodyColors = intArrayOf(
        Color.parseColor("#00E676"), Color.parseColor("#FF4081"),
        Color.parseColor("#7C4DFF"), Color.parseColor("#00E5FF"),
        Color.parseColor("#FFD600")
    )
    private val headColors = intArrayOf(
        Color.parseColor("#00C853"), Color.parseColor("#F50057"),
        Color.parseColor("#651FFF"), Color.parseColor("#00B8D4"),
        Color.parseColor("#FFAB00")
    )
    private var bodyColor = bodyColors[0]
    private var headColor = headColors[0]
    private var isRainbow = false
    private val rainbow = IntArray(361) { Color.HSVToColor(floatArrayOf(it.toFloat(), 1f, 1f)) }

    private var aiMode = 0
    private var aiLevel = 1
    private var aiBest = 0
    private var consecDeaths = 0
    private val hamPath = mutableListOf<Point>()

    private var deathFlash = 0f
    private var shakeTime = 0f
    private var shakeX = 0f
    private var shakeY = 0f
    private var shockX = 0f
    private var shockY = 0f
    private var shockR = 0f
    private var shockA = 0f

    private data class Particle(
        var x: Float, var y: Float, var vx: Float, var vy: Float,
        var life: Float, val color: Int, var size: Float, var decay: Float,
        var isTrail: Boolean
    )
    private data class FloatText(var x: Float, var y: Float, var life: Float, val text: String)
    private val particles = mutableListOf<Particle>()
    private val floats = mutableListOf<FloatText>()

    private val paintBg = Paint().apply { color = Color.BLACK }
    private val paintGrid = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        strokeWidth = 2f; setShadowLayer(8f, 0f, 0f, Color.CYAN)
    }
    private val paintBody = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        style = Paint.Style.STROKE; strokeCap = Paint.Cap.ROUND; strokeJoin = Paint.Join.ROUND
        color = bodyColor; setShadowLayer(20f, 0f, 0f, bodyColor)
    }
    private val paintHead = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        style = Paint.Style.FILL; color = headColor; setShadowLayer(15f, 0f, 0f, headColor)
    }
    private val paintEyeW = Paint(Paint.ANTI_ALIAS_FLAG).apply { color = Color.WHITE }
    private val paintEyeB = Paint(Paint.ANTI_ALIAS_FLAG).apply { color = Color.BLACK }
    private val paintHL = Paint(Paint.ANTI_ALIAS_FLAG).apply { color = Color.WHITE; alpha = 100 }
    private val paintFoodGlow = Paint(Paint.ANTI_ALIAS_FLAG).apply { style = Paint.Style.FILL }
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
    private val paintShock = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        style = Paint.Style.STROKE; strokeWidth = 8f; color = Color.RED
    }
    private val paintText = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.WHITE; textSize = 60f; textAlign = Paint.Align.CENTER
    }
    private val paintTextSm = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        color = Color.parseColor("#AAAAAA"); textSize = 36f; textAlign = Paint.Align.CENTER
    }
    private val paintHam = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        style = Paint.Style.STROKE; strokeWidth = 3f; color = Color.argb(60, 255, 255, 255)
    }

    private val vibrator: Vibrator =
        context.getSystemService(Context.VIBRATOR_SERVICE) as Vibrator

    init {
        isFocusable = true
        loadPrefs()
        initHamPath()
        reset()
    }

    private fun loadPrefs() {
        val p = context.getSharedPreferences("GamePrefs", Context.MODE_PRIVATE)
        high = p.getInt("HighScore", 0)
        money = p.getInt("Money", 0)
        aiLevel = p.getInt("AiLevel", 1)
        aiBest = p.getInt("AiBest", 0)
        consecDeaths = p.getInt("Consec", 0)
    }

    private fun savePrefs() {
        context.getSharedPreferences("GamePrefs", Context.MODE_PRIVATE).edit()
            .putInt("HighScore", high).putInt("Money", money)
            .putInt("AiLevel", aiLevel).putInt("AiBest", aiBest)
            .putInt("Consec", consecDeaths).apply()
    }

    private fun initHamPath() {
        hamPath.clear()
        for (x in 0 until COLS) {
            if (x % 2 == 0) for (y in 0 until ROWS) hamPath.add(Point(x, y))
            else for (y in ROWS - 1 downTo 0) hamPath.add(Point(x, y))
        }
    }

    private fun reset() {
        snake.clear()
        if (aiMode == 2) {
            snake.add(Point(0, 0)); dir = Point(0, 1)
        } else {
            snake.addFirst(Point(0, 0)); snake.addFirst(Point(1, 0)); snake.addFirst(Point(2, 0))
            dir = Point(1, 0)
        }
        queue.clear()
        tick = INIT_TICK; score = 0; combo = 0; hunger = 0
        gameOver = false; running = true
        deathFlash = 0f; shakeTime = 0f; shockA = 0f
        particles.clear(); floats.clear()
        rebuildGrid(); applySkin()
        lastUpdate = System.currentTimeMillis()
        spawnFood()
        invalidate()
    }

    private fun rebuildGrid() {
        for (x in 0 until COLS) for (y in 0 until ROWS) bodyGrid[x][y] = false
        for (p in snake) if (p.x in 0 until COLS && p.y in 0 until ROWS) bodyGrid[p.x][p.y] = true
    }

    private fun onBody(x: Int, y: Int) =
        x in 0 until COLS && y in 0 until ROWS && bodyGrid[x][y]

    private fun applySkin() {
        isRainbow = (skin == 5)
        if (isRainbow) {
            paintBody.shader = null
            paintBody.setShadowLayer(35f, 0f, 0f, Color.WHITE)
            paintHead.color = Color.WHITE
            paintHead.setShadowLayer(15f, 0f, 0f, Color.WHITE)
        } else {
            bodyColor = bodyColors[skin.coerceIn(0, 4)]
            headColor = headColors[skin.coerceIn(0, 4)]
            paintBody.shader = null
            paintBody.color = bodyColor
            paintBody.setShadowLayer(20f, 0f, 0f, bodyColor)
            paintHead.color = headColor
            paintHead.setShadowLayer(15f, 0f, 0f, headColor)
        }
    }

    private fun spawnFood() {
        var nx: Int; var ny: Int; var a = 0
        do {
            nx = Random.nextInt(COLS); ny = Random.nextInt(ROWS); a++
        } while (onBody(nx, ny) && a < 500)
        if (onBody(nx, ny)) {
            outer@ for (x in 0 until COLS) for (y in 0 until ROWS) {
                if (!onBody(x, y)) { nx = x; ny = y; break@outer }
            }
        }
        food = Point(nx, ny)
    }

    fun update() {
        if (!running || gameOver) return
        val now = System.currentTimeMillis()
        if (now - lastUpdate < tick) return
        lastUpdate = now

        when (aiMode) { 1 -> aiBfs(); 2 -> aiHam() }

        if (queue.isNotEmpty()) dir = queue.removeFirst()

        val head = snake.first()
        val nh = Point(head.x + dir.x, head.y + dir.y)
        if (nh.x !in 0 until COLS || nh.y !in 0 until ROWS) { die(); return }

        val eat = nh == food
        val body = if (eat) snake else snake.dropLast(1)
        if (body.any { it == nh }) { die(); return }

        snake.addFirst(nh); bodyGrid[nh.x][nh.y] = true

        if (eat) {
            combo++
            val base = 10 + (combo - 1) * 5
            val mult = when { score >= 1000 -> 3f; score >= 500 -> 2f; score >= 200 -> 1.5f; else -> 1f }
            val earned = (base * mult).toInt()
            score += earned
            money += when { score >= 1000 -> 10; score >= 500 -> 5; else -> 1 }
            if (score > high) high = score
            foodBurst(nh)
            floats.add(FloatText(
                offX + nh.x * cellSize + cellSize / 2,
                offY + nh.y * cellSize + cellSize / 2, 1f, "+$earned"
            ))
            tick = (tick - SPEED_STEP).coerceAtLeast(MIN_TICK)
            vibrate(80L)
            spawnFood(); hunger = 0
        } else {
            val t = snake.removeLast(); bodyGrid[t.x][t.y] = false
            hunger++
        }
        invalidate()
    }

    private fun updateFx(dt: Float) {
        if (gameOver) {
            deathFlash = 120f + 60f * sin(System.currentTimeMillis() / 150.0).toFloat()
            if (shockA > 0) { shockR += dt * 0.5f; shockA -= dt * 0.05f }
        } else if (deathFlash > 0) deathFlash = max(0f, deathFlash - dt * 0.2f)
        if (shakeTime > 0) {
            shakeTime -= dt
            shakeX = (Random.nextFloat() - 0.5f) * 30f * (shakeTime / 400f)
            shakeY = (Random.nextFloat() - 0.5f) * 30f * (shakeTime / 400f)
        } else { shakeX = 0f; shakeY = 0f }
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

    private data class Move(
        val dir: Point, val willEat: Boolean, val canTail: Boolean,
        val foodOk: Boolean, val space: Int, val dist: Int, val eatSafe: Boolean
    )

    private fun aiBfs() {
        val head = snake.first()
        val dirs = listOf(Point(1, 0), Point(-1, 0), Point(0, 1), Point(0, -1))
        queue.clear()
        val moves = mutableListOf<Move>()

        for (d in dirs) {
            if (d.x == -dir.x && d.y == -dir.y) continue
            val n = Point(head.x + d.x, head.y + d.y)
            if (n.x !in 0 until COLS || n.y !in 0 until ROWS) continue
            val eat = n == food
            val body = if (eat) snake else snake.dropLast(1)
            if (body.any { it == n }) continue

            val sim = ArrayDeque(snake); sim.addFirst(n); sim.removeLast()
            val canTail = bfs(n, sim.last(), sim).isNotEmpty()
            val reachable = reachable(n, sim)
            val foodOk = reachable.contains(food)
            val distPath = bfs(n, food, sim)
            val dist = if (distPath.isNotEmpty()) distPath.size else 9999
            var eatSafe = true
            if (eat) {
                val se = ArrayDeque(snake); se.addFirst(n)
                eatSafe = bfs(n, se.last(), se).isNotEmpty()
            }
            moves.add(Move(d, eat, canTail, foodOk, reachable.size, dist, eatSafe))
        }
        if (moves.isEmpty()) return

        // 第1层：食物贴脸+安全
        for (m in moves) if (m.willEat && m.eatSafe) { queue.add(m.dir); return }
        // 第2层：极度饥饿
        if (hunger > 15) {
            var best: Move? = null
            for (m in moves) if (m.foodOk || m.willEat) if (best == null || m.dist < best.dist) best = m
            if (best != null) { queue.add(best.dir); return }
        }
        // 第3层：能追到尾巴中选最优
        var bestTail: Move? = null
        for (m in moves) {
            if (!m.canTail) continue
            if (bestTail == null) { bestTail = m; continue }
            val b = bestTail
            val mf = if (m.foodOk) 1 else 0
            val bf = if (b.foodOk) 1 else 0
            val better = when {
                mf > bf -> true; mf < bf -> false
                m.dist < b.dist -> true; m.dist > b.dist -> false
                m.space > b.space -> true; else -> false
            }
            if (better) bestTail = m
        }
        if (bestTail != null) { queue.add(bestTail.dir); return }
        // 第4层：死局搏命
        var bestFood: Move? = null
        for (m in moves) if (m.foodOk || m.willEat) if (bestFood == null || m.dist < bestFood.dist) bestFood = m
        if (bestFood != null) { queue.add(bestFood.dir); return }
        // 兜底
        var bestSpace: Move? = null
        for (m in moves) if (bestSpace == null || m.space > bestSpace.space) bestSpace = m
        if (bestSpace != null) queue.add(bestSpace.dir)
        else moves.firstOrNull()?.let { queue.add(it.dir) }
    }

    private fun bfs(start: Point, target: Point, custom: ArrayDeque<Point>): List<Point> {
        val q = ArrayDeque<Point>(); val vis = HashSet<Point>(); val par = HashMap<Point, Point>()
        q.add(start); vis.add(start)
        while (q.isNotEmpty()) {
            val c = q.removeFirst()
            if (c == target) {
                val p = mutableListOf<Point>(); var n: Point? = c
                while (n != null && n != start) { p.add(n); n = par[n] }
                return p.reversed()
            }
            for (d in listOf(Point(1, 0), Point(-1, 0), Point(0, 1), Point(0, -1))) {
                val nx = Point(c.x + d.x, c.y + d.y)
                if (nx.x !in 0 until COLS || nx.y !in 0 until ROWS) continue
                if (vis.contains(nx)) continue
                if (nx != target) {
                    val body = if (nx == custom.last()) custom.dropLast(1) else custom
                    if (body.any { it == nx }) continue
                }
                vis.add(nx); par[nx] = c; q.add(nx)
            }
        }
        return emptyList()
    }

    private fun reachable(start: Point, custom: ArrayDeque<Point>): Set<Point> {
        val q = ArrayDeque<Point>(); val vis = HashSet<Point>(); q.add(start); vis.add(start)
        while (q.isNotEmpty()) {
            val c = q.removeFirst()
            for (d in listOf(Point(1, 0), Point(-1, 0), Point(0, 1), Point(0, -1))) {
                val nx = Point(c.x + d.x, c.y + d.y)
                if (nx.x !in 0 until COLS || nx.y !in 0 until ROWS) continue
                if (vis.contains(nx)) continue
                if (nx != custom.last() && custom.any { it == nx }) continue
                vis.add(nx); q.add(nx)
            }
        }
        return vis
    }

    private fun aiHam() {
        val head = snake.first()
        var idx = hamPath.indexOf(head)
        if (idx == -1) {
            var md = Int.MAX_VALUE; var cl = 0
            for (i in hamPath.indices) {
                val p = hamPath[i]; val d = abs(p.x - head.x) + abs(p.y - head.y)
                if (d < md) { md = d; cl = i }
            }
            idx = cl
        }
        val ni = (idx + 1) % hamPath.size
        val np = hamPath[ni]
        val dx = np.x - head.x; val dy = np.y - head.y
        if (abs(dx) + abs(dy) != 1) { aiBfs(); return }
        queue.clear(); queue.add(Point(dx, dy))
    }

    private fun die() {
        gameOver = true; running = false; aiMode = 0
        shakeTime = 400f; deathFlash = 255f
        val h = snake.first()
        shockX = offX + h.x * cellSize + cellSize / 2
        shockY = offY + h.y * cellSize + cellSize / 2
        shockR = cellSize; shockA = 255f
        repeat(60) { particle(shockX, shockY, Color.RED, true) }
        vibrate(300L)
        consecDeaths++
        if (score > high) high = score
        if (score > aiBest) {
            aiBest = score
            if (score > 100) aiLevel = (aiLevel + 1).coerceAtMost(10)
            consecDeaths = 0
        } else if (score < 50) {
            if (consecDeaths >= 2 || score < aiBest * 0.3) {
                aiLevel = (aiLevel - 1).coerceAtLeast(1); consecDeaths = 0
            }
        } else consecDeaths = 0
        savePrefs(); invalidate()
    }

    private fun foodBurst(at: Point) {
        val cx = offX + at.x * cellSize + cellSize / 2
        val cy = offY + at.y * cellSize + cellSize / 2
        repeat(25) { particle(cx, cy, Color.YELLOW, false) }
    }

    private fun particle(x: Float, y: Float, color: Int, death: Boolean) {
        if (particles.size >= 300) particles.removeAt(0)
        val a = Random.nextFloat() * 6.2832f
        val s = if (death) Random.nextFloat() * 12f + 3f else Random.nextFloat() * 8f + 2f
        particles.add(Particle(
            x + (Random.nextFloat() - 0.5f) * cellSize * 0.5f,
            y + (Random.nextFloat() - 0.5f) * cellSize * 0.5f,
            cos(a) * s, sin(a) * s,
            if (death) 1.5f else 1f, color,
            Random.nextFloat() * 1.5f + 0.5f,
            if (death) 0.002f else 0.0015f,
            false
        ))
    }

    override fun onSizeChanged(w: Int, h: Int, ow: Int, oh: Int) {
        super.onSizeChanged(w, h, ow, oh)
        cellSize = minOf(w / COLS.toFloat(), h / ROWS.toFloat())
        offX = (w - cellSize * COLS) / 2f
        offY = (h - cellSize * ROWS) / 2f
    }

    override fun onDraw(canvas: Canvas) {
        super.onDraw(canvas)
        val dt = 16f
        updateFx(dt)
        cellSize = minOf(width / COLS.toFloat(), height / ROWS.toFloat())
        offX = (width - cellSize * COLS) / 2f
        offY = (height - cellSize * ROWS) / 2f
        canvas.drawColor(Color.BLACK)
        canvas.save()
        if (gameOver && shakeTime > 0) canvas.translate(shakeX, shakeY)

        // 呼吸网格
        val breath = (sin(System.currentTimeMillis() / 400.0).toFloat() + 1f) / 2f
        paintGrid.alpha = (60 + 195 * breath).toInt().coerceIn(0, 255)
        paintGrid.color = if (isRainbow) {
            val c = rainbow[((System.currentTimeMillis() / 20).toInt()) % 360]
            Color.argb(200, Color.red(c), Color.green(c), Color.blue(c))
        } else Color.CYAN
        for (i in 0..COLS) {
            val x = offX + i * cellSize
            canvas.drawLine(x, offY, x, offY + ROWS * cellSize, paintGrid)
        }
        for (i in 0..ROWS) {
            val y = offY + i * cellSize
            canvas.drawLine(offX, y, offX + COLS * cellSize, y, paintGrid)
        }

        if (aiMode == 2 && !gameOver) {
            for (i in 0 until hamPath.size - 1) {
                val a = hamPath[i]; val b = hamPath[i + 1]
                canvas.drawLine(
                    offX + a.x * cellSize + cellSize / 2, offY + a.y * cellSize + cellSize / 2,
                    offX + b.x * cellSize + cellSize / 2, offY + b.y * cellSize + cellSize / 2,
                    paintHam
                )
            }
        }

        // 食物
        val fx = offX + food.x * cellSize + cellSize / 2
        val fy = offY + food.y * cellSize + cellSize / 2
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
        canvas.drawCircle(fx, fy, fr * 0.35f, paintFoodCore)

        // 蛇
        if (snake.isNotEmpty()) {
            val path = Path()
            val pts = snake.mapIndexed { i, p ->
                val bx = offX + p.x * cellSize + cellSize / 2
                val by = offY + p.y * cellSize + cellSize / 2
                val t = System.currentTimeMillis() / 200.0
                val amp = if (dir.x != 0) cellSize * 0.1f else cellSize * 0.05f
                PointF(bx + sin(t + i * 0.5).toFloat() * amp, by + cos(t + i * 0.5).toFloat() * amp)
            }
            path.moveTo(pts[0].x, pts[0].y)
            for (i in 1 until pts.size) {
                val p = pts[i - 1]; val c = pts[i]
                path.quadTo(p.x, p.y, (p.x + c.x) / 2f, (p.y + c.y) / 2f)
            }
            if (pts.size > 1) path.lineTo(pts.last().x, pts.last().y)

            if (isRainbow) {
                val hp = pts.first(); val tp = pts.last()
                val ang = atan2(tp.y - hp.y, tp.x - hp.x)
                val to = (System.currentTimeMillis() % 3000) / 3000f
                val fd = cellSize * 6 * to
                paintBody.shader = LinearGradient(
                    hp.x - cos(ang) * fd, hp.y - sin(ang) * fd,
                    tp.x - cos(ang) * fd, tp.y - sin(ang) * fd,
                    rainbow, null, Shader.TileMode.MIRROR
                )
                paintBody.alpha = 255
                paintBody.setShadowLayer(35f, 0f, 0f, Color.WHITE)
            } else {
                paintBody.shader = null
                paintBody.color = bodyColor
                paintBody.alpha = 255
                paintBody.setShadowLayer(20f, 0f, 0f, bodyColor)
            }
            paintBody.strokeWidth = cellSize * 0.8f
            paintBody.alpha = if (isRainbow) 150 else 120
            canvas.drawPath(path, paintBody)
            paintBody.strokeWidth = cellSize * 0.65f
            paintBody.alpha = 255
            canvas.drawPath(path, paintBody)

            val hp = pts.first()
            canvas.drawCircle(hp.x, hp.y, cellSize * 0.5f, paintHead)
            canvas.drawCircle(hp.x - cellSize * 0.1f, hp.y - cellSize * 0.1f, cellSize * 0.15f, paintHL)
            val eo = cellSize * 0.2f; val er = cellSize * 0.12f; val pr = cellSize * 0.06f
            val px = -dir.y * (cellSize * 0.2f); val py = dir.x * (cellSize * 0.2f)
            canvas.drawCircle(hp.x + dir.x * eo + px, hp.y + dir.y * eo + py, er, paintEyeW)
            canvas.drawCircle(hp.x + dir.x * eo - px, hp.y + dir.y * eo - py, er, paintEyeW)
            canvas.drawCircle(hp.x + dir.x * eo * 1.2f + px, hp.y + dir.y * eo * 1.2f + py, pr, paintEyeB)
            canvas.drawCircle(hp.x + dir.x * eo * 1.2f - px, hp.y + dir.y * eo * 1.2f - py, pr, paintEyeB)
        }

        particles.forEach { p ->
            paintParticle.color = p.color
            paintParticle.alpha = (p.life * 255).toInt().coerceIn(0, 255)
            canvas.drawCircle(p.x, p.y, cellSize * 0.1f * p.life * p.size, paintParticle)
        }
        if (shockA > 0) {
            paintShock.alpha = shockA.toInt().coerceIn(0, 255)
            canvas.drawCircle(shockX, shockY, shockR, paintShock)
        }
        floats.forEach { t ->
            paintFloat.alpha = (t.life * 255).toInt().coerceIn(0, 255)
            canvas.drawText(t.text, t.x, t.y, paintFloat)
        }
        canvas.restore()

        if (gameOver) {
            canvas.drawColor(Color.argb(deathFlash.toInt().coerceIn(0, 255), 180, 0, 0))
            paintText.textSize = 80f; paintText.color = Color.RED
            paintText.setShadowLayer(20f, 0f, 0f, Color.BLACK)
            canvas.drawText("GAME OVER", width / 2f, height / 2f - 60, paintText)
            paintText.textSize = 40f; paintText.color = Color.WHITE
            canvas.drawText("最终得分: $score", width / 2f, height / 2f + 10, paintText)
            paintTextSm.textSize = 30f; paintTextSm.color = Color.rgb(241, 196, 15)
            canvas.drawText("最高分: $high", width / 2f, height / 2f + 60, paintTextSm)
            paintTextSm.textSize = 20f; paintTextSm.color = Color.LTGRAY
            canvas.drawText("AI Lv.$aiLevel | Best $aiBest", width / 2f, height / 2f + 100, paintTextSm)
            if ((System.currentTimeMillis() / 500) % 2 == 0L) {
                paintTextSm.textSize = 28f; paintTextSm.color = Color.WHITE
                canvas.drawText("点击屏幕重新开始", width / 2f, height / 2f + 160, paintTextSm)
            }
        } else {
            paintText.textSize = 40f; paintText.color = Color.WHITE
            canvas.drawText("Score: $score", width / 2f, 60f, paintText)
            paintTextSm.textSize = 26f; paintTextSm.color = Color.parseColor("#AAAAAA")
            canvas.drawText("High: $high  Money: $money", width / 2f, 100f, paintTextSm)
        }
    }

    override fun onTouchEvent(e: MotionEvent): Boolean {
        if (e.action == MotionEvent.ACTION_DOWN) {
            if (gameOver) { reset(); return true }
            val dx = e.x - width / 2f; val dy = e.y - height / 2f
            val nd = when {
                abs(dx) > abs(dy) -> if (dx > 0) Point(1, 0) else Point(-1, 0)
                else -> if (dy > 0) Point(0, 1) else Point(0, -1)
            }
            if (!(nd.x == -dir.x && nd.y == -dir.y) && queue.size < 3) queue.add(nd)
            performClick(); return true
        }
        return super.onTouchEvent(e)
    }

    override fun performClick(): Boolean { super.performClick(); return true }

    private fun vibrate(ms: Long) {
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O)
            vibrator.vibrate(VibrationEffect.createOneShot(ms, VibrationEffect.DEFAULT_AMPLITUDE))
        else @Suppress("DEPRECATION") vibrator.vibrate(ms)
    }

    fun setSkin(i: Int) { skin = i; applySkin(); invalidate() }
    fun setAiMode(m: Int) { aiMode = m; queue.clear(); reset() }
    fun getScore() = score
    fun getHighScore() = high
    fun getMoney() = money
    fun isGameOver() = gameOver
}
