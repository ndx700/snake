package com.example.snake

import android.content.Context
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Paint
import android.graphics.RectF
import android.util.AttributeSet
import android.util.Log
import android.view.Choreographer
import android.view.MotionEvent
import android.view.View
import java.io.DataInputStream
import java.io.DataOutputStream
import java.io.File
import java.io.FileInputStream
import java.io.FileOutputStream
import java.util.Random
import java.util.concurrent.ConcurrentLinkedQueue
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.atomic.AtomicLong
import kotlin.math.abs
import kotlin.math.ln
import kotlin.math.max
import kotlin.math.min
import kotlin.math.sqrt

/* ============================================================================
 * SNAKE PRO v8 完整版
 * 底层 = 参考文件保命逻辑(可150+)，学习网络只做安全改道
 * 8线程无头训练 / 世代统计 / 存档续跑 / 图表HUD / 策略亮灯
 * ==========================================================================*/

enum class StepResult { MOVED, ATE, DIED }
enum class DeathReason { WALL, SELF, TRAPPED, STARVED, WIN }

class GameEngine(val w: Int = 15, val h: Int = 15) {
    companion object { val DIRS = arrayOf(0 to -1, 1 to 0, 0 to 1, -1 to 0) }
    val snake = ArrayDeque<Pair<Int, Int>>()
    var food = 0 to 0
    var dir = 1
    var alive = false
    var score = 0
    var stepsSinceFood = 0
    var totalSteps = 0L
    var deathReason = DeathReason.WALL
    private val rng = Random()

    fun occupied(x: Int, y: Int): Boolean {
        for (c in snake) if (c.first == x && c.second == y) return true
        return false
    }

    fun reset() {
        snake.clear()
        val cx = w / 2; val cy = h / 2
        snake.addLast(cx to cy); snake.addLast((cx - 1) to cy); snake.addLast((cx - 2) to cy)
        dir = 1; score = 0; stepsSinceFood = 0; totalSteps = 0
        alive = true; deathReason = DeathReason.WALL
        spawnFood()
    }

    fun head() = snake.first()
    fun tail() = snake.last()

    fun nextCell(d: Int): Pair<Int, Int>? {
        val nd = if (snake.size > 1 && (d + 2) % 4 == dir) dir else d
        val (dx, dy) = DIRS[nd]
        val nx = head().first + dx; val ny = head().second + dy
        return if (nx < 0 || ny < 0 || nx >= w || ny >= h) null else nx to ny
    }

    private fun spawnFood() {
        repeat(300) {
            val x = rng.nextInt(w); val y = rng.nextInt(h)
            if (!occupied(x, y)) { food = x to y; return }
        }
        val free = ArrayList<Pair<Int, Int>>()
        for (y in 0 until h) for (x in 0 until w) if (!occupied(x, y)) free.add(x to y)
        if (free.isEmpty()) { alive = false; deathReason = DeathReason.WIN; return }
        food = free[rng.nextInt(free.size)]
    }

    fun step(d: Int): StepResult {
        if (!alive) return StepResult.DIED
        if (snake.size <= 1 || (d + 2) % 4 != dir) dir = d
        val (dx, dy) = DIRS[dir]
        val nx = head().first + dx; val ny = head().second + dy
        if (nx < 0 || ny < 0 || nx >= w || ny >= h) { die(DeathReason.WALL); return StepResult.DIED }
        val eating = nx == food.first && ny == food.second
        val tc = tail()
        if (occupied(nx, ny) && !(nx == tc.first && ny == tc.second && !eating)) {
            die(DeathReason.SELF); return StepResult.DIED
        }
        snake.addFirst(nx to ny)
        totalSteps++
        return if (eating) {
            score++; stepsSinceFood = 0; spawnFood()
            if (alive) StepResult.ATE else StepResult.DIED
        } else {
            snake.removeLast()
            stepsSinceFood++
            if (stepsSinceFood > w * h * 2) { die(DeathReason.STARVED); StepResult.DIED }
            else StepResult.MOVED
        }
    }

    private fun die(r: DeathReason) { alive = false; deathReason = r }
}

class Sim(val w: Int, val h: Int) {
    val occ = BooleanArray(w * h)
    val body = ArrayDeque<Int>()
    var head = -1
    var foodIdx = -1
    val n get() = occ.size
    val tail get() = body.last()
    val len get() = body.size

    fun load(e: GameEngine): Sim {
        java.util.Arrays.fill(occ, false)
        body.clear()
        for (c in e.snake) { val i = c.second * w + c.first; occ[i] = true; body.addLast(i) }
        head = body.first()
        foodIdx = e.food.second * w + e.food.first
        return this
    }

    fun copy(): Sim {
        val s = Sim(w, h)
        System.arraycopy(occ, 0, s.occ, 0, occ.size)
        s.body.addAll(body); s.head = head; s.foodIdx = foodIdx
        return s
    }

    private val nb = IntArray(4)
    fun neighbors(i: Int, out: IntArray = nb): Int {
        val x = i % w; val y = i / w
        var k = 0
        if (y > 0) out[k++] = i - w
        if (x < w - 1) out[k++] = i + 1
        if (y < h - 1) out[k++] = i + w
        if (x > 0) out[k++] = i - 1
        return k
    }

    fun free(i: Int) = !occ[i] || i == tail

    fun targetOf(d: Int): Int? {
        val (dx, dy) = GameEngine.DIRS[d]
        val x = head % w + dx; val y = head / w + dy
        if (x < 0 || y < 0 || x >= w || y >= h) return null
        return y * w + x
    }

    fun step(d: Int, eat: Boolean): Boolean {
        val ni = targetOf(d) ?: return false
        if (occ[ni] && !(ni == tail && !eat)) return false
        if (!eat) { val t = body.removeLast(); occ[t] = false }
        body.addFirst(ni); occ[ni] = true; head = ni
        if (eat) foodIdx = -1
        return true
    }

    fun stepAuto(d: Int): Boolean {
        val t = targetOf(d) ?: return false
        return step(d, t == foodIdx)
    }

    fun flood(start: Int): Int {
        var c = 0
        val seen = BooleanArray(n)
        val q = ArrayDeque<Int>()
        seen[start] = true; q.addLast(start)
        val buf = IntArray(4)
        while (q.isNotEmpty()) {
            val cur = q.removeFirst(); c++
            val m = neighbors(cur, buf)
            for (i in 0 until m) { val nx = buf[i]; if (!seen[nx] && free(nx)) { seen[nx] = true; q.add(nx) } }
        }
        return c
    }

    /** 考虑尾巴移动时间的可达性检查 */
    fun tailReachSteps(start: Int): Int {
        val freeTime = IntArray(n) { Int.MAX_VALUE }
        var t = 1
        for (i in body.size - 1 downTo 0) freeTime[body.elementAt(i)] = t++
        val best = IntArray(n) { -1 }
        val q = ArrayDeque<Int>()
        best[start] = 1; q.addLast(start)
        val buf = IntArray(4)
        while (q.isNotEmpty()) {
            val cur = q.removeFirst()
            val curT = best[cur]
            if (cur == tail) return curT
            val m = neighbors(cur, buf)
            for (i in 0 until m) {
                val nx = buf[i]
                if (best[nx] >= 0) continue
                val arrive = curT + 1
                if (!occ[nx] || freeTime[nx] <= arrive) { best[nx] = arrive; q.add(nx) }
            }
        }
        return -1
    }

    fun shortestPathTo(target: Int): IntArray? {
        if (target < 0) return null
        if (head == target) return IntArray(0)
        val parent = IntArray(n) { -1 }
        val seen = BooleanArray(n)
        val q = ArrayDeque<Int>()
        seen[head] = true
        q.addLast(head)
        val buf = IntArray(4)
        var found = false
        while (q.isNotEmpty() && !found) {
            val cur = q.removeFirst()
            val m = neighbors(cur, buf)
            for (i in 0 until m) {
                val nx = buf[i]
                if (seen[nx] || !free(nx)) continue
                seen[nx] = true
                parent[nx] = cur
                if (nx == target) { found = true; break }
                q.addLast(nx)
            }
        }
        if (!found) return null
        var len = 0
        var cur = target
        while (cur != head) { cur = parent[cur]; len++ }
        val path = IntArray(len)
        cur = target
        for (i in len - 1 downTo 0) { path[i] = cur; cur = parent[cur] }
        return path
    }
}

object Hamiltonian {
    private var cw = -1; private var ch = -1
    private lateinit var order: IntArray
    private lateinit var cells: IntArray

    fun ensure(w: Int, h: Int) {
        if (w == cw && h == ch) return
        cw = w; ch = h
        order = IntArray(w * h); cells = IntArray(w * h)
        var left = 0; var right = w - 1; var top = 0; var bottom = h - 1
        var i = 0
        while (i < w * h) {
            var x = left
            while (x <= right && i < w * h) { order[top * w + x] = i; cells[i] = top * w + x; i++; x++ }
            top++
            var y = top
            while (y <= bottom && i < w * h) { order[y * w + right] = i; cells[i] = y * w + right; i++; y++ }
            right--
            x = right
            while (x >= left && i < w * h) { order[bottom * w + x] = i; cells[i] = bottom * w + x; i++; x-- }
            bottom--
            y = bottom
            while (y >= top && i < w * h) { order[y * w + left] = i; cells[i] = y * w + left; i++; y-- }
            left++
        }
    }

    fun follow(e: GameEngine, strict: Boolean): Int {
        ensure(e.w, e.h)
        val N = e.w * e.h
        val hd = e.head()
        val hi = order[hd.second * e.w + hd.first]
        var bestD = -1; var bestGain = Int.MAX_VALUE
        for (d in 0 until 4) {
            if (e.snake.size > 1 && (d + 2) % 4 == e.dir) continue
            val c = e.nextCell(d) ?: continue
            if (e.occupied(c.first, c.second)) continue
            val ci = c.second * e.w + c.first
            val gain = (order[ci] - hi + N) % N
            var ok = false
            if (strict) ok = gain == 1
            else {
                var allFree = true; var k = 1
                while (k < gain && allFree) {
                    val mid = cells[(hi + k) % N]
                    if (e.occupied(mid % e.w, mid / e.w)) allFree = false
                    k++
                }
                ok = gain in 1..min(N - 1, 40) && allFree
            }
            if (ok && gain < bestGain) { bestGain = gain; bestD = d }
        }
        if (bestD >= 0) return bestD
        for (d in 0 until 4) {
            if (e.snake.size > 1 && (d + 2) % 4 == e.dir) continue
            val c = e.nextCell(d) ?: continue
            if (!e.occupied(c.first, c.second)) return d
        }
        return e.dir
    }
}

class FailureMemory(private val cap: Int = 6000) {
    private val map = HashMap<Int, Int>()
    private val lru = ArrayDeque<Int>()
    fun record(x: Int, y: Int, dir: Int) {
        val k = ((y * 256 + x) * 5 + dir)
        map[k] = (map[k] ?: 0) + 1
        lru.addLast(k)
        if (lru.size > cap) {
            val old = lru.removeFirst()
            map[old]?.let { if (it <= 1) map.remove(old) else map[old] = it - 1 }
        }
    }
    fun danger(x: Int, y: Int, dir: Int) = min(1.0, (map[(y * 256 + x) * 5 + dir] ?: 0) / 5.0)
    fun size() = map.size
    fun write(dos: DataOutputStream) {
        val top = map.entries.sortedByDescending { it.value }.take(1500)
        dos.writeInt(top.size)
        for ((k, v) in top) { dos.writeInt(k); dos.writeInt(v) }
    }
    fun read(dis: DataInputStream) = try {
        val n = dis.readInt().coerceIn(0, 100000)
        repeat(n) {
            val k = dis.readInt(); val v = dis.readInt()
            if (v > 0) { map[k] = v; lru.addLast(k) }
        }
    } catch (t: Throwable) { Log.w("SnakeAI", "mem read", t) }
}

class Genome {
    var margin = 4.0; var tailBias = 1.0; var risk = 0.4
    var trust = 0.3; var patience = 0.45; var lambda = 0.8
    private fun vec() = doubleArrayOf(margin, tailBias, risk, trust, patience, lambda)
    private fun load(v: DoubleArray) {
        margin = v[0].coerceIn(0.0, 20.0); tailBias = v[1].coerceIn(0.0, 5.0)
        risk = v[2].coerceIn(0.05, 1.0); trust = v[3].coerceIn(0.0, 1.0)
        patience = v[4].coerceIn(0.1, 0.9); lambda = v[5].coerceIn(0.0, 2.0)
    }
    fun adjust(r: DeathReason) {
        val a = 0.04
        when (r) {
            DeathReason.TRAPPED -> { margin += a * 4; tailBias += a * 2; lambda += a }
            DeathReason.STARVED -> { risk += a; patience -= a }
            DeathReason.WALL, DeathReason.SELF -> margin += a * 2
            DeathReason.WIN -> margin -= a * 2
        }
        load(vec())
    }
    fun params(): List<Triple<String, Double, Double>> = listOf(
        Triple("安全边际", margin, 20.0), Triple("追尾偏好", tailBias, 5.0),
        Triple("冒险度", risk, 1.0), Triple("信任AI", trust, 1.0),
        Triple("耐心", patience, 0.9), Triple("风险厌恶", lambda, 2.0)
    )
    fun write(dos: DataOutputStream) { for (v in vec()) dos.writeDouble(v) }
    fun read(dis: DataInputStream) = try { load(DoubleArray(6) { dis.readDouble() }) } catch (t: Throwable) {}
}

class Brain(val inp: Int, val h1: Int, val h2: Int, val out: Int, seed: Long) {
    val w1 = DoubleArray(inp * h1); val b1 = DoubleArray(h1)
    val w2 = DoubleArray(h1 * h2); val b2 = DoubleArray(h2)
    val w3 = DoubleArray(h2 * out); val b3 = DoubleArray(out)
    private val a1 = DoubleArray(h1); private val a2 = DoubleArray(h2)
    private val q = DoubleArray(out)
    private val dz2 = DoubleArray(h2); private val dz1 = DoubleArray(h1)

    init {
        val rnd = Random(seed)
        for (i in w1.indices) w1[i] = rnd.nextGaussian() / sqrt(inp.toDouble())
        for (i in w2.indices) w2[i] = rnd.nextGaussian() / sqrt(h1.toDouble())
        for (i in w3.indices) w3[i] = rnd.nextGaussian() / sqrt(h2.toDouble())
    }

    fun forward(x: DoubleArray): DoubleArray {
        for (j in 0 until h1) {
            var s = b1[j]; val off = j * inp
            for (k in 0 until inp) s += w1[off + k] * x[k]
            a1[j] = if (s > 0) s else 0.0
        }
        for (j in 0 until h2) {
            var s = b2[j]; val off = j * h1
            for (k in 0 until h1) s += w2[off + k] * a1[k]
            a2[j] = if (s > 0) s else 0.0
        }
        for (o in 0 until out) {
            var s = b3[o]; val off = o * h2
            for (j in 0 until h2) s += w3[off + j] * a2[j]
            q[o] = s
        }
        return q
    }

    fun train(x: DoubleArray, act: Int, target: Double, lr: Double) {
        forward(x)
        val err = (q[act] - target).coerceIn(-2.0, 2.0)
        val dOut = DoubleArray(out)
        dOut[act] = err
        java.util.Arrays.fill(dz2, 0.0)
        for (o in 0 until out) {
            if (dOut[o] == 0.0) continue
            val off = o * h2
            for (j in 0 until h2) {
                w3[off + j] -= lr * dOut[o] * a2[j]
                if (a2[j] > 0) dz2[j] += w3[off + j] * dOut[o]
            }
            b3[o] -= lr * dOut[o]
        }
        java.util.Arrays.fill(dz1, 0.0)
        for (j in 0 until h2) {
            if (a2[j] <= 0 || dz2[j] == 0.0) continue
            val off = j * h1
            for (k in 0 until h1) {
                w2[off + k] -= lr * dz2[j] * a1[k]
                if (a1[k] > 0) dz1[k] += w2[off + k] * dz2[j]
            }
            b2[j] -= lr * dz2[j]
        }
        for (j in 0 until h1) {
            if (a1[j] <= 0 || dz1[j] == 0.0) continue
            val off = j * inp
            for (k in 0 until inp) w1[off + k] -= lr * dz1[j] * x[k]
            b1[j] -= lr * dz1[j]
        }
    }

    fun copyFrom(o: Brain) {
        System.arraycopy(o.w1, 0, w1, 0, w1.size); System.arraycopy(o.b1, 0, b1, 0, b1.size)
        System.arraycopy(o.w2, 0, w2, 0, w2.size); System.arraycopy(o.b2, 0, b2, 0, b2.size)
        System.arraycopy(o.w3, 0, w3, 0, w3.size); System.arraycopy(o.b3, 0, b3, 0, b3.size)
    }

    fun write(dos: DataOutputStream) {
        fun w(a: DoubleArray) { for (v in a) dos.writeDouble(v) }
        w(w1); w(b1); w(w2); w(b2); w(w3); w(b3)
    }
    fun read(dis: DataInputStream) = try {
        fun r(a: DoubleArray) { for (i in a.indices) a[i] = dis.readDouble() }
        r(w1); r(b1); r(w2); r(b2); r(w3); r(b3)
    } catch (t: Throwable) { false }
}

object Features {
    const val SIZE = 21
    fun extract(e: GameEngine): DoubleArray {
        val f = DoubleArray(SIZE)
        val hd = e.head()
        val sim = Sim(e.w, e.h).load(e)
        for (d in 0 until 4) {
            val c = e.nextCell(d)
            f[d] = if (c == null || e.occupied(c.first, c.second)) 1.0 else 0.0
            val a = if (f[d] > 0.5) 0 else {
                val s2 = sim.copy()
                if (s2.stepAuto(d)) s2.flood(s2.head) else 0
            }
            f[4 + d] = (ln(1.0 + a) / 6.0).coerceAtMost(1.0)
        }
        val fx = (e.food.first - hd.first).toDouble() / e.w
        val fy = (e.food.second - hd.second).toDouble() / e.h
        f[8] = fx; f[9] = fy
        val (dx, dy) = GameEngine.DIRS[e.dir]
        f[10] = (fx * dx + fy * dy).coerceIn(-1.0, 1.0)
        f[11] = (fx * -dy + fy * dx).coerceIn(-1.0, 1.0)
        val t = e.tail()
        f[12] = (t.first - hd.first).toDouble() / e.w
        f[13] = (t.second - hd.second).toDouble() / e.h
        f[14] = e.snake.size.toDouble() / (e.w * e.h)
        f[15] = min(1.0, e.stepsSinceFood / 225.0)
        f[16 + e.dir] = 1.0
        var free = 0
        for (y in 0 until e.h) for (x in 0 until e.w) if (!e.occupied(x, y)) free++
        f[20] = free.toDouble() / (e.w * e.h)
        return f
    }
}

class Transition(val f: DoubleArray, val a: Int, val r: Double, val nf: DoubleArray?, val done: Boolean)

class Replay(private val cap: Int = 20000) {
    private val list = ArrayList<Transition>(cap)
    @Synchronized fun add(t: Transition) {
        if (list.size >= cap) list.removeAt(0)
        list.add(t)
    }
    @Synchronized fun sample(k: Int, rnd: Random): List<Transition> {
        if (list.isEmpty()) return emptyList()
        val out = ArrayList<Transition>(k)
        repeat(k) { out.add(list[rnd.nextInt(list.size)]) }
        return out
    }
    @Synchronized fun size() = list.size
}

class AiCore(ctx: Context) {
    companion object {
        const val FEAT = Features.SIZE
        const val GAMMA = 0.95
        const val B_BASE = 0; const val B_SAFEFOOD = 1; const val B_TAIL = 2
        const val B_SPACE = 3; const val B_QLEARN = 4; const val B_HAMILTON = 5
        const val B_ENSEMBLE = 6; const val B_EPS = 7; const val B_MEMORY = 8
        val TECH_NAMES = arrayOf(
            "基础策略", "安全食物", "追尾保命", "空间保底",
            "Q学习改道", "哈密尔顿", "网络集成", "探索随机", "死亡记忆"
        )
    }

    val THREADS = 8
    @Volatile var generation = 0
    @Volatile var bestScore = 0
    @Volatile var eps = 0.25
    @Volatile var activeMask = 0L
    @Volatile var lastBaseBit = B_SAFEFOOD
    val ensemble = Array(3) { Brain(FEAT, 24, 16, 4, seed = 1000L + it * 7919) }
    val genome = Genome()
    val memory = FailureMemory()
    val replay = Replay()
    val deathStats = IntArray(5)
    private val rnd = Random()
    private val learnLock = Any()
    private var learnSteps = 0L
    private val running = AtomicBoolean(false)
    private val threads = ArrayList<Thread>()

    @Volatile var threadScore = IntArray(8)
    @Volatile var threadLen = IntArray(8)
    @Volatile var threadAlive = BooleanArray(8)
    @Volatile var threadGames = IntArray(8)

    @Volatile var genBest = 0
    @Volatile var genAvg = 0f
    @Volatile var genDone = 0
    val genBestHist = IntArray(30)
    val genAvgHist = FloatArray(30)
    @Volatile var genHistIdx = 0
    private val genSum = AtomicLong(0)
    private val genCnt = AtomicInteger(0)

    private val file = File(ctx.filesDir, "snake_ai_v8.dat")

    private fun dirTo(dx: Int, dy: Int): Int = when {
        dy == -1 -> 0; dx == 1 -> 1; dy == 1 -> 2; else -> 3
    }

    private fun mark(bit: Int) { activeMask = activeMask or (1L shl bit) }

    fun meanQ(f: DoubleArray): DoubleArray {
        val out = DoubleArray(4)
        for (b in ensemble) {
            val q = b.forward(f)
            for (a in 0 until 4) out[a] += q[a]
        }
        for (a in 0 until 4) out[a] /= 3.0
        return out
    }

    private fun maxQ(f: DoubleArray): Double {
        val q = meanQ(f)
        return q.max()
    }

    /** ═══ 基础策略：完整移植参考文件底层保命逻辑 ═══ */
    private fun basePolicyDir(e: GameEngine, sim: Sim): Int? {
        val len = e.snake.size
        val total = e.w * e.h
        // 层1：安全食物（含空间余量阈值表）
        if (sim.foodIdx >= 0) {
            val path = sim.shortestPathTo(sim.foodIdx)
            if (path != null && path.isNotEmpty()) {
                val s2 = sim.copy()
                var ok = true
                for (idx in path) {
                    val dx = (idx % e.w) - (s2.head % e.w)
                    val dy = (idx / e.w) - (s2.head / e.w)
                    if (!s2.step(dirTo(dx, dy), idx == sim.foodIdx)) { ok = false; break }
                }
                if (ok) {
                    val afterLen = s2.len
                    val freeLeft = total - afterLen
                    var pass = when {
                        afterLen > 180 -> freeLeft >= 4
                        afterLen > 150 -> freeLeft >= 6
                        afterLen > 120 -> freeLeft >= 10
                        afterLen > 90 -> freeLeft >= 14
                        afterLen > 60 -> freeLeft >= 20
                        else -> freeLeft >= 20
                    }
                    if (pass && afterLen <= 60 && freeLeft >= 20) {
                        pass = s2.flood(s2.head) >= max(4, freeLeft / 3)
                    }
                    if (pass) pass = s2.tailReachSteps(s2.head) >= 0 || s2.flood(s2.head) >= s2.len
                    if (pass) {
                        lastBaseBit = B_SAFEFOOD
                        val f0 = path[0]
                        return dirTo((f0 % e.w) - (sim.head % e.w), (f0 / e.w) - (sim.head / e.w))
                    }
                }
            }
        }
        // 层2：追尾保命
        if (len > 2) {
            val tpath = sim.shortestPathTo(sim.tail)
            if (tpath != null && tpath.isNotEmpty()) {
                val t0 = tpath[0]
                val d = dirTo((t0 % e.w) - (sim.head % e.w), (t0 / e.w) - (sim.head / e.w))
                if (sim.targetOf(d) != null) {
                    val s2 = sim.copy()
                    if (s2.step(d, false) && s2.tailReachSteps(s2.head) >= 0) {
                        lastBaseBit = B_TAIL
                        return d
                    }
                }
            }
        }
        // 层3：最大空间保底
        var bestD = -1; var bestArea = -1
        for (d in 0 until 4) {
            if (len > 1 && (d + 2) % 4 == e.dir) continue
            val s2 = sim.copy()
            if (!s2.stepAuto(d)) continue
            val a = s2.flood(s2.head)
            if (a > bestArea) { bestArea = a; bestD = d }
        }
        if (bestD >= 0) { lastBaseBit = B_SPACE; return bestD }
        return null
    }

    /** 主决策入口（训练与实况共用） */
    fun act(e: GameEngine): Int {
        activeMask = 0L
        mark(B_ENSEMBLE)
        val len = e.snake.size
        val total = e.w * e.h
        val sim = Sim(e.w, e.h).load(e)
        mark(B_BASE)

        // 长蛇直接进入哈密尔顿螺旋（占盘过半）
        if (len > total * 0.55) {
            mark(B_HAMILTON)
            return Hamiltonian.follow(e, strict = true)
        }

        val base = basePolicyDir(e, sim)
        if (base != null) {
            mark(lastBaseBit)
            var d = base
            // 训练期小概率探索
            if (running.get() && rnd.nextDouble() < eps) {
                val alt = (0 until 4).filter {
                    it != (e.dir + 2) % 4 && e.nextCell(it) != null &&
                        !e.occupied(e.nextCell(it)!!.first, e.nextCell(it)!!.second)
                }
                if (alt.isNotEmpty()) { mark(B_EPS); return alt[rnd.nextInt(alt.size)] }
            }
            // 学习网络改道：需过10代 + Q值显著高 + 模拟验证安全
            if (generation >= 10) {
                val f = Features.extract(e)
                val qm = meanQ(f)
                for (a in 0 until 4) {
                    if (a == base || a == (e.dir + 2) % 4 && len > 1) continue
                    if (qm[a] > qm[base] + genome.trust * 4.0) {
                        val s3 = sim.copy()
                        if (s3.stepAuto(a) && s3.flood(s3.head) >= len &&
                            s3.tailReachSteps(s3.head) >= 0
                        ) { d = a; mark(B_QLEARN); break }
                    }
                }
            }
            // 死亡记忆回避
            val nc = e.nextCell(d)
            if (nc != null && memory.danger(nc.first, nc.second, d) > 0.5) {
                for (a in 0 until 4) {
                    if (a == d || a == (e.dir + 2) % 4 && len > 1) continue
                    val c2 = e.nextCell(a) ?: continue
                    if (e.occupied(c2.first, c2.second)) continue
                    val s3 = sim.copy()
                    if (s3.stepAuto(a) && s3.flood(s3.head) >= len &&
                        memory.danger(c2.first, c2.second, a) < 0.3
                    ) { d = a; mark(B_MEMORY); break }
                }
            }
            return d
        }
        // 基础策略无解 → 哈密尔顿兜底
        mark(B_HAMILTON)
        return Hamiltonian.follow(e, len > total * 0.4)
    }

    // ═══ 训练 ═══
    fun startTraining() {
        if (running.get()) return
        running.set(true)
        eps = 0.25
        for (i in 0 until THREADS) {
            val t = Thread({ trainLoop(i) }, "snake-train-$i")
            t.isDaemon = true
            t.start()
            threads.add(t)
        }
    }

    fun stopTraining() {
        running.set(false)
        for (t in threads) try { t.join(1500) } catch (_: Throwable) {}
        threads.clear()
        for (i in 0 until THREADS) threadAlive[i] = false
        save()
    }

    fun isTraining() = running.get()

    private fun trainLoop(id: Int) {
        val e = GameEngine()
        var stepCount = 0L
        while (running.get()) {
            e.reset()
            threadAlive[id] = true; threadScore[id] = 0; threadLen[id] = 3
            var prevF: DoubleArray? = null; var prevA = -1
            while (e.alive && e.totalSteps < 2500 && running.get()) {
                val f = Features.extract(e)
                val d = act(e)
                val res = e.step(d)
                var r = -0.01
                if (res == StepResult.ATE) r += 1.0
                if (!e.alive) r -= 1.0
                val nf = if (e.alive) Features.extract(e) else null
                if (prevF != null && prevA >= 0) {
                    replay.add(Transition(prevF, prevA, r, nf, !e.alive))
                }
                prevF = f; prevA = d
                stepCount++
                if (stepCount % 16 == 0L) learnBatch()
                if (stepCount % 25 == 0L) { threadLen[id] = e.snake.size; threadScore[id] = e.score }
            }
            // 死亡记忆 + 基因调整
            if (!e.alive && e.deathReason != DeathReason.WIN) {
                val h = e.head()
                memory.record(h.first, h.second, e.dir)
            }
            genome.adjust(e.deathReason)
            deathStats[e.deathReason.ordinal]++
            threadAlive[id] = false
            threadScore[id] = e.score
            reportGame(e.score, id)
            if (deathStats.sum() % 40 == 0) save()
        }
    }

    private fun learnBatch() {
        val batch = replay.sample(32, rnd)
        if (batch.isEmpty()) return
        synchronized(learnLock) {
            val net = ensemble[(learnSteps++ % 3).toInt()]
            for (t in batch) {
                val target = if (t.done || t.nf == null) t.r else t.r + GAMMA * maxQ(t.nf)
                net.train(t.f, t.a, target, 0.003)
            }
        }
    }

    private fun reportGame(score: Int, id: Int) {
        threadGames[id]++
        if (score > bestScore) bestScore = score
        genSum.addAndGet(score.toLong())
        val n = genCnt.incrementAndGet()
        genDone = n
        if (score > genBest) genBest = score
        if (n >= THREADS) {
            genAvg = genSum.toFloat() / n
            genBestHist[genHistIdx] = genBest
            genAvgHist[genHistIdx] = genAvg
            genHistIdx = (genHistIdx + 1) % 30
            generation++
            eps = max(0.02, 0.25 * kotlin.math.exp(-generation / 20.0))
            genBest = 0
            genSum.set(0); genCnt.set(0)
            if (generation % 10 == 0) save()
        }
    }

    // ═══ 存档：续跑不重头 ═══
    fun save() {
        try {
            DataOutputStream(FileOutputStream(file)).use { dos ->
                dos.writeInt(generation)
                dos.writeInt(bestScore)
                genome.write(dos)
                memory.write(dos)
                dos.writeInt(deathStats.size)
                for (v in deathStats) dos.writeInt(v)
                for (b in ensemble) b.write(dos)
            }
        } catch (t: Throwable) { Log.w("SnakeAI", "save", t) }
    }

    fun load() {
        if (!file.exists()) return
        try {
            DataInputStream(FileInputStream(file)).use { dis ->
                generation = dis.readInt()
                bestScore = dis.readInt()
                genome.read(dis)
                memory.read(dis)
                val n = dis.readInt()
                for (i in 0 until n) deathStats[i] = dis.readInt()
                for (b in ensemble) b.read(dis)
            }
        } catch (t: Throwable) {
            Log.w("SnakeAI", "load", t)
        }
    }
}

class SnakeView @JvmOverloads constructor(
    context: Context, attrs: AttributeSet? = null
) : View(context, attrs) {

    private val engine = GameEngine()
    private val ai = AiCore(context)
    private var manualDir = 1
    private var lastStep = 0L
    private var restartAt = 0L
    private var touchX = 0f; private var touchY = 0f
    private val trainBtn = RectF()

    private val p = Paint(Paint.ANTI_ALIAS_FLAG)
    private val line = Paint(Paint.ANTI_ALIAS_FLAG)
    private val prefs = context.getSharedPreferences("snake_prefs", Context.MODE_PRIVATE)
    private var highScore = prefs.getInt("high_score", 0)

    private fun dp(v: Float) = v * resources.displayMetrics.density

    private val frame = object : Choreographer.FrameCallback {
        override fun doFrame(ns: Long) {
            if (lastStep == 0L) lastStep = ns
            val dt = ns - lastStep
            lastStep = ns
            if (!ai.isTraining()) {
                if (engine.alive && dt >= 130L) {
                    lastStep = ns
                    engine.step(ai.act(engine))
                    if (engine.score > highScore) {
                        highScore = engine.score
                        prefs.edit().putInt("high_score", highScore).apply()
                    }
                }
                if (!engine.alive) {
                    if (restartAt == 0L) restartAt = ns + 2_000_000_000L
                    else if (ns > restartAt) { engine.reset(); restartAt = 0L }
                }
            }
            invalidate()
            Choreographer.getInstance().postFrameCallback(this)
        }
    }

    init {
        ai.load()
        engine.reset()
    }

    override fun onAttachedToWindow() {
        super.onAttachedToWindow()
        Choreographer.getInstance().postFrameCallback(frame)
    }

    override fun onDetachedFromWindow() {
        super.onDetachedFromWindow()
        Choreographer.getInstance().removeFrameCallback(frame)
        ai.stopTraining()
        ai.save()
    }

    // ═══ 绘制 ═══
    override fun onDraw(c: Canvas) {
        super.onDraw(c)
        if (ai.isTraining()) { drawTrainingHud(c); drawTrainButton(c, true) }
        else { drawGame(c); drawTrainButton(c, false) }
    }

    private fun drawGame(c: Canvas) {
        c.drawColor(Color.BLACK)
        val cell = min(width, height * 0.7f) / 15f
        val ox = (width - cell * 15) / 2f
        val oy = dp(30f)
        // 网格
        line.style = Paint.Style.STROKE; line.strokeWidth = 1f; line.color = Color.rgb(40, 40, 45)
        for (i in 0..15) {
            c.drawLine(ox + i * cell, oy, ox + i * cell, oy + 15 * cell, line)
            c.drawLine(ox, oy + i * cell, ox + 15 * cell, oy + i * cell, line)
        }
        // 食物
        p.color = Color.RED
        c.drawCircle(ox + (engine.food.first + 0.5f) * cell, oy + (engine.food.second + 0.5f) * cell, cell * 0.28f, p)
        // 蛇
        val list = engine.snake.toList()
        line.style = Paint.Style.STROKE; line.strokeWidth = cell * 0.6f
        line.strokeCap = Paint.Cap.ROUND
        for (i in 0 until list.size - 1) {
            line.color = if (i == 0) Color.rgb(39, 174, 96) else Color.rgb(46, 204, 113)
            c.drawLine(ox + (list[i].first + 0.5f) * cell, oy + (list[i].second + 0.5f) * cell,
                ox + (list[i + 1].first + 0.5f) * cell, oy + (list[i + 1].second + 0.5f) * cell, line)
        }
        // 顶栏
        p.textAlign = Paint.Align.LEFT; p.textSize = dp(16f); p.color = Color.WHITE
        c.drawText("分数 ${engine.score}  最高 $highScore  长 ${engine.snake.size}", dp(12f), dp(22f), p)
        if (!engine.alive) {
            p.textAlign = Paint.Align.CENTER; p.textSize = dp(22f); p.color = Color.RED
            c.drawText("GAME OVER · ${engine.deathReason}", width / 2f, height / 2f, p)
            p.textSize = dp(13f); p.color = Color.LTGRAY
            c.drawText("点击屏幕重新开始", width / 2f, height / 2f + dp(26f), p)
        }
    }

    private fun drawTrainButton(c: Canvas, training: Boolean) {
        val w = dp(150f); val h = dp(44f)
        trainBtn.set(width - w - dp(14f), height - h - dp(20f), width - dp(14f), height - dp(20f))
        p.style = Paint.Style.FILL
        p.color = if (training) Color.rgb(231, 76, 60) else Color.rgb(46, 204, 113)
        c.drawRoundRect(trainBtn, dp(12f), dp(12f), p)
        p.textAlign = Paint.Align.CENTER; p.textSize = dp(15f); p.isFakeBoldText = true
        p.color = Color.WHITE
        c.drawText(if (training) "⏹ 停止训练" else "▶ 开始训练", trainBtn.centerX(), trainBtn.centerY() + dp(5f), p)
        p.isFakeBoldText = false
    }

    private fun drawTrainingHud(c: Canvas) {
        c.drawColor(Color.rgb(12, 12, 16))
        val cx = width / 2f
        // ═══ 顶部：世代圆环 ═══
        val cy = dp(56f); val ringR = dp(38f)
        val ring = Paint(Paint.ANTI_ALIAS_FLAG).apply { style = Paint.Style.STROKE; strokeWidth = dp(6f) }
        ring.color = Color.rgb(40, 40, 48)
        c.drawCircle(cx, cy, ringR, ring)
        ring.color = Color.rgb(80, 255, 150)
        c.drawArc(cx - ringR, cy - ringR, cx + ringR, cy + ringR, -90f, ai.genDone / 8f * 360f, false, ring)
        p.textAlign = Paint.Align.CENTER
        p.color = Color.WHITE; p.textSize = dp(22f); p.isFakeBoldText = true
        c.drawText("${ai.generation}", cx, cy + dp(2f), p)
        p.color = Color.LTGRAY; p.textSize = dp(9f); p.isFakeBoldText = false
        c.drawText("世代 GEN", cx, cy + dp(15f), p)
        p.textAlign = Paint.Align.LEFT
        p.textSize = dp(15f); c.drawText("🏆", dp(14f), cy - dp(2f), p)
        p.color = Color.rgb(255, 215, 80); p.textSize = dp(17f); p.isFakeBoldText = true
        c.drawText("${ai.bestScore}", dp(36f), cy, p)
        p.color = Color.GRAY; p.textSize = dp(9f); p.isFakeBoldText = false
        c.drawText("历史最高", dp(14f), cy + dp(14f), p)
        p.textAlign = Paint.Align.RIGHT
        p.textSize = dp(15f); c.drawText("🐍", width - dp(14f), cy - dp(2f), p)
        p.color = Color.rgb(120, 255, 180); p.textSize = dp(17f); p.isFakeBoldText = true
        c.drawText("${"%.1f".format(ai.genAvg)}", width - dp(36f), cy, p)
        p.color = Color.GRAY; p.textSize = dp(9f); p.isFakeBoldText = false
        c.drawText("本代平均", width - dp(14f), cy + dp(14f), p)

        // ═══ 8蛇卡片 ═══
        val icons = arrayOf("🟢", "🔵", "🟡", "🟣", "🟠", "🔴", "⚪", "🩵")
        val cardW = (width - dp(36f)) / 2f; val cardH = dp(38f)
        val startY = cy + ringR + dp(14f)
        for (i in 0 until 8) {
            val col = i % 2; val row = i / 2
            val x = dp(12f) + col * (cardW + dp(12f))
            val y = startY + row * (cardH + dp(7f))
            val alive = ai.threadAlive[i]
            p.style = Paint.Style.FILL
            p.color = if (alive) Color.argb(50, 40, 120, 70) else Color.argb(50, 60, 60, 65)
            c.drawRoundRect(x, y, x + cardW, y + cardH, dp(9f), dp(9f), p)
            line.style = Paint.Style.STROKE; line.strokeWidth = dp(1.2f)
            line.color = if (alive) Color.rgb(80, 255, 150) else Color.rgb(80, 80, 85)
            c.drawRoundRect(x, y, x + cardW, y + cardH, dp(9f), dp(9f), line)
            p.textAlign = Paint.Align.LEFT
            p.textSize = dp(13f)
            p.color = if (alive) Color.WHITE else Color.GRAY
            c.drawText(icons[i], x + dp(8f), y + dp(15f), p)
            p.color = if (alive) Color.rgb(80, 255, 150) else Color.rgb(100, 100, 105)
            c.drawCircle(x + dp(27f), y + dp(10f), dp(3.2f), p)
            p.textSize = dp(11f)
            p.color = if (alive) Color.WHITE else Color.GRAY
            c.drawText("长${ai.threadLen[i]} 分${ai.threadScore[i]}", x + dp(36f), y + dp(15f), p)
            p.textAlign = Paint.Align.RIGHT; p.textSize = dp(9f); p.color = Color.GRAY
            c.drawText("第${ai.threadGames[i] + 1}局", x + cardW - dp(8f), y + dp(15f), p)
            val ratio = (ai.threadLen[i].toFloat() / 225f).coerceIn(0f, 1f)
            p.style = Paint.Style.FILL; p.color = Color.rgb(35, 35, 42)
            c.drawRoundRect(x + dp(8f), y + dp(23f), x + cardW - dp(8f), y + dp(29f), dp(3f), dp(3f), p)
            p.color = if (alive) Color.rgb(255, 170, 60) else Color.rgb(110, 110, 115)
            if (ratio > 0.01f) c.drawRoundRect(x + dp(8f), y + dp(23f),
                x + dp(8f) + (cardW - dp(16f)) * ratio, y + dp(29f), dp(3f), dp(3f), p)
        }

        // ═══ 本代统计 ═══
        val sy = startY + 4 * (cardH + dp(7f)) + dp(4f)
        p.textAlign = Paint.Align.CENTER; p.textSize = dp(12f)
        p.color = Color.rgb(255, 200, 100)
        c.drawText("📊 本代最高 ${ai.genBest}  平均 ${"%.1f".format(ai.genAvg)}  完成 ${ai.genDone}/8", cx, sy, p)

        // ═══ 趋势图 ═══
        val gx = dp(12f); val gy = sy + dp(8f)
        val gw = width - dp(24f); val gh = dp(58f)
        p.color = Color.rgb(22, 22, 28)
        c.drawRoundRect(gx, gy, gx + gw, gy + gh, dp(8f), dp(8f), p)
        var maxV = 1
        for (v in ai.genBestHist) if (v > maxV) maxV = v
        val stepX = gw / 29f
        line.style = Paint.Style.STROKE; line.strokeWidth = dp(1f); line.color = Color.rgb(50, 50, 58)
        c.drawLine(gx, gy + gh * 0.5f, gx + gw, gy + gh * 0.5f, line)
        line.strokeWidth = dp(1.8f)
        line.color = Color.rgb(255, 90, 90)
        var prevX = 0f; var prevY = 0f
        for (i in 0 until 30) {
            val v = ai.genBestHist[(ai.genHistIdx + i) % 30]
            val x = gx + i * stepX
            val y = gy + gh - gh * v / maxV
            if (i > 0) c.drawLine(prevX, prevY, x, y, line)
            if (v > 0) { p.color = Color.rgb(255, 90, 90); c.drawCircle(x, y, dp(1.6f), p) }
            prevX = x; prevY = y
        }
        line.color = Color.rgb(80, 255, 150)
        prevX = 0f; prevY = 0f
        for (i in 0 until 30) {
            val v = ai.genAvgHist[(ai.genHistIdx + i) % 30]
            val x = gx + i * stepX
            val y = gy + gh - gh * v / maxV
            if (i > 0) c.drawLine(prevX, prevY, x, y, line)
            prevX = x; prevY = y
        }
        p.textSize = dp(9f); p.textAlign = Paint.Align.LEFT
        p.color = Color.rgb(255, 90, 90); c.drawText("— 最高", gx + dp(5f), gy + dp(11f), p)
        p.color = Color.rgb(80, 255, 150); c.drawText("— 平均", gx + dp(48f), gy + dp(11f), p)
        p.color = Color.GRAY; p.textAlign = Paint.Align.RIGHT
        c.drawText("峰值$maxV", gx + gw - dp(5f), gy + dp(11f), p)

        // ═══ 策略亮灯 ═══
        val ty = gy + gh + dp(12f)
        p.style = Paint.Style.FILL
        val panelH = 5 * dp(20f) + dp(22f)
        p.color = Color.argb(120, 20, 20, 26)
        c.drawRoundRect(dp(8f), ty, width - dp(8f), ty + panelH, dp(10f), dp(10f), p)
        p.textAlign = Paint.Align.LEFT; p.textSize = dp(11f); p.isFakeBoldText = true
        p.color = Color.rgb(200, 180, 255)
        c.drawText("🧠 策略雷达 — 亮=在用", dp(16f), ty + dp(14f), p)
        p.isFakeBoldText = false
        val colW = (width - dp(32f)) / 2f
        for (i in ai.TECH_NAMES.indices) {
            val col = i % 2; val row = i / 2
            val x = dp(16f) + col * colW
            val y = ty + dp(30f) + row * dp(20f)
            val on = (ai.activeMask shr i) and 1L == 1L
            p.color = if (on) Color.rgb(80, 255, 150) else Color.rgb(70, 70, 75)
            c.drawCircle(x + dp(4f), y - dp(3f), dp(4f), p)
            if (on) { p.color = Color.argb(60, 80, 255, 150); c.drawCircle(x + dp(4f), y - dp(3f), dp(7.5f), p) }
            p.color = if (on) Color.WHITE else Color.rgb(110, 110, 115)
            p.textSize = dp(11f); p.textAlign = Paint.Align.LEFT
            c.drawText(ai.TECH_NAMES[i], x + dp(14f), y, p)
        }

        // ═══ 底部：死亡饼图 + 基因柱状图 ═══
        val by = ty + panelH + dp(10f)
        // 饼图
        val pieR = dp(30f); val pieCX = dp(46f); val pieCY = by + pieR + dp(4f)
        val pieColors = arrayOf(
            Color.rgb(255, 100, 100), Color.rgb(100, 150, 255),
            Color.rgb(255, 200, 100), Color.rgb(160, 100, 255), Color.rgb(100, 255, 150)
        )
        val totalD = ai.deathStats.sum()
        if (totalD == 0) { p.color = Color.rgb(60, 60, 60); c.drawCircle(pieCX, pieCY, pieR, p) }
        else {
            val oval = RectF(pieCX - pieR, pieCY - pieR, pieCX + pieR, pieCY + pieR)
            var start = -90f
            for (i in 0 until 5) {
                val sweep = 360f * ai.deathStats[i] / totalD
                if (sweep > 0f) { p.color = pieColors[i]; c.drawArc(oval, start, sweep, true, p); start += sweep }
            }
        }
        p.textAlign = Paint.Align.LEFT; p.textSize = dp(9f)
        val pieNames = arrayOf("墙", "己", "困", "饿", "胜")
        for (i in 0 until 5) {
            p.color = pieColors[i]
            c.drawText("${pieNames[i]}${ai.deathStats[i]}", dp(84f), by + dp(10f) + i * dp(12f), p)
        }
        // 基因柱状图
        val barX = width * 0.42f; val barW = width * 0.5f
        p.textSize = dp(9f); p.color = Color.rgb(255, 200, 100)
        c.drawText("🧬 基因参数", barX, by + dp(2f), p)
        val params = ai.genome.params()
        for (i in params.indices) {
            val y = by + dp(12f) + i * dp(12f)
            p.textAlign = Paint.Align.LEFT; p.color = Color.LTGRAY; p.textSize = dp(8f)
            c.drawText(params[i].first, barX, y + dp(7f), p)
            p.color = Color.rgb(45, 45, 52)
            c.drawRoundRect(barX + dp(44f), y, barX + barW, y + dp(7f), dp(2f), dp(2f), p)
            p.color = Color.rgb(120, 255, 180)
            val r = (params[i].second / params[i].third).coerceIn(0f..1f.toDouble()).toFloat()
            if (r > 0.01f) c.drawRoundRect(barX + dp(44f), y, barX + dp(44f) + (barW - dp(44f)) * r, y + dp(7f), dp(2f), dp(2f), p)
        }
    }

    // ═══ 触摸 ═══
    override fun onTouchEvent(e: MotionEvent): Boolean {
        when (e.action) {
            MotionEvent.ACTION_DOWN -> { touchX = e.x; touchY = e.y; return true }
            MotionEvent.ACTION_UP -> {
                if (trainBtn.contains(e.x, e.y)) {
                    if (ai.isTraining()) ai.stopTraining() else ai.startTraining()
                    return true
                }
                if (!ai.isTraining()) {
                    if (!engine.alive) { engine.reset(); return true }
                    val dx = e.x - touchX; val dy = e.y - touchY
                    if (abs(dx) > 24f || abs(dy) > 24f) {
                        val d = if (abs(dx) > abs(dy)) (if (dx > 0) 1 else 3) else (if (dy > 0) 2 else 0)
                        if (engine.snake.size <= 1 || (d + 2) % 4 != engine.dir) manualDir = d
                    }
                }
                return true
            }
        }
        return true
    }
}
