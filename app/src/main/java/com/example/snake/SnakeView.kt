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
import java.util.concurrent.atomic.AtomicBoolean
import kotlin.math.abs
import kotlin.math.max
import kotlin.math.min
import kotlin.math.sin
import kotlin.math.sqrt

/* ============================================================================
 * SNAKE PRO v4 — 35项AI技术 + 商店皮肤/棋盘 + MainActivity 完整对接
 * ==========================================================================*/

// ═══════════════════ 引擎 ═══════════════════

enum class StepResult { MOVED, ATE, DIED }
enum class DeathReason { WALL, SELF, TRAPPED, STARVED, WIN }
enum class Goal { FOOD, TAIL, SPACE, SEARCH, SPIRAL, LEARN, NONE }

class GameEngine(val w: Int = 15, val h: Int = 15) {
    companion object {
        val DIRS = arrayOf(0 to -1, 1 to 0, 0 to 1, -1 to 0)

        fun dirBetween(a: Int, b: Int, w: Int): Int {
            if (b == a - w) return 0
            if (b == a + 1) return 1
            if (b == a + w) return 2
            return 3
        }
    }

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
    fun distToFood(x: Int, y: Int) = abs(x - food.first) + abs(y - food.second)

    fun cloneState(): GameEngine {
        val e = GameEngine(w, h)
        e.snake.addAll(snake); e.food = food; e.dir = dir; e.score = score
        e.stepsSinceFood = stepsSinceFood; e.totalSteps = totalSteps
        e.alive = alive; e.deathReason = deathReason
        return e
    }
}

// ═══════════════════ 沙盒仿真 ═══════════════════

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

    fun regionStats(start: Int): Triple<Int, Int, Int> {
        var area = 0; var dead = 0; var perim = 0
        val seen = BooleanArray(n)
        val q = ArrayDeque<Int>()
        seen[start] = true; q.addLast(start)
        val buf = IntArray(4)
        while (q.isNotEmpty()) {
            val cur = q.removeFirst(); area++
            val m = neighbors(cur, buf)
            var freeDeg = 0
            for (i in 0 until m) {
                if (free(buf[i])) freeDeg++
                else perim++
            }
            if (freeDeg <= 1) dead++
        }
        return Triple(area, dead, perim)
    }

    fun distField(from: Int): IntArray {
        val d = IntArray(n) { -1 }
        val q = ArrayDeque<Int>()
        d[from] = 0; q.addLast(from)
        val buf = IntArray(4)
        while (q.isNotEmpty()) {
            val cur = q.removeFirst()
            val m = neighbors(cur, buf)
            for (i in 0 until m) { val nx = buf[i]; if (d[nx] < 0 && free(nx)) { d[nx] = d[cur] + 1; q.add(nx) } }
        }
        return d
    }

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

    fun articulation(): Pair<BooleanArray, IntArray> {
        val disc = IntArray(n) { -1 }; val low = IntArray(n)
        val art = BooleanArray(n); val maxComp = IntArray(n)
        var timer = 0
        val buf = IntArray(4)
        fun dfs(u: Int, parent: Int): Unit {
            disc[u] = timer
            low[u] = timer
            timer++
            var children = 0
            val m = neighbors(u, buf)
            for (i in 0 until m) {
                val v = buf[i]
                if (!free(v) || v == parent) continue
                if (disc[v] == -1) {
                    children++
                    dfs(v, u)
                    low[u] = min(low[u], low[v])
                    if (parent != -1 && low[v] >= disc[u]) art[u] = true
                } else low[u] = min(low[u], disc[v])
            }
            if (parent == -1 && children > 1) art[u] = true
        }
        for (i in 0 until n) if (free(i) && disc[i] == -1) dfs(i, -1)
        for (i in 0 until n) {
            if (!art[i]) continue
            val seen = BooleanArray(n)
            var best = 0
            val m = neighbors(i, buf)
            for (k in 0 until m) {
                val v = buf[k]
                if (free(v) && !seen[v]) {
                    var c = 0
                    val q = ArrayDeque<Int>(); seen[v] = true; q.add(v)
                    while (q.isNotEmpty()) {
                        val cur = q.removeFirst(); c++
                        val mm = neighbors(cur, buf)
                        for (j in 0 until mm) { val nx = buf[j]; if (!seen[nx] && free(nx) && nx != i) { seen[nx] = true; q.add(nx) } }
                    }
                    best = max(best, c)
                }
            }
            maxComp[i] = best
        }
        return art to maxComp
    }
}

// ═══════════════════ 扰动哈密顿 ═══════════════════

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
        var bestD = -1
        var bestGain = Int.MAX_VALUE
        for (d in 0 until 4) {
            if (e.snake.size > 1 && (d + 2) % 4 == e.dir) continue
            val c = e.nextCell(d) ?: continue
            if (e.occupied(c.first, c.second)) continue
            val ci = c.second * e.w + c.first
            val gain = (order[ci] - hi + N) % N
            var ok = false
            if (strict) {
                ok = gain == 1
            } else {
                var allFree = true
                var k = 1
                while (k < gain && allFree) {
                    val mid = cells[(hi + k) % N]
                    if (e.occupied(mid % e.w, mid / e.w)) allFree = false
                    k++
                }
                ok = gain >= 1 && gain <= min(N - 1, 40) && allFree
            }
            if (ok && gain < bestGain) {
                bestGain = gain
                bestD = d
            }
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

// ═══════════════════ Beam Search ═══════════════════

object BeamSearch {
    private class BNode(val sim: Sim, val first: Int, val lastDir: Int, val score: Double)

    fun search(root: Sim, rootDir: Int, deadlineNanos: Long, budgetOps: Int, width: Int, depth: Int): DoubleArray {
        val sum = DoubleArray(4); val cnt = IntArray(4)
        var ops = 0
        var beam = ArrayList<BNode>()
        for (d in 0 until 4) {
            if (d == (rootDir + 2) % 4 && root.len > 1) continue
            val s = root.copy()
            val bf = s.foodIdx
            if (!s.stepAuto(d)) continue
            val ate = bf >= 0 && s.foodIdx == -1
            val area = s.flood(s.head)
            beam.add(BNode(s, d, d, (if (ate) 12.0 else 0.0) + area * 0.08 + s.len * 0.2))
        }
        var dep = 1
        val result = DoubleArray(4)
        for (b in beam) { sum[b.first] += b.score; cnt[b.first]++ }
        while (beam.isNotEmpty() && dep < depth && ops < budgetOps) {
            if ((ops and 15) == 0 && System.nanoTime() > deadlineNanos) break
            val next = ArrayList<BNode>()
            for (node in beam) {
                for (d in 0 until 4) {
                    if (d == (node.lastDir + 2) % 4 && node.sim.len > 1) continue
                    ops++
                    if (ops >= budgetOps + width * 4) break
                    val s = node.sim.copy()
                    val bf = s.foodIdx
                    if (!s.stepAuto(d)) continue
                    val ate = bf >= 0 && s.foodIdx == -1
                    val area = s.flood(s.head)
                    var sc = node.score + (if (ate) 14.0 else 0.0) + area * 0.07
                    if (area < s.len) sc -= 30.0
                    else if (area < s.len + 4) sc -= 6.0
                    next.add(BNode(s, node.first, d, sc))
                }
            }
            if (next.isEmpty()) break
            next.sortByDescending { it.score }
            beam = ArrayList(next.take(width))
            for (d in 0 until 4) { sum[d] = 0.0; cnt[d] = 0 }
            for (b in beam) { sum[b.first] += b.score; cnt[b.first]++ }
            dep++
        }
        for (d in 0 until 4) if (cnt[d] > 0) result[d] = sum[d] / cnt[d]
        return result
    }
}

// ═══════════════════ MCTS ═══════════════════

object Mcts {
    private class MN(val sim: Sim, val parent: MN?, val action: Int, val first: Int, val lastDir: Int, val dead: Boolean) {
        var visits = 0; var value = 0.0; var sqSum = 0.0
        val children = ArrayList<MN>()
        val untried = ArrayList<Int>()
    }

    private fun rollout(s0: Sim, firstDir: Int, maxSteps: Int, rnd: Random): Double {
        val s = s0.copy()
        var steps = 0; var foods = 0
        val buf = IntArray(4)
        while (steps < maxSteps) {
            var bestD = -1; var bestScore = Double.NEGATIVE_INFINITY
            for (d in 0 until 4) {
                if (steps == 0 && d == (firstDir + 2) % 4 && s.len > 1) continue
                val t = s.targetOf(d) ?: continue
                if (s.occ[t] && t != s.tail) continue
                var sc = rnd.nextDouble() * 0.3
                if (s.foodIdx >= 0) {
                    val fd = abs(t % s.w - s.foodIdx % s.w) + abs(t / s.w - s.foodIdx / s.w)
                    sc += (s.w + s.h - fd) * 0.35
                }
                val m = s.neighbors(t, buf)
                var fc = 0
                for (i in 0 until m) if (!s.occ[buf[i]] || buf[i] == s.tail) fc++
                sc += fc * 0.5
                if (sc > bestScore) { bestScore = sc; bestD = d }
            }
            if (bestD < 0) break
            if (!s.stepAuto(bestD)) break
            if (s.foodIdx == -1) { foods++; s.foodIdx = -2 }
            steps++
        }
        return foods * 10.0 + steps * 0.06 - (if (steps < maxSteps) 10.0 else 0.0)
    }

    fun search(root: Sim, rootDir: Int, deadlineNanos: Long, budget: Int, qPrior: DoubleArray, rnd: Random): DoubleArray {
        val rootNode = MN(root.copy(), null, -1, -1, rootDir, false)
        for (d in 0 until 4) if (!(d == (rootDir + 2) % 4 && root.len > 1)) rootNode.untried.add(d)
        var ops = 0
        while (ops < budget) {
            if ((ops and 7) == 0 && System.nanoTime() > deadlineNanos) break
            var node = rootNode
            while (node.untried.isEmpty() && node.children.isNotEmpty()) {
                val lnN = kotlin.math.ln((node.visits + 1).toDouble())
                node = node.children.maxByOrNull { c ->
                    if (c.visits == 0) Double.MAX_VALUE / 2
                    else {
                        val v = c.value / c.visits
                        val varr = (c.sqSum / c.visits) - v * v
                        val tuned = v + 1.4 * sqrt(min(0.25, varr + sqrt(2.0 * lnN / c.visits)) * lnN / c.visits)
                        tuned + qPrior[c.first] * 0.25
                    }
                }!!
            }
            if (node.dead) {
                var cur: MN? = node
                while (cur != null) { cur.visits++; cur.value += -10.0; cur.sqSum += 100.0; cur = cur.parent }
                ops += 2; continue
            }
            var child: MN
            if (node.untried.isNotEmpty()) {
                val a = node.untried.removeAt(rnd.nextInt(node.untried.size))
                val s = node.sim.copy()
                val ok = s.stepAuto(a)
                child = MN(s, node, a, if (node === rootNode) a else node.first, a, !ok)
                node.children.add(child)
            } else child = node
            ops++
            val v = if (child.dead) -10.0 else rollout(child.sim, child.lastDir, 20, rnd)
            var cur: MN? = child
            while (cur != null) {
                cur.visits++; cur.value += v; cur.sqSum += v * v
                cur = cur.parent
            }
        }
        val out = DoubleArray(4)
        for (c in rootNode.children) if (c.visits > 0) out[c.first] = c.value / c.visits
        return out
    }
}

// ═══════════════════ 特征 ═══════════════════

object Features {
    const val SIZE = 36

    fun extract(e: GameEngine, dir: Int): DoubleArray {
        val f = DoubleArray(SIZE)
        val hd = e.head()
        val sim = Sim(e.w, e.h).load(e)
        var i = 0
        for (d in 0 until 4) {
            val c = e.nextCell(d)
            f[i++] = if (c == null || e.occupied(c.first, c.second)) 1.0 else 0.0
        }
        for (d in 0 until 4) {
            val c = e.nextCell(d)
            val a = if (c == null || e.occupied(c.first, c.second)) 0
            else { val s2 = sim.copy(); if (s2.step(d, false)) s2.flood(s2.head) else 0 }
            f[i++] = (kotlin.math.ln(1.0 + a) / 8.0).coerceAtMost(1.0)
        }
        val fx = (e.food.first - hd.first).toDouble() / e.w
        val fy = (e.food.second - hd.second).toDouble() / e.h
        f[i++] = fx; f[i++] = fy
        val (dx, dy) = GameEngine.DIRS[dir]
        f[i++] = (fx * dx + fy * dy).coerceIn(-1.0, 1.0)
        f[i++] = (fx * -dy + fy * dx).coerceIn(-1.0, 1.0)
        val t = e.tail()
        f[i++] = (t.first - hd.first).toDouble() / e.w
        f[i++] = (t.second - hd.second).toDouble() / e.h
        f[i++] = e.snake.size.toDouble() / (e.w * e.h)
        f[i++] = min(1.0, e.stepsSinceFood / 200.0)
        f[16 + dir] = 1.0; i = 20
        for (oy in -1..1) for (ox in -1..1) {
            if (ox == 0 && oy == 0) continue
            val x = hd.first + ox; val y = hd.second + oy
            f[i++] = if (x < 0 || y < 0 || x >= e.w || y >= e.h || e.occupied(x, y)) 1.0 else 0.0
        }
        f[i++] = 1.0
        var free = 0
        for (y in 0 until e.h) for (x in 0 until e.w) if (!e.occupied(x, y)) free++
        f[i++] = free.toDouble() / (e.w * e.h)
        for (d in 0 until 4) {
            val c = e.nextCell(d)
            f[i++] = if (c == null) 1.0 else e.distToFood(c.first, c.second).toDouble() / (e.w + e.h)
        }
        f[i++] = if (e.food.first == hd.first || e.food.second == hd.second) 1.0 else 0.0
        f[i] = min(1.0, e.score / 50.0)
        return f
    }
}

// ═══════════════════ 记忆系统 ═══════════════════

class LoopDetector(private val cap: Int = 48) {
    private val recent = ArrayDeque<Int>()
    private val count = HashMap<Int, Int>()
    private val dirHist = ArrayDeque<Int>()

    fun record(e: GameEngine) {
        val h = e.head(); val k = h.second * 256 + h.first
        recent.addLast(k); count[k] = (count[k] ?: 0) + 1
        if (recent.size > cap) {
            val old = recent.removeFirst()
            count[old]?.let { if (it <= 1) count.remove(old) else count[old] = it - 1 }
        }
        dirHist.addLast(e.dir)
        if (dirHist.size > 8) dirHist.removeFirst()
    }

    fun cellPenalty(x: Int, y: Int) = min(1.0, (count[y * 256 + x] ?: 0) / 3.0)

    fun oscillationPenalty(): Double {
        if (dirHist.size < 4) return 0.0
        val d0 = dirHist.elementAt(dirHist.size - 1)
        val d1 = dirHist.elementAt(dirHist.size - 2)
        val d2 = dirHist.elementAt(dirHist.size - 3)
        val d3 = dirHist.elementAt(dirHist.size - 4)
        return if (d0 == d2 && d1 == d3 && d0 != d1) 1.0 else 0.0
    }

    fun reset() { recent.clear(); count.clear(); dirHist.clear() }
}

class FailureMemory(private val cap: Int = 8000) {
    private val map = HashMap<Int, Int>()
    private val lru = ArrayDeque<Int>()
    fun record(x: Int, y: Int, dir: Int) {
        val k = ((y * 256 + x) * 5 + dir).toInt()
        map[k] = (map[k] ?: 0) + 1
        lru.addLast(k)
        if (lru.size > cap) {
            val old = lru.removeFirst()
            map[old]?.let { if (it <= 1) map.remove(old) else map[old] = it - 1 }
        }
    }
    fun danger(x: Int, y: Int, dir: Int) = min(1.0, (map[((y * 256 + x) * 5 + dir).toInt()] ?: 0) / 5.0)
    fun size() = map.size
    fun write(dos: DataOutputStream) {
        val top = map.entries.sortedByDescending { it.value }.take(2000)
        dos.writeInt(top.size)
        for ((k, v) in top) { dos.writeInt(k); dos.writeInt(v) }
    }
    fun read(dis: DataInputStream) = try {
        val n = dis.readInt().coerceIn(0, 100000)
        repeat(n) {
            val k = dis.readInt(); val v = dis.readInt()
            if (v > 0) { map[k] = v; repeat(min(3, v)) { lru.addLast(k) } }
        }
    } catch (t: Throwable) { Log.w("SnakeAI", "mem read fail", t) }
}

class CausalHistory(private val cap: Int = 32) {
    class Step(val x: Int, val y: Int, val dir: Int)
    private val ring = ArrayDeque<Step>()
    fun record(e: GameEngine) {
        val h = e.head()
        ring.addLast(Step(h.first, h.second, e.dir))
        if (ring.size > cap) ring.removeFirst()
    }
    fun onDeath(cb: (Step, Double) -> Unit) {
        var w = 1.0
        for (i in ring.indices) {
            cb(ring.elementAt(ring.size - 1 - i), w)
            w *= 0.85
        }
    }
    fun reset() = ring.clear()
}

// ═══════════════════ 基因性格 ═══════════════════

class Genome {
    var margin = 4.0; var tailBias = 1.0; var wanderlust = 1.0
    var risk = 0.4; var trust = 0.3; var shortcut = 2.5
    var patience = 0.45; var lambda = 0.8; var regretSens = 0.6; var rate = 0.05

    private fun vec() = doubleArrayOf(margin, tailBias, wanderlust, risk, trust, shortcut, patience, lambda, regretSens, rate)
    private fun load(v: DoubleArray) {
        margin = v[0].coerceIn(0.0, 20.0); tailBias = v[1].coerceIn(0.0, 5.0)
        wanderlust = v[2].coerceIn(0.0, 5.0); risk = v[3].coerceIn(0.05, 1.0)
        trust = v[4].coerceIn(0.0, 1.0); shortcut = v[5].coerceIn(1.0, 6.0)
        patience = v[6].coerceIn(0.1, 0.9); lambda = v[7].coerceIn(0.0, 2.0)
        regretSens = v[8].coerceIn(0.0, 2.0); rate = v[9].coerceIn(0.01, 0.15)
    }

    fun personality(): String {
        if (margin > 8 && tailBias > 1.5) return "稳健守成型"
        if (risk > 0.6 && patience < 0.35) return "激进捕食型"
        if (lambda > 1.2) return "风险厌恶型"
        if (wanderlust > 2.0) return "游走探索型"
        if (shortcut > 3.5) return "路径贪婪型"
        return "均衡型"
    }

    fun adjust(r: DeathReason) {
        val a = rate
        when (r) {
            DeathReason.TRAPPED -> { margin += a * 4; tailBias += a * 2; lambda += a }
            DeathReason.STARVED -> { risk += a; patience -= a; wanderlust += a }
            DeathReason.WALL, DeathReason.SELF -> { margin += a * 2 }
            DeathReason.WIN -> { margin -= a * 2 }
        }
        load(vec())
    }

    fun copy() = Genome().also { it.load(vec()) }
    fun copyFrom(o: Genome) = load(o.vec())
    fun mutate(rnd: Random) {
        val v = vec()
        for (i in v.indices) if (rnd.nextDouble() < .2) v[i] += rnd.nextGaussian() * (v[i] * .15 + .05)
        load(v)
    }

    companion object {
        fun cross(a: Genome, b: Genome, rnd: Random): Genome {
            val va = a.vec(); val vb = b.vec()
            return Genome().also { it.load(DoubleArray(10) { i -> if (rnd.nextBoolean()) va[i] else vb[i] }) }
        }
        fun write(g: Genome, dos: DataOutputStream) { for (v in g.vec()) dos.writeDouble(v) }
        fun read(dis: DataInputStream) = try {
            Genome().also { it.load(DoubleArray(10) { _ -> dis.readDouble() }) }
        } catch (t: Throwable) { null }
    }
}

// ═══════════════════ 网络 ═══════════════════

class Brain(val inN: Int, val h1: Int, val h2: Int, val actN: Int, seed: Long = System.nanoTime()) {
    var w1 = Array(h1) { DoubleArray(inN) }; var b1 = DoubleArray(h1)
    var w2 = Array(h2) { DoubleArray(h1) }; var b2 = DoubleArray(h2)
    var va = DoubleArray(h2); var vb = 0.0
    var aa = Array(actN) { DoubleArray(h2) }; var ab = DoubleArray(actN)
    private var g1 = Array(h1) { DoubleArray(inN) }; private var gb1 = DoubleArray(h1)
    private var g2 = Array(h2) { DoubleArray(h1) }; private var gb2 = DoubleArray(h2)
    private var gva = DoubleArray(h2); private var gvb = 0.0
    private var gaa = Array(actN) { DoubleArray(h2) }; private var gab = DoubleArray(actN)
    private var z1 = DoubleArray(h1); private var z2 = DoubleArray(h2)

    init {
        val rnd = Random(seed)
        for (j in 0 until h1) for (k in 0 until inN) w1[j][k] = rnd.nextGaussian() / sqrt(inN.toDouble())
        for (j in 0 until h2) for (k in 0 until h1) w2[j][k] = rnd.nextGaussian() / sqrt(h1.toDouble())
        for (j in 0 until h2) va[j] = rnd.nextGaussian() / sqrt(h2.toDouble())
        for (m in 0 until actN) for (j in 0 until h2) aa[m][j] = rnd.nextGaussian() / sqrt(h2.toDouble())
    }

    fun forward(x: DoubleArray): DoubleArray {
        for (j in 0 until h1) {
            var s = b1[j]; val wj = w1[j]
            for (k in 0 until inN) if (x[k] != 0.0) s += wj[k] * x[k]
            z1[j] = if (s > 0) s else 0.0
        }
        for (j in 0 until h2) {
            var s = b2[j]; val wj = w2[j]
            for (k in 0 until h1) if (z1[k] > 0) s += wj[k] * z1[k]
            z2[j] = if (s > 0) s else 0.0
        }
        var v = vb
        for (j in 0 until h2) v += va[j] * z2[j]
        var mean = 0.0; val adv = DoubleArray(actN)
        for (m in 0 until actN) {
            var s = ab[m]; val am = aa[m]
            for (j in 0 until h2) s += am[j] * z2[j]
            adv[m] = s; mean += s
        }
        mean /= actN
        return DoubleArray(actN) { m -> v + adv[m] - mean }
    }

    fun backward(x: DoubleArray, action: Int, target: Double, weight: Double = 1.0): Double {
        val q = forward(x)
        val err = q[action] - target
        if (!err.isFinite()) return 0.0
        val d = ((if (abs(err) <= 1.0) err else kotlin.math.sign(err)) * weight).coerceIn(-5.0, 5.0)
        val dz2 = DoubleArray(h2)
        for (j in 0 until h2) { gva[j] += d * z2[j]; dz2[j] += d * va[j] }
        gvb += d
        for (m in 0 until actN) {
            val dam = if (m == action) d - d / actN else -d / actN
            gab[m] += dam
            for (j in 0 until h2) { gaa[m][j] += dam * z2[j]; dz2[j] += dam * aa[m][j] }
        }
        val dz1 = DoubleArray(h1)
        for (j in 0 until h2) {
            if (z2[j] <= 0) continue
            gb2[j] += dz2[j]
            for (k in 0 until h1) { g2[j][k] += dz2[j] * z1[k]; dz1[k] += dz2[j] * w2[j][k] }
        }
        for (j in 0 until h1) {
            if (z1[j] <= 0) continue
            gb1[j] += dz1[j]
            for (k in 0 until inN) if (x[k] != 0.0) g1[j][k] += dz1[j] * x[k]
        }
        return err
    }

    fun apply(lr: Double, batch: Int) {
        val k = lr / max(1, batch)
        for (j in 0 until h1) { b1[j] -= (gb1[j] * k).coerceIn(-.05, .05); for (i in 0 until inN) w1[j][i] -= (g1[j][i] * k).coerceIn(-.05, .05) }
        for (j in 0 until h2) { b2[j] -= (gb2[j] * k).coerceIn(-.05, .05); for (i in 0 until h1) w2[j][i] -= (g2[j][i] * k).coerceIn(-.05, .05) }
        for (j in 0 until h2) va[j] -= (gva[j] * k).coerceIn(-.05, .05)
        vb -= (gvb * k).coerceIn(-.05, .05)
        for (m in 0 until actN) { ab[m] -= (gab[m] * k).coerceIn(-.05, .05); for (j in 0 until h2) aa[m][j] -= (gaa[m][j] * k).coerceIn(-.05, .05) }
        clear()
    }

    private fun clear() {
        for (j in 0 until h1) { gb1[j] = 0.0; java.util.Arrays.fill(g1[j], 0.0) }
        for (j in 0 until h2) { gb2[j] = 0.0; java.util.Arrays.fill(g2[j], 0.0) }
        java.util.Arrays.fill(gva, 0.0); gvb = 0.0
        for (m in 0 until actN) { gab[m] = 0.0; java.util.Arrays.fill(gaa[m], 0.0) }
    }

    fun copyFrom(o: Brain) {
        for (j in 0 until h1) { System.arraycopy(o.w1[j], 0, w1[j], 0, inN); b1[j] = o.b1[j] }
        for (j in 0 until h2) { System.arraycopy(o.w2[j], 0, w2[j], 0, h1); b2[j] = o.b2[j] }
        System.arraycopy(o.va, 0, va, 0, h2); vb = o.vb
        for (m in 0 until actN) { System.arraycopy(o.aa[m], 0, aa[m], 0, h2); ab[m] = o.ab[m] }
    }

    fun clone(): Brain { val b = Brain(inN, h1, h2, actN); b.copyFrom(this); return b }

    companion object {
        fun write(b: Brain, dos: DataOutputStream) {
            dos.writeInt(b.inN); dos.writeInt(b.h1); dos.writeInt(b.h2); dos.writeInt(b.actN)
            fun w(a: DoubleArray) { for (v in a) dos.writeDouble(v) }
            for (j in 0 until b.h1) w(b.w1[j]); w(b.b1)
            for (j in 0 until b.h2) w(b.w2[j]); w(b.b2)
            w(b.va); dos.writeDouble(b.vb)
            for (m in 0 until b.actN) w(b.aa[m]); w(b.ab)
        }
        fun read(dis: DataInputStream): Brain? = try {
            val inN = dis.readInt(); val h1 = dis.readInt(); val h2 = dis.readInt(); val actN = dis.readInt()
            if (inN <= 0 || h1 <= 0 || h2 <= 0 || actN <= 0) null
            else Brain(inN, h1, h2, actN).also { b ->
                fun r(a: DoubleArray) { for (i in a.indices) a[i] = dis.readDouble() }
                for (j in 0 until h1) r(b.w1[j]); r(b.b1)
                for (j in 0 until h2) r(b.w2[j]); r(b.b2)
                r(b.va); b.vb = dis.readDouble()
                for (m in 0 until actN) r(b.aa[m]); r(b.ab)
            }
        } catch (t: Throwable) { Log.w("SnakeAI", "brain read fail", t); null }
    }
}

class WorldModel {
    val net = Brain(Features.SIZE + 4, 32, 20, 4)

    fun predict(s: DoubleArray, a: Int): DoubleArray {
        val x = DoubleArray(Features.SIZE + 4)
        System.arraycopy(s, 0, x, 0, Features.SIZE)
        x[Features.SIZE + a] = 1.0
        val out = net.forward(x)
        return doubleArrayOf(out[0].coerceIn(0.0, 1.0), out[1].coerceIn(-1.0, 1.0), out[2].coerceIn(-1.0, 1.0), out[3].coerceIn(0.0, 1.0))
    }

    fun train(s: DoubleArray, a: Int, death: Double, foodDelta: Double, areaDelta: Double, tailOk: Double) {
        val x = DoubleArray(Features.SIZE + 4)
        System.arraycopy(s, 0, x, 0, Features.SIZE)
        x[Features.SIZE + a] = 1.0
        net.backward(x, 0, death)
        net.backward(x, 1, foodDelta)
        net.backward(x, 2, areaDelta)
        net.backward(x, 3, tailOk)
    }

    fun applyBatch() = net.apply(0.002, 4)
    fun write(dos: DataOutputStream) = Brain.write(net, dos)
    fun read(dis: DataInputStream): Boolean {
        Brain.read(dis)?.let { net.copyFrom(it); return true }
        return false
    }
}

// ═══════════════════ 回放 / 遗憾 ═══════════════════

class Replay(private val cap: Int = 20000) {
    class T(
        val s: DoubleArray, val a: Int, val r: Double, val ns: DoubleArray?,
        val done: Boolean, val ep: Long, var nextIdx: Int
    )

    private val items = arrayOfNulls<T>(cap)
    private val prios = DoubleArray(cap)
    private var idx = 0
    var size = 0; private set
    private var maxP = 1.0

    fun add(s: DoubleArray, a: Int, r: Double, ns: DoubleArray?, done: Boolean, ep: Long): Int {
        items[idx] = T(s, a, r, ns, done, ep, -1)
        prios[idx] = maxP
        val at = idx
        idx = (idx + 1) % cap; if (size < cap) size++
        return at
    }

    fun link(prevIdx: Int, nextIdx: Int) {
        val t = items[prevIdx] ?: return
        if (!t.done) t.nextIdx = nextIdx
    }

    fun get(i: Int): T? = items.getOrNull(i)

    fun sample(batch: Int, rnd: Random): List<Pair<T, Int>> {
        if (size == 0) return emptyList()
        var sum = 0.0; val cum = DoubleArray(size)
        for (i in 0 until size) { sum += prios[i]; cum[i] = sum }
        val out = ArrayList<Pair<T, Int>>(batch)
        repeat(batch) {
            val t = rnd.nextDouble() * sum
            var lo = 0; var hi = size - 1
            while (lo < hi) { val m = (lo + hi) / 2; if (cum[m] < t) lo = m + 1 else hi = m }
            items[lo]?.let { out.add(it to lo) }
        }
        return out
    }

    fun priority(i: Int) = prios[i]

    fun update(i: Int, td: Double, boost: Double = 0.0) {
        val p = min(80.0, abs(td) + .01 + boost); prios[i] = p
        if (p > maxP) maxP = p
    }
}

class RegretTable {
    private class Entry { var ret = DoubleArray(4); var cnt = IntArray(4) }
    private val map = HashMap<Int, Entry>()

    fun cluster(f: DoubleArray): Int {
        var danger = 0
        for (d in 0 until 4) if (f[d] > 0.5) danger = danger or (1 shl d)
        val fq = (if (f[8] >= 0) 1 else 0) + (if (f[9] >= 0) 2 else 0)
        val lenB = min(7, (f[14] * 8).toInt())
        val tight = if (f[29] < 0.3) 1 else 0
        return danger or (fq shl 4) or (lenB shl 6) or (tight shl 9)
    }

    fun penalty(f: DoubleArray, a: Int): Double {
        val e = map[cluster(f)] ?: return 0.0
        if (e.cnt[a] == 0) return 0.0
        val best = (0 until 4).filter { e.cnt[it] > 0 }.maxOfOrNull { e.ret[it] / e.cnt[it] } ?: return 0.0
        return max(0.0, best - e.ret[a] / e.cnt[a])
    }

    fun update(f: DoubleArray, chosen: Int, qMean: DoubleArray, bootstrap: Double) {
        val e = map.getOrPut(cluster(f)) { Entry() }
        e.ret[chosen] = e.ret[chosen] * 0.998 + bootstrap; e.cnt[chosen]++
        for (a in 0 until 4) {
            if (a == chosen || e.cnt[a] > 500) continue
            e.ret[a] = e.ret[a] * 0.998 + qMean[a]; e.cnt[a]++
        }
    }

    fun write(dos: DataOutputStream) {
        val top = map.entries.take(512)
        dos.writeInt(top.size)
        for ((k, e) in top) {
            dos.writeInt(k)
            for (a in 0 until 4) { dos.writeDouble(e.ret[a]); dos.writeInt(e.cnt[a]) }
        }
    }

    fun read(dis: DataInputStream) = try {
        map.clear()
        val n = dis.readInt().coerceIn(0, 4096)
        repeat(n) {
            val k = dis.readInt()
            val e = Entry()
            for (a in 0 until 4) { e.ret[a] = dis.readDouble(); e.cnt[a] = dis.readInt() }
            map[k] = e
        }
    } catch (t: Throwable) { Log.w("SnakeAI", "regret read fail", t) }
}

// ═══════════════════ 元控制器 ═══════════════════

class MetaController {
    enum class Phase { OPENING, MID, LATE, ENDGAME }
    enum class Strategy { FAST, SAFE, SPIRAL, ENDGAME }

    var phase = Phase.OPENING; private set
    var strategy = Strategy.FAST; private set
    var curriculum = 0; private set
    var tightness = 0.0; private set
    var fillRatio = 0.0; private set

    private var safeStreak = 0
    private var fastStreak = 0
    var timeBudgetMicros = 4000L; private set

    val wSafety get() = if (strategy == Strategy.SAFE) 3.2 else 1.6
    val wFood get() = if (strategy == Strategy.SAFE) 0.55 else 1.25
    val wSpace get() = if (strategy == Strategy.SAFE) 1.5 else 0.8
    val wLearn get() = when (curriculum) {
        0 -> 0.15
        1 -> 0.35
        2 -> 0.55
        else -> 0.7
    }
    val wSearch get() = if (strategy == Strategy.SAFE) 1.25 else 0.9
    val wRegret get() = 0.5

    fun update(e: GameEngine, bestScore: Int, recentDeathStreak: Int) {
        val cells = e.w * e.h
        val free = cells - e.snake.size
        fillRatio = e.snake.size.toDouble() / cells
        tightness = 1.0 - free.toDouble() / cells
        phase = when {
            free < e.snake.size / 2 + 10 -> Phase.ENDGAME
            fillRatio > 0.6 -> Phase.LATE
            fillRatio > 0.25 -> Phase.MID
            else -> Phase.OPENING
        }
        curriculum = when {
            recentDeathStreak >= 4 -> max(0, targetLevel(bestScore) - 1)
            else -> targetLevel(bestScore)
        }
        when {
            phase == Phase.ENDGAME -> { strategy = Strategy.ENDGAME; safeStreak = 0; fastStreak = 0 }
            tightness > 0.72 -> { safeStreak++; fastStreak = 0; if (safeStreak >= 5) strategy = Strategy.SAFE }
            else -> { fastStreak++; safeStreak = 0; if (fastStreak >= 5) strategy = Strategy.FAST }
        }
        timeBudgetMicros = when (phase) {
            Phase.OPENING -> 2500L
            Phase.MID -> 4000L
            Phase.LATE -> 7000L
            Phase.ENDGAME -> 2000L
        }
    }

    private fun targetLevel(best: Int): Int {
        if (best >= 100) return 4
        if (best >= 60) return 3
        if (best >= 30) return 2
        if (best >= 10) return 1
        return 0
    }

    fun escalateToSpiral() { strategy = Strategy.SPIRAL }
}

// ═══════════════════ AI 总管 ═══════════════════

class AiCore(ctx: Context) {
    class Decision(
        val dir: Int, val learnerDir: Int, val qMean: DoubleArray,
        val strategy: MetaController.Strategy, val goal: Goal,
        val area: Int, val margin: Int, val budgetUs: Long, val searchMs: Double
    )

    private class Cand(
        val d: Int, val hard: Boolean, val safety: Double, val food: Double,
        val space: Double, val danger: Double, val cfGain: Double
    )

    val ensemble = Array(3) { Brain(Features.SIZE, 48, 32, 4, seed = 1000L + it * 7919) }
    val targets = ensemble.map { it.clone() }
    val predictor = WorldModel()
    val replay = Replay(20000)
    val deathReplay = Replay(4000)
    val successReplay = Replay(6000)
    val hardReplay = Replay(4000)
    val genome = Genome()
    val memory = FailureMemory()
    val regret = RegretTable()
    val meta = MetaController()
    var eps = 1.0
    var trainSteps = 0L
    var bestScore = 0
    var lastLoss = 0.0
    var generation = 0
    var deathStreak = 0
    val deathStats = IntArray(5)

    @Volatile var intensity = 0

    class Info {
        @Volatile var goal = Goal.NONE
        @Volatile var strategy = MetaController.Strategy.FAST
        @Volatile var phase = MetaController.Phase.OPENING
        @Volatile var personality = "均衡型"
        @Volatile var area = 0
        @Volatile var margin = 0
        @Volatile var qSigma = 0.0
        @Volatile var deathProb = 0.0
        @Volatile var budgetUs = 0L
        @Volatile var curriculum = 0
        @Volatile var searchMs = 0.0
        @Volatile var lastDeathReason = DeathReason.WALL
        @Volatile var lastTailOk = true
        @Volatile var counterfactualGain = 0.0
    }

    val info = Info()
    private val rnd = Random()
    private val lock = Any()
    private val file = File(ctx.filesDir, "snake_ai_pro.dat")
    private val running = AtomicBoolean(false)
    private var thread: Thread? = null
    private var beta = 0.4

    fun act(e: GameEngine, loop: LoopDetector): Decision = synchronized(lock) {
        meta.update(e, bestScore, deathStreak)
        info.phase = meta.phase; info.curriculum = meta.curriculum
        val deadline = System.nanoTime() + meta.timeBudgetMicros * 1000
        val t0 = System.nanoTime()

        if (meta.strategy == MetaController.Strategy.ENDGAME) {
            val d = Hamiltonian.follow(e, strict = true)
            info.strategy = meta.strategy; info.goal = Goal.SPIRAL
            return Decision(d, d, DoubleArray(4), meta.strategy, Goal.SPIRAL, -1, -1,
                meta.timeBudgetMicros, (System.nanoTime() - t0) / 1e6)
        }

        val sim = Sim(e.w, e.h).load(e)
        val len = e.snake.size
        val artPair = sim.articulation()
        val art = artPair.first
        val artMax = artPair.second

        val hungerRatio = e.stepsSinceFood.toDouble() / (e.w * e.h * 2)
        var margin = genome.margin
        if (hungerRatio > genome.patience) {
            val pressure = ((hungerRatio - genome.patience) / (1.0 - genome.patience)).coerceIn(0.0, 1.0)
            margin *= (1.0 - genome.risk * pressure)
        }
        margin += meta.fillRatio * meta.fillRatio * 8.0
        val marginI = margin.toInt().coerceAtLeast(0)

        val dTail = sim.distField(sim.tail)
        val oscPen = loop.oscillationPenalty()

        val cands = ArrayList<Cand>()
        val s0 = Features.extract(e, e.dir)
        val qVectors = ensemble.map { it.forward(s0) }
        val qMean = DoubleArray(4)
        for (a in 0 until 4) { var m = 0.0; for (q in qVectors) m += q[a]; qMean[a] = m / qVectors.size }

        for (d in 0 until 4) {
            if (len > 1 && (d + 2) % 4 == e.dir) continue
            val nc = e.nextCell(d) ?: continue
            val cellIdx = nc.second * e.w + nc.first
            val eat = cellIdx == sim.foodIdx

            val s2 = sim.copy()
            if (!s2.step(d, eat)) { cands.add(Cand(d, true, 0.0, 0.0, 0.0, 1.0, 0.0)); continue }

            val stats = s2.regionStats(s2.head)
            val area = stats.first
            val deadEnds = stats.second
            val perim = stats.third
            var articRisk = 0.0
            if (art[cellIdx]) {
                val m = artMax[cellIdx]
                if (m < len) { cands.add(Cand(d, true, 0.0, 0.0, 0.0, 1.0, 0.0)); continue }
                articRisk = if (m < len + marginI) 0.5 else 0.15
            }
            val tailSteps = s2.tailReachSteps(s2.head)
            val tailOk = tailSteps >= 0
            val df = s2.distField(s2.head)
            var m2 = 0; var m4 = 0; var m8 = 0; var access = 0.0; var territory = 0.0
            for (i in 0 until s2.n) {
                if (i == s2.head) continue
                val dh = df[i]
                if (dh < 0) continue
                if (!s2.occ[i] || i == s2.tail) {
                    if (dh <= 2) m2++
                    if (dh <= 4) m4++
                    if (dh <= 8) m8++
                    access += 1.0 / (1.0 + dh)
                    if (dTail[i] >= 0) territory += 1.0 / (1.0 + dh) - 1.0 / (1.0 + dTail[i])
                }
            }
            val pred = predictor.predict(s0, d)
            val deathProb = pred[0]
            val distNow = e.distToFood(e.head().first, e.head().second)
            val distAfter: Int = if (eat) 0 else e.distToFood(nc.first, nc.second)
            val foodGain = (distNow - distAfter).toDouble()

            var followupOk = false
            for (d2 in 0 until 4) {
                val s3 = s2.copy()
                if (s3.stepAuto(d2) && s3.flood(s3.head) >= s3.len) { followupOk = true; break }
            }

            val areaScore = min(1.0, area.toDouble() / (len + marginI + 1))
            var safety = areaScore * 0.5 + (if (tailOk) 0.22 else 0.0) +
                    min(0.13, m4 / 32.0) + min(0.08, m2 / 10.0)
            if (area < len) safety -= 3.0
            else if (area < len + marginI) safety -= 0.35
            safety -= articRisk
            safety -= deathProb * 0.45
            if (!tailOk) safety -= 0.3
            if (!followupOk) safety -= 0.25
            safety -= min(0.15, deadEnds * 0.03)
            safety -= min(0.1, perim / 200.0 * 0.1)

            val food = foodGain * 0.10 + (if (eat) 1.0 else 0.0) + pred[1] * 0.15
            val space = min(1.0, m4 / 25.0) * 0.3 + min(1.0, m8 / 60.0) * 0.25 +
                    min(1.0, max(0.0, territory) / 8.0) * 0.25 + min(1.0, access / 28.0) * 0.2
            val danger = loop.cellPenalty(nc.first, nc.second) + oscPen * 0.4 + memory.danger(nc.first, nc.second, d)
            val cfGain = pred[2] * 0.3 + pred[3] * 0.2

            cands.add(Cand(d, false, safety, food, space, danger, cfGain))
        }

        if (cands.isEmpty() || cands.all { it.hard }) {
            meta.escalateToSpiral()
            val d = Hamiltonian.follow(e, strict = false)
            info.strategy = MetaController.Strategy.SPIRAL; info.goal = Goal.SPIRAL
            return Decision(d, d, qMean, MetaController.Strategy.SPIRAL, Goal.SPIRAL, 0, marginI,
                meta.timeBudgetMicros, (System.nanoTime() - t0) / 1e6)
        }

        val sortedQ = Array(4) { a -> qVectors.map { it[a] }.sorted() }
        val lam = (genome.lambda * (1.0 + min(1.0, deathStreak * 0.15))).coerceIn(0.0, 2.0)
        val qRisk = DoubleArray(4) { a ->
            val s = sortedQ[a]
            val worst = s[0]
            (qMean[a] * (1 - lam / 2) + worst * (lam / 2)) + (qMean[a] - s[s.size / 2]) * 0.3
        }
        val regretPen = DoubleArray(4) { a -> regret.penalty(s0, a) }
        var learnerDir = 0
        for (a in 1 until 4) if (qMean[a] > qMean[learnerDir]) learnerDir = a
        var spread = 0.0
        for (a in 0 until 4) for (q in qVectors) spread += abs(q[a] - qMean[a])
        info.qSigma = spread / 12.0
        info.deathProb = predictor.predict(s0, learnerDir)[0]

        val searchPrior = DoubleArray(4)
        val useMcts = meta.phase == MetaController.Phase.LATE || meta.tightness > 0.6
        if (meta.curriculum >= 1) {
            if (useMcts && meta.curriculum >= 2)
                Mcts.search(sim, e.dir, deadline, 90, qMean, rnd).copyInto(searchPrior)
            else
                BeamSearch.search(sim, e.dir, deadline, 140, 6, 14).copyInto(searchPrior)
        }
        var spMax = 0.0
        for (v in searchPrior) spMax = max(spMax, abs(v))
        if (spMax > 1e-9) for (a in 0 until 4) searchPrior[a] /= spMax

        val disagreeGate = if (info.qSigma > 0.8) 0.5 else 1.0

        val m = meta
        var best: Cand? = null
        var bestTotal = Double.NEGATIVE_INFINITY
        for (c in cands) {
            if (c.hard) continue
            var total = 0.0
            total += m.wSafety * c.safety
            total += m.wFood * c.food
            total += m.wSpace * c.space
            total += m.wLearn * disagreeGate * (qRisk[c.d] * 0.15 + c.cfGain)
            total += m.wSearch * searchPrior[c.d]
            total -= m.wRegret * genome.regretSens * regretPen[c.d] * 2.0
            total -= c.danger * 0.8
            if (total > bestTotal) { bestTotal = total; best = c }
        }

        if (best == null) {
            val d = Hamiltonian.follow(e, strict = false)
            return Decision(d, learnerDir, qMean, meta.strategy, Goal.NONE, 0, marginI,
                meta.timeBudgetMicros, (System.nanoTime() - t0) / 1e6)
        }

        info.strategy = meta.strategy
        info.goal = when {
            best.food > 0.8 -> Goal.FOOD
            best.safety < 0.4 -> Goal.TAIL
            best.space > best.food -> Goal.SPACE
            searchPrior[best.d] > 0.5 -> Goal.SEARCH
            else -> Goal.LEARN
        }
        info.area = (best.safety * 100).toInt()
        info.margin = marginI
        info.budgetUs = meta.timeBudgetMicros
        info.counterfactualGain = best.cfGain
        val searchMs = (System.nanoTime() - t0) / 1e6
        info.searchMs = searchMs
        Decision(best.d, learnerDir, qMean, meta.strategy, info.goal, info.area, marginI, meta.timeBudgetMicros, searchMs)
    }

    fun postStep(s: DoubleArray, d: Decision, r: Double, ns: DoubleArray?, done: Boolean, ep: Long, prevLink: Int): Int {
        if (ns != null) {
            val nq = ensemble.map { it.forward(ns) }
            var maxNq = Double.NEGATIVE_INFINITY
            for (a in 0 until 4) {
                var m = 0.0
                for (q in nq) m += q[a]
                m /= nq.size
                if (m > maxNq) maxNq = m
            }
            regret.update(s, d.dir, d.qMean, r + 0.92 * maxNq)
        }
        val overridden = d.learnerDir != d.dir
        val idx = synchronized(lock) { replay.add(s, d.dir, r, ns, done, ep) }
        if (prevLink >= 0) synchronized(lock) { replay.link(prevLink, idx) }
        if (done) synchronized(lock) { deathReplay.add(s, d.dir, r, ns, true, ep) }
        if (r > 5.0) synchronized(lock) { successReplay.add(s, d.dir, r, ns, done, ep) }
        if (overridden) synchronized(lock) { hardReplay.add(s, d.dir, r, ns, done, ep) }
        return idx
    }

    fun observeDeath(reason: DeathReason, causal: CausalHistory) = synchronized(lock) {
        var r = reason
        if (r == DeathReason.SELF && !info.lastTailOk) r = DeathReason.TRAPPED
        info.lastDeathReason = r
        val idx = when (r) {
            DeathReason.WALL -> 0
            DeathReason.SELF -> 1
            DeathReason.TRAPPED -> 2
            DeathReason.STARVED -> 3
            DeathReason.WIN -> 4
        }
        deathStats[idx]++
        deathStreak = if (r == DeathReason.WIN) 0 else deathStreak + 1
        genome.adjust(r)
        info.personality = genome.personality()
        causal.onDeath { s, w -> if (w >= 0.4) memory.record(s.x, s.y, s.dir) }
    }

    fun learn(): Double = synchronized(lock) {
        if (replay.size < 600) return 0.0
        val cur = meta.curriculum
        val mainN = when (cur) { 0 -> 40; 1 -> 38; 2 -> 34; else -> 32 }
        val succN = when (cur) { 0 -> 20; 1 -> 14; 2 -> 10; else -> 8 }
        val deathN = when (cur) { 0 -> 4; 1 -> 8; 2 -> 14; else -> 18 }
        val hardN = 8
        val batch = ArrayList<Pair<Replay.T, Int>>()
        batch.addAll(replay.sample(mainN, rnd))
        if (successReplay.size > 100) batch.addAll(successReplay.sample(succN, rnd))
        if (deathReplay.size > 100) batch.addAll(deathReplay.sample(deathN, rnd))
        if (hardReplay.size > 100) batch.addAll(hardReplay.sample(hardN, rnd))
        if (batch.isEmpty()) return 0.0

        var loss = 0.0; var n = 0
        val tdsAll = ArrayList<Pair<Int, Double>>()
        for (bi in ensemble.indices) {
            for ((t, i) in batch) {
                var cur2 = t
                var ret = 0.0; var gamma = 1.0; var steps = 0
                var terminated = false
                val nstep = 1 + rnd.nextInt(5)
                while (steps < nstep) {
                    ret += gamma * cur2.r; gamma *= 0.92; steps++
                    if (cur2.done) { terminated = true; break }
                    val nxtIdx = cur2.nextIdx
                    if (nxtIdx < 0) break
                    val nxt = replay.get(nxtIdx) ?: break
                    if (nxt.ep != cur2.ep) break
                    cur2 = nxt
                }
                val nsCur = if (terminated) null else cur2.ns
                if (nsCur != null) {
                    val q = ensemble[bi].forward(nsCur)
                    var mq = Double.NEGATIVE_INFINITY
                    for (a in 0 until 4) if (q[a] > mq) mq = q[a]
                    ret += gamma * mq
                }
                if (!ret.isFinite()) continue
                val isW = if (i < 20000) {
                    val p = max(1e-4, replay.priority(i))
                    (1.0 / (replay.size * p)).coerceIn(0.25, 2.0) * beta
                } else 1.0
                val td = ensemble[bi].backward(t.s, t.a, ret, isW)
                if (td.isFinite()) { loss += min(abs(td), 10.0); n++; tdsAll.add(i to td) }
            }
            ensemble[bi].apply(0.0025, max(1, batch.size))
        }
        for ((i, td) in tdsAll) {
            replay.update(i, td, if (abs(td) > 4.0) 6.0 else 0.0)
            if (abs(td) > 5.0) {
                val t = replay.get(i)
                if (t != null && hardReplay.size < 3900) hardReplay.add(t.s, t.a, t.r, t.ns, t.done, t.ep)
            }
        }
        for ((t, _) in batch) {
            val nsT = t.ns
            if (nsT == null) continue
            val deathT = if (t.done) 1.0 else 0.0
            val fd = (abs(t.s[8]) + abs(t.s[9])) - (abs(nsT[8]) + abs(nsT[9]))
            val ad = nsT[4] - t.s[4]
            predictor.train(t.s, t.a, deathT, fd, ad, nsT[4])
        }
        predictor.applyBatch()
        trainSteps++
        beta = min(1.0, beta + 0.0002)
        eps = max(when (cur) { 0 -> 0.10; 1 -> 0.08; else -> 0.05 }, eps * 0.9995)
        if (trainSteps % 500 == 0L) for (bi in ensemble.indices) targets[bi].copyFrom(ensemble[bi])
        lastLoss = if (n > 0) loss / n else 0.0
        lastLoss
    }

    fun recordBest(s: Int) = synchronized(lock) {
        if (s > bestScore) { bestScore = s; deathStreak = 0; save() }
    }

    fun startTraining() {
        if (!running.compareAndSet(false, true)) return
        load()
        thread = Thread({
            val loop = LoopDetector()
            val causal = CausalHistory()
            val pop = ArrayList<Genome>()
            repeat(12) { pop.add(genome.copy().also { it.mutate(rnd) }) }
            var games = 0; var ep = 0L
            while (running.get()) {
                try {
                    ep++
                    val e = GameEngine(); e.reset()
                    loop.reset(); causal.reset()
                    val capSteps = when (meta.curriculum) { 0 -> 700L; 1 -> 1500L; 2 -> 3000L; else -> 4000L }
                    var link = -1
                    while (e.alive && e.totalSteps < capSteps) {
                        val s = Features.extract(e, e.dir)
                        val d = act(e, loop)
                        causal.record(e)
                        val prevDist = e.distToFood(e.head().first, e.head().second)
                        val res = e.step(d.dir)
                        loop.record(e)
                        val shaping = when (meta.curriculum) { 0 -> 0.6; 1 -> 0.4; 2 -> 0.25; else -> 0.15 }
                        val r = when (res) {
                            StepResult.DIED -> -10.0
                            StepResult.ATE -> 10.0
                            StepResult.MOVED -> (prevDist - e.distToFood(e.head().first, e.head().second)) * shaping - 0.01
                        }
                        val ns = if (e.alive) Features.extract(e, e.dir) else null
                        link = postStep(s, d, r, ns, !e.alive, ep, link)
                        if (e.totalSteps % 2 == 0L) learn()
                    }
                    if (!e.alive) observeDeath(e.deathReason, causal)
                    else deathStreak = 0
                    recordBest(e.score)
                    if (++games % 12 == 0) {
                        val fits = pop.map { g ->
                            val ge = GameEngine(); ge.reset()
                            val ld = LoopDetector()
                            var st = 0
                            while (ge.alive && st < 2500) {
                                val sm = Sim(ge.w, ge.h).load(ge)
                                var bd = 0; var bs = Double.NEGATIVE_INFINITY
                                for (dd in 0 until 4) {
                                    if (ge.snake.size > 1 && (dd + 2) % 4 == ge.dir) continue
                                    val s2 = sm.copy()
                                    if (!s2.stepAuto(dd)) continue
                                    val a = s2.flood(s2.head)
                                    val nc = ge.nextCell(dd)!!
                                    val sc = a * 3.0 - ge.distToFood(nc.first, nc.second) -
                                            memory.danger(nc.first, nc.second, dd) * 40 -
                                            ld.cellPenalty(nc.first, nc.second) * 20 + g.margin * 0.1
                                    if (sc > bs) { bs = sc; bd = dd }
                                }
                                ge.step(bd); ld.record(ge); st++
                            }
                            ge.score * 100.0 + ge.snake.size + ge.totalSteps * 0.005
                        }
                        val order = fits.indices.sortedByDescending { fits[it] }
                        val next = ArrayList<Genome>(12)
                        for (i in 0 until 3) next.add(pop[order[i]].copy())
                        while (next.size < 12) {
                            val a = pop[order[rnd.nextInt(6)]]
                            val b = pop[order[rnd.nextInt(6)]]
                            next.add(Genome.cross(a, b, rnd).also { it.mutate(rnd) })
                        }
                        for (i in next.indices) pop[i] = next[i]
                        if (fits[order[0]] > 200 && fits[order[0]] > bestScore * 100.0 * 1.05)
                            synchronized(lock) { genome.copyFrom(pop[order[0]]) }
                        generation++
                    }
                    when (intensity) {
                        0 -> Thread.sleep(30)
                        1 -> Thread.sleep(5)
                        else -> { }
                    }
                } catch (t: Throwable) {
                    Log.w("SnakeAI", "train error", t)
                    try { Thread.sleep(500) } catch (_: InterruptedException) { return@Thread }
                }
            }
        }, "snake-ai").apply { isDaemon = true; start() }
    }

    fun stopTraining() {
        if (!running.compareAndSet(true, false)) return
        save(); thread?.interrupt(); thread = null
    }

    fun save() = synchronized(lock) {
        try {
            val tmp = File(file.parentFile, "snake_ai_pro.tmp")
            DataOutputStream(FileOutputStream(tmp).buffered()).use {
                it.writeInt(0x534E4B50)
                it.writeDouble(eps); it.writeLong(trainSteps); it.writeInt(bestScore)
                it.writeDouble(beta); it.writeInt(deathStreak)
                it.writeInt(ensemble.size)
                for (b in ensemble) Brain.write(b, it)
                predictor.write(it)
                Genome.write(genome, it)
                memory.write(it)
                regret.write(it)
                it.writeInt(generation)
                for (v in deathStats) it.writeInt(v)
            }
            if (file.exists()) file.delete()
            if (!tmp.renameTo(file)) Log.w("SnakeAI", "save rename failed")
        } catch (t: Throwable) { Log.w("SnakeAI", "save fail", t) }
    }

    private fun load() = synchronized(lock) {
        if (!file.exists()) return
        try {
            DataInputStream(FileInputStream(file).buffered()).use {
                if (it.readInt() != 0x534E4B50) return
                eps = it.readDouble(); trainSteps = it.readLong(); bestScore = it.readInt()
                beta = it.readDouble(); deathStreak = it.readInt()
                val k = it.readInt().coerceIn(1, 8)
                for (i in 0 until k) if (i < ensemble.size) Brain.read(it)?.let { b -> ensemble[i].copyFrom(b) }
                predictor.read(it)
                Genome.read(it)?.let { g -> genome.copyFrom(g) }
                memory.read(it)
                regret.read(it)
                generation = it.readInt()
                for (i in deathStats.indices) deathStats[i] = it.readInt()
                for (i in ensemble.indices) targets[i].copyFrom(ensemble[i])
            }
            info.personality = genome.personality()
            Log.i("SnakeAI", "loaded best=$bestScore steps=$trainSteps gen=$generation")
        } catch (t: Throwable) { Log.w("SnakeAI", "load fail", t) }
    }
}

// ═══════════════════ 主题 ═══════════════════

class Theme(ctx: Context) {
    var bg = Color.parseColor("#0D1117"); private set
    var board = Color.parseColor("#161B22"); private set
    var grid = Color.parseColor("#21262D"); private set
    var food = Color.parseColor("#FF5B5B"); private set
    var head = Color.parseColor("#4ADE80"); private set
    var body = Color.parseColor("#2E9E57"); private set
    var text = Color.parseColor("#E6EDF3"); private set
    var dim = Color.parseColor("#8B949E"); private set
    var skinId = "green"; private set
    var boardId = "dark"; private set

    private val prefs = ctx.getSharedPreferences("snake_prefs", Context.MODE_PRIVATE)

    fun reload() {
        skinId = prefs.getString("equipped_skin", "green") ?: "green"
        boardId = prefs.getString("equipped_board", "dark") ?: "dark"
        when (boardId) {
            "light" -> {
                bg = Color.parseColor("#E8EAED"); board = Color.parseColor("#FFFFFF")
                grid = Color.parseColor("#DADCE0"); text = Color.parseColor("#202124")
                dim = Color.parseColor("#5F6368")
            }
            "neon" -> {
                bg = Color.parseColor("#050510"); board = Color.parseColor("#0A0A2A")
                grid = Color.parseColor("#202060"); food = Color.parseColor("#00FFFF")
            }
            "forest" -> {
                bg = Color.parseColor("#0F1A0F"); board = Color.parseColor("#1A2E1A")
                grid = Color.parseColor("#2A4A2A"); food = Color.parseColor("#FFD700")
            }
            "cyberpunk" -> {
                bg = Color.parseColor("#12051F"); board = Color.parseColor("#1F0A33")
                grid = Color.parseColor("#3A1560"); food = Color.parseColor("#FF00A0")
            }
            else -> {
                bg = Color.parseColor("#0D1117"); board = Color.parseColor("#161B22")
                grid = Color.parseColor("#21262D"); text = Color.parseColor("#E6EDF3")
                dim = Color.parseColor("#8B949E")
            }
        }
        when (skinId) {
            "blue" -> { head = Color.parseColor("#60A5FA"); body = Color.parseColor("#2563EB") }
            "red" -> { head = Color.parseColor("#F87171"); body = Color.parseColor("#DC2626") }
            "purple" -> { head = Color.parseColor("#C084FC"); body = Color.parseColor("#7C3AED") }
            "gold" -> { head = Color.parseColor("#FDE047"); body = Color.parseColor("#D97706") }
            "green" -> { head = Color.parseColor("#4ADE80"); body = Color.parseColor("#2E9E57") }
        }
    }

    fun isRainbowSkin() = skinId == "rainbow"
    fun isRainbowBoard() = boardId == "rainbow_board"
}

// ═══════════════════ SnakeView ═══════════════════

class SnakeView @JvmOverloads constructor(
    context: Context, attrs: AttributeSet? = null
) : View(context, attrs) {

    private val engine = GameEngine()
    private val ai = AiCore(context)
    private val loop = LoopDetector()
    private val causal = CausalHistory()
    private val theme = Theme(context)
    private val prefs = context.getSharedPreferences("snake_prefs", Context.MODE_PRIVATE)

    var onScoreChanged: ((Int) -> Unit)? = null
    var onMoneyChanged: ((Int) -> Unit)? = null
    private var sessionMoney = 0

    private var aiOn = true
    private var pausedByLifecycle = false

    fun setTrainingMode(on: Boolean) { ai.intensity = if (on) 1 else 0 }
    fun setReinforceTraining(on: Boolean) { ai.intensity = if (on) 2 else 0 }
    fun setAIMode(mode: Int) {
        aiOn = mode != 0
        if (aiOn) restart()
    }
    fun resume() {
        pausedByLifecycle = false
        invalidate()
    }
    fun pause() {
        pausedByLifecycle = true
        flushMoney()
    }
    fun updateCurrentSkin() { theme.reload(); invalidate() }
    fun updateCurrentBoard() { theme.reload(); invalidate() }

    private fun flushMoney() {
        if (sessionMoney <= 0) return
        val total = prefs.getInt("money", 0) + sessionMoney
        prefs.edit().putInt("money", total).apply()
        sessionMoney = 0
        onMoneyChanged?.invoke(total)
    }

    private var deathAt = 0L
    private var stepAccum = 0L
    private var lastFrame = 0L
    private var tick = 0L
    private var attached = false

    private val frameCb: Choreographer.FrameCallback = object : Choreographer.FrameCallback {
        override fun doFrame(frameTimeNanos: Long) {
            onFrame(frameTimeNanos)
            if (attached) Choreographer.getInstance().postFrameCallback(this)
        }
    }

    private class P(var x: Float, var y: Float, var vx: Float, var vy: Float, var life: Float)
    private val particles = ArrayList<P>()
    private val rng = Random()

    private val fill = Paint(Paint.ANTI_ALIAS_FLAG)
    private val stroke = Paint(Paint.ANTI_ALIAS_FLAG).apply { style = Paint.Style.STROKE; strokeWidth = 2f }
    private val text = Paint(Paint.ANTI_ALIAS_FLAG)
    private val bold = Paint(Paint.ANTI_ALIAS_FLAG)

    private fun dp(v: Float) = v * resources.displayMetrics.density

    init {
        engine.reset()
        theme.reload()
        bold.isFakeBoldText = true
    }

    override fun onAttachedToWindow() {
        super.onAttachedToWindow()
        attached = true
        Choreographer.getInstance().postFrameCallback(frameCb)
        ai.startTraining()
    }

    override fun onDetachedFromWindow() {
        attached = false
        Choreographer.getInstance().removeFrameCallback(frameCb)
        ai.stopTraining()
        super.onDetachedFromWindow()
    }

    private fun boardRect(): RectF {
        val top = dp(122f)
        val size = min(width - dp(24f), height - top - dp(24f)).toFloat()
        return RectF((width - size) / 2f, top, (width + size) / 2f, top + size)
    }

    private fun cell() = boardRect().width() / engine.w

    private fun onFrame(nanos: Long) {
        val now = nanos / 1_000_000
        if (lastFrame == 0L) lastFrame = now
        val dt = min(100L, now - lastFrame)
        lastFrame = now; tick++
        if (!pausedByLifecycle && aiOn && engine.alive) {
            val interval = when (ai.intensity) {
                2 -> 35L
                1 -> 60L
                else -> 110L
            }
            stepAccum += dt
            while (stepAccum >= interval) {
                stepAccum -= interval
                gameTick()
                if (!engine.alive) { stepAccum = 0; break }
            }
        }
        if (!engine.alive && aiOn && !pausedByLifecycle) {
            if (deathAt == 0L) deathAt = now
            else if (now - deathAt > 1200) restart()
        }
        updateParticles(dt.toFloat())
        invalidate()
    }

    private fun gameTick() {
        val prev = engine.distToFood(engine.head().first, engine.head().second)
        val s = Features.extract(engine, engine.dir)
        val d = ai.act(engine, loop)
        causal.record(engine)
        val res = engine.step(d.dir)
        loop.record(engine)
        val r = when (res) {
            StepResult.DIED -> -10.0
            StepResult.ATE -> 10.0
            StepResult.MOVED -> (prev - engine.distToFood(engine.head().first, engine.head().second)) * 0.3 - 0.01
        }
        ai.postStep(s, d, r, if (engine.alive) Features.extract(engine, engine.dir) else null, !engine.alive, 0L, -1)
        if (res == StepResult.ATE) {
            spawnParticles(engine.food.first, engine.food.second, 12)
            sessionMoney += 1
            onScoreChanged?.invoke(engine.score)
            onMoneyChanged?.invoke(prefs.getInt("money", 0) + sessionMoney)
        }
        if (!engine.alive) {
            ai.observeDeath(engine.deathReason, causal)
            ai.recordBest(engine.score)
            flushMoney()
            spawnParticles(engine.head().first, engine.head().second, 30)
        }
    }

    private fun restart() {
        engine.reset(); loop.reset(); causal.reset()
        particles.clear(); deathAt = 0; stepAccum = 0
        onScoreChanged?.invoke(0)
    }

    private fun spawnParticles(gx: Int, gy: Int, n: Int) {
        val b = boardRect(); val c = cell()
        repeat(n) {
            val a = rng.nextFloat() * (Math.PI * 2).toFloat()
            particles.add(P(
                b.left + (gx + .5f) * c, b.top + (gy + .5f) * c,
                kotlin.math.cos(a) * .12f * c, kotlin.math.sin(a) * .12f * c, .7f
            ))
        }
    }

    private fun updateParticles(dt: Float) {
        val it = particles.iterator()
        while (it.hasNext()) {
            val p = it.next()
            p.x += p.vx * dt; p.y += p.vy * dt
            p.vx *= .96f; p.vy *= .96f
            p.life -= dt / 700f
            if (p.life <= 0) it.remove()
        }
    }

    private var downX = 0f; private var downY = 0f

    override fun onTouchEvent(e: MotionEvent): Boolean {
        when (e.actionMasked) {
            MotionEvent.ACTION_DOWN -> { downX = e.x; downY = e.y; return true }
            MotionEvent.ACTION_UP -> {
                if (!aiOn) {
                    val dx = e.x - downX; val dy = e.y - downY
                    if (max(abs(dx), abs(dy)) > dp(24f)) {
                        val d = if (abs(dx) > abs(dy)) (if (dx > 0) 1 else 3) else (if (dy > 0) 2 else 0)
                        if (!(engine.snake.size > 1 && (d + 2) % 4 == engine.dir)) engine.dir = d
                        if (!engine.alive) restart()
                    }
                }
                performClick(); return true
            }
        }
        return super.onTouchEvent(e)
    }

    override fun onDraw(cv: Canvas) {
        if (theme.isRainbowBoard()) {
            val hue = (tick * 0.15f) % 360f
            cv.drawColor(Color.HSVToColor(floatArrayOf(hue, 0.55f, 0.10f)))
        } else {
            cv.drawColor(theme.bg)
        }
        drawGame(cv)
        drawMiniStatus(cv)
    }

    private fun drawGame(cv: Canvas) {
        val b = boardRect(); val c = cell()
        if (theme.isRainbowBoard()) {
            val hue = (tick * 0.15f + 30f) % 360f
            fill.color = Color.HSVToColor(floatArrayOf(hue, 0.6f, 0.16f))
        } else {
            fill.color = theme.board
        }
        cv.drawRoundRect(RectF(b.left - dp(5f), b.top - dp(5f), b.right + dp(5f), b.bottom + dp(5f)), dp(12f), dp(12f), fill)
        stroke.color = theme.grid
        stroke.strokeWidth = 1.5f
        for (i in 0..engine.w) {
            cv.drawLine(b.left + i * c, b.top, b.left + i * c, b.bottom, stroke)
            cv.drawLine(b.left, b.top + i * c, b.right, b.top + i * c, stroke)
        }
        val pulse = (sin(tick * .07f) + 1f) / 2f
        fill.color = theme.food
        cv.drawCircle(b.left + (engine.food.first + .5f) * c, b.top + (engine.food.second + .5f) * c, c * (.3f + pulse * .07f), fill)

        var i = engine.snake.size
        val rainbow = theme.isRainbowSkin()
        for (seg in engine.snake) {
            if (rainbow) {
                val hue = (tick * 3f + i * 24f) % 360f
                fill.color = Color.HSVToColor(floatArrayOf(hue, 0.85f, 0.98f))
            } else {
                fill.color = if (i == engine.snake.size) theme.head else theme.body
                if (i < engine.snake.size) fill.alpha = (150 + (1f - i.toFloat() / max(1, engine.snake.size)) * 80).toInt().coerceIn(150, 230)
            }
            val l = b.left + seg.first * c + c * .07f
            val t2 = b.top + seg.second * c + c * .07f
            cv.drawRoundRect(l, t2, l + c * .86f, t2 + c * .86f, c * .28f, c * .28f, fill)
            i--
        }
        fill.alpha = 255
        for (p in particles) {
            fill.color = Color.argb((p.life * 255).toInt().coerceIn(0, 255), 255, 205, 120)
            cv.drawCircle(p.x, p.y, c * .1f * p.life, fill)
        }
        if (!engine.alive && !aiOn) {
            bold.color = theme.text; bold.textSize = dp(26f); bold.textAlign = Paint.Align.CENTER
            cv.drawText("游戏结束 · 滑动重开", width / 2f, b.centerY(), bold)
        }
    }

    private fun drawMiniStatus(cv: Canvas) {
        val b = boardRect()
        val y = min(b.bottom + dp(26f), height - dp(10f))
        text.color = theme.dim; text.textSize = dp(12f); text.textAlign = Paint.Align.LEFT
        val info = ai.info
        val strategy = when (info.strategy) {
            MetaController.Strategy.FAST -> "极速"
            MetaController.Strategy.SAFE -> "保守"
            MetaController.Strategy.SPIRAL -> "螺旋"
            MetaController.Strategy.ENDGAME -> "终局"
        }
        val goal = when (info.goal) {
            Goal.FOOD -> "觅食"
            Goal.TAIL -> "尾行"
            Goal.SPACE -> "控场"
            Goal.SEARCH -> "搜索"
            Goal.SPIRAL -> "螺旋"
            Goal.LEARN -> "学习"
            Goal.NONE -> "—"
        }
        val phase = when (info.phase) {
            MetaController.Phase.OPENING -> "开局"
            MetaController.Phase.MID -> "中期"
            MetaController.Phase.LATE -> "后期"
            MetaController.Phase.ENDGAME -> "终局"
        }
        cv.drawText(
            "🤖${info.personality}·$strategy·$phase·$goal 余量${info.margin} σ=${"%.2f".format(info.qSigma)} " +
                "代${ai.generation} 记忆${ai.memory.size()} 训${ai.trainSteps}",
            dp(12f), y, text
        )
    }
}
