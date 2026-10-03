package com.example.snake

import kotlin.random.Random

/** No Android dependency: manual play, AI viewing and training share these exact rules. */
class SnakeEngine(val cols: Int = 15, val rows: Int = 15, seed: Int = Random.nextInt()) {
    val capacity = cols * rows
    private val rng = Random(seed)
    private val ring = IntArray(capacity)
    val occupied = BooleanArray(capacity)
    private var first = 0
    var length = 1; private set
    var direction = RIGHT; private set
    var food = -1; private set
    var score = 0; private set
    var combo = 0; private set
    var hunger = 0; private set
    var steps = 0; private set
    var foods = 0; private set
    var ended = false; private set
    var cause = ""; private set
    val head: Int get() = ring[first]
    val tail: Int get() = cellAt(length - 1)
    val speedMs: Long get() = (220L - length * 2L).coerceAtLeast(45L)
    init { require(cols >= 3 && rows >= 3); reset() }
    fun cellAt(i: Int): Int = ring[(first + i) % capacity]
    fun reset() {
        occupied.fill(false); first = 0; length = 1; direction = RIGHT
        ring[0] = (rows / 2) * cols + cols / 2; occupied[ring[0]] = true
        score = 0; combo = 0; hunger = 0; steps = 0; foods = 0; ended = false; cause = ""
        placeFood()
    }
    fun next(cell: Int, action: Int): Int = when (action) {
        UP -> if (cell >= cols) cell - cols else -1
        RIGHT -> if (cell % cols < cols - 1) cell + 1 else -1
        DOWN -> if (cell < capacity - cols) cell + cols else -1
        LEFT -> if (cell % cols > 0) cell - 1 else -1
        else -> -1
    }
    fun legal(action: Int): Boolean {
        if (length > 1 && action == (direction + 2) % 4) return false
        val n = next(head, action)
        return n >= 0 && (!occupied[n] || (n == tail && n != food))
    }
    /** Returns food gain, 0 for movement, -1 for death. */
    fun step(action: Int): Int {
        if (ended) return 0
        if (hunger >= 500) return die("HUNGER")
        // Manual reversals are ignored, but legal turns into obstacles are NOT silently ignored.
        if (action in 0..3 && !(length > 1 && action == (direction + 2) % 4)) direction = action
        val n = next(head, direction)
        if (n < 0) return die("WALL")
        val ate = n == food
        if (occupied[n] && !(n == tail && !ate)) return die("SELF")
        if (!ate) occupied[tail] = false
        first = (first + capacity - 1) % capacity; ring[first] = n; occupied[n] = true; steps++
        if (ate) {
            length++; val gain = 10 + combo.coerceAtMost(30) * 3 + length
            score += gain; combo++; hunger = (hunger * 0.35f).toInt(); foods++
            if (length == capacity) { food = -1; ended = true; cause = "WIN" } else placeFood()
            return gain
        }
        hunger++; combo = (combo - 1).coerceAtLeast(0)
        return 0
    }
    private fun die(why: String): Int { ended = true; cause = why; return -1 }
    private fun placeFood() {
        var target = rng.nextInt(capacity - length)
        for (i in 0 until capacity) if (!occupied[i]) { if (target-- == 0) { food = i; return } }
    }
    fun saveState(): IntArray = intArrayOf(direction, food, score, combo, hunger, steps, foods,
        if (ended) 1 else 0, length) + IntArray(length) { cellAt(it) }
    fun restoreState(state: IntArray): Boolean {
        if (state.size < 10) return false
        val n = state[8]
        if (n !in 1..capacity || state.size != 9 + n || state[0] !in 0..3) return false
        val cells = state.copyOfRange(9, state.size)
        if (cells.any { it !in 0 until capacity } || cells.distinct().size != n) return false
        if (cells.asList().zipWithNext().any { (a,b) -> (0..3).none { next(a,it) == b } }) return false
        if (n < capacity && (state[1] !in 0 until capacity || state[1] in cells)) return false
        if (state.slice(2..6).any { it < 0 }) return false
        first = 0; length = n; occupied.fill(false)
        cells.forEachIndexed { i,v -> ring[i] = v; occupied[v] = true }
        direction = state[0]; food = state[1]; score = state[2]; combo = state[3]
        hunger = state[4]; steps = state[5]; foods = state[6]; ended = state[7] == 1
        cause = if (ended) if (n == capacity) "WIN" else "RESTORED" else ""
        return true
    }
    companion object { const val UP=0; const val RIGHT=1; const val DOWN=2; const val LEFT=3 }
}
