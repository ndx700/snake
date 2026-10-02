package com.example.snake

import android.content.Context
import android.graphics.*
import android.media.AudioAttributes
import android.media.AudioFormat
import android.media.AudioManager
import android.media.AudioTrack
import android.media.ToneGenerator
import android.os.Build
import android.os.Bundle
import android.os.Parcelable
import android.os.VibrationEffect
import android.os.Vibrator
import android.os.VibratorManager
import android.util.AttributeSet
import android.util.Log
import android.view.Choreographer
import android.view.MotionEvent
import android.view.View
import java.io.BufferedInputStream
import java.io.BufferedOutputStream
import java.io.DataInputStream
import java.io.DataOutputStream
import java.io.FileInputStream
import java.io.FileOutputStream
import java.util.ArrayDeque
import java.util.concurrent.Callable
import java.util.concurrent.ExecutorService
import java.util.concurrent.Executors
import java.util.concurrent.Future
import kotlin.math.abs
import kotlin.math.max
import kotlin.math.min
import kotlin.random.Random

class SnakeView @JvmOverloads constructor(
    context: Context,
    attrs: AttributeSet? = null
) : View(context, attrs) {

    private val cols = 15
    private val rows = 15
    private val total = cols * rows

    private var cell = 0f
    private var ox = 0f
    private var oy = 0f

    private data class P(val x: Int, val y: Int)

    private data class Candidate(
        val d: P, val score: Float, val reason: String, val legal: Boolean,
        val regionScore: Float = 0f, val mobilityScore: Float = 0f,
        val tailScore: Float = 0f, val foodScore: Float = 0f,
        val edgeScore: Float = 0f, val spaceScore: Float = 0f,
        val region: Int = 0, val mobility: Int = 0,
        val tailOk: Boolean = false, val foodDist: Int = -1,
        val ate: Boolean = false, val qValue: Float = 0f
    )

    private data class Snapshot(
        var strategy: String = "V2 AUTO", var reason: String = "初始化",
        var danger: Int = 1, var region: Int = 1, var spaceRatio: Float = 1f,
        var tailReachable: Boolean = false, var foodReachable: Boolean = false,
        var foodDistance: Int = -1, var hunger: Int = 0, var chosen: P = P(0, 0),
        var candidates: List<Candidate> = emptyList(),
        var depth: Int = 0, var nodes: Int = 0, var hungerFactor: Float = 1f,
        var regionWeight: Float = 11f, var strategyId: Int = -1,
        var qValue: Float = 0f, var nVisits: Int = 0,
        var forceEatActive: Boolean = false, var forceEatSafe: Boolean = false,
        var safeFollowMode: Boolean = false
    )

    private data class Sim(val body: ArrayDeque<P>, val ate: Boolean)
    private data class Particle(var x: Float, var y: Float, var vx: Float, var vy: Float, var life: Float, val color: Int)
    private data class FloatText(var x: Float, var y: Float, var life: Float, val text: String)

    private data class BeamNode(
        val body: ArrayDeque<P>,
        val dir: P,
        val food: P,
        val score: Float,
        val steps: Int,
        val ateFood: Boolean,
        val dead: Boolean,
        val loopPenalty: Float,
        val firstAction: P,
        val recentHeadCells: IntArray
    )

    private val snake = ArrayDeque<P>()
    private val queue = ArrayDeque<P>()
    private val dirs = listOf(P(0, -1), P(0, 1), P(-1, 0), P(1, 0))

    private var dir = P(1, 0)
    private var food = P(5, 5)
    private var score = 0
    private var highScore = 0
    private var money = 0
    private var gameOver = false
    private var running = false
    private var aiMode = 1
    private var forcedStrategy = -1

    private var gameSpeed = 220L
    private val gameSpeedMin = 45L
    private val gameSpeedStart = 220L
    private var accumulator = 0L
    private var lastFrame = 0L
    private var combo = 0
    private var hunger = 0
    private var lastFreeRegion = 0f
    private var deathCause = "无"
    private var lastDeathInfo = ""
    private var ai = Snapshot(chosen = dir)

    private val sharedLock = Any()
    private val evolveLock = Any()

    private val POPULATION_SIZE = 50
    @Volatile private var generation = 0
    private val population = MutableList(POPULATION_SIZE) { TinyBrain() }
    @Volatile private var currentAgentIndex = 0
    private var completedAgents = 0
    private val currentScores = FloatArray(POPULATION_SIZE)
    @Volatile private var qWeight = 1.0f
    @Volatile private var nnWeight = 0.0f
    @Volatile private var bestScoreThisGen = 0f
    @Volatile private var bestScoreAllTime = 0f
    @Volatile private var deadEndPredicted = false
    @Volatile private var rolloutActive = false
    @Volatile private var rolloutSteps = 0
    @Volatile private var foodSpaceRatio = 1f
    @Volatile private var evolving = false
    @Volatile private var generationTransitioning = false

    @Volatile private var beamCalls = 0L
    @Volatile private var beamSuccess = 0L
    @Volatile private var beamSelected = 0L
    @Volatile private var beamTotalNodes = 0L
    @Volatile private var beamBestScore = 0f

    private val visitedStates = java.util.Collections.newSetFromMap(
        java.util.concurrent.ConcurrentHashMap<Int, Boolean>()
    )

    private class ThreadStatus {
        @Volatile var alive = false
        @Volatile var agentId = -1
        @Volatile var score = 0
        @Volatile var steps = 0
        @Volatile var phase = "空闲"
    }
    private val threadStatus = Array(8) { ThreadStatus() }

    private class EvoRecord(
        val gen: Int, val bestScore: Float,
        val eliteN: Int, val crossN: Int, val breedN: Int,
        val personality: String, val deaths: IntArray, val timestamp: Long
    )
    private val evoHistory = java.util.concurrent.ConcurrentLinkedDeque<EvoRecord>()

    private val completedAgentIds = HashSet<Int>()
    private val agentCompleted = BooleanArray(POPULATION_SIZE)
    @Volatile private var generationToken = 0L
    @Volatile private var uniqueCompletedAgents = 0

    private enum class V3Goal(val label: String, val short: String, val color: Int) {
        GET_FOOD("获取食物", "食", Color.rgb(46, 204, 113)),
        PRESERVE_SPACE("保持空间", "空", Color.rgb(52, 152, 219)),
        REACH_TAIL("追踪尾巴", "尾", Color.rgb(155, 89, 182)),
        ESCAPE_DANGER("逃离危险", "危", Color.rgb(231, 76, 60)),
        BREAK_LOOP("打破循环", "循", Color.rgb(241, 196, 15)),
        SURVIVE("极限求生", "生", Color.rgb(230, 126, 34))
    }

    private data class V3Lesson(
        var badAction: Int, var cause: String, var penalty: Float,
        var confidence: Float, var occurrences: Int, var altAction: Int
    )

    private class V3FailureMemory(private val capacity: Int = 8000) {
        private val memory = LinkedHashMap<Long, V3Lesson>()

        @Synchronized
        fun remember(ctx: Long, action: Int, cause: String, penalty: Float, alt: Int): V3Lesson {
            val old = memory[ctx]
            return if (old == null) {
                val l = V3Lesson(action, cause, penalty, 0.30f, 1, alt)
                memory[ctx] = l
                if (memory.size > capacity) memory.remove(memory.keys.first())
                l
            } else {
                old.occurrences++
                old.cause = cause
                old.penalty = max(old.penalty, penalty)
                old.confidence = min(0.95f, 0.40f + old.occurrences * 0.18f)
                if (alt >= 0) old.altAction = alt
                old
            }
        }

        @Synchronized
        fun penaltyFor(ctx: Long, action: Int): Float {
            val l = memory[ctx] ?: return 0f
            if (l.badAction != action) return 0f
            return l.penalty * l.confidence
        }

        @Synchronized
        fun hardLesson(ctx: Long, action: Int): Boolean {
            val l = memory[ctx] ?: return false
            return l.badAction == action && l.occurrences >= 3 && l.confidence >= 0.70f
        }

        @Synchronized
        fun worstLessonText(): String {
            var best: V3Lesson? = null
            for (l in memory.values) if (best == null || l.occurrences > best!!.occurrences) best = l
            val b = best ?: return "暂无教训"
            return "死因=${b.cause} 重复${b.occurrences}次 置信=${"%.2f".format(b.confidence)}"
        }

        @Synchronized fun size(): Int = memory.size
        @Synchronized fun clear() = memory.clear()
    }

    private class V3StrategyGenome {
        var foodPriority = 1.00f
        var spacePriority = 1.25f
        var tailPriority = 0.90f
        var dangerAversion = 1.40f
        var loopAversion = 0.80f
        var hungerUrgency = 0.80f
        private var backup = floatArrayOf(1.00f, 1.25f, 0.90f, 1.40f, 0.80f, 0.80f)

        fun snapshot() { backup = floatArrayOf(foodPriority, spacePriority, tailPriority, dangerAversion, loopAversion, hungerUrgency) }
        fun revert() {
            foodPriority = backup[0]; spacePriority = backup[1]; tailPriority = backup[2]
            dangerAversion = backup[3]; loopAversion = backup[4]; hungerUrgency = backup[5]
        }
        fun normalize() {
            foodPriority = foodPriority.coerceIn(0.4f, 2.2f)
            spacePriority = spacePriority.coerceIn(0.6f, 2.4f)
            tailPriority = tailPriority.coerceIn(0.4f, 2.0f)
            dangerAversion = dangerAversion.coerceIn(0.8f, 2.6f)
            loopAversion = loopAversion.coerceIn(0.3f, 2.2f)
            hungerUrgency = hungerUrgency.coerceIn(0.4f, 2.0f)
        }
        fun selfAdjust(cause: String) {
            when (cause) {
                "SELF" -> { spacePriority += 0.05f; dangerAversion += 0.04f; tailPriority += 0.02f }
                "TRAP" -> { dangerAversion += 0.05f; spacePriority += 0.03f }
                "WALL" -> { dangerAversion += 0.03f; tailPriority += 0.03f }
                "HUNGER" -> { hungerUrgency += 0.04f; foodPriority += 0.03f; spacePriority -= 0.02f }
            }
            normalize()
        }
        fun evolve() {
            val sigma = 0.06f
            fun noise() = Random.nextFloat() * 2f * sigma - sigma
            foodPriority += noise(); spacePriority += noise(); tailPriority += noise()
            dangerAversion += noise(); loopAversion += noise(); hungerUrgency += noise()
            normalize()
        }
        fun values(): FloatArray = floatArrayOf(foodPriority, spacePriority, tailPriority, dangerAversion, loopAversion, hungerUrgency)
    }

    @Volatile private var v3FusionEnabled = true
    @Volatile private var v3Goal: V3Goal = V3Goal.GET_FOOD
    @Volatile private var v3LayerActive: Int = 4
    @Volatile private var v3LayerWhy: String = "V4融合待命"
    @Volatile private var v3Regret: Float = 0f
    @Volatile private var v3LessonFires: Int = 0
    @Volatile private var v3LoopHits: Int = 0

    private val v3GoalCounter = IntArray(V3Goal.values().size)
    private val v3RecentHeads = ArrayDeque<Int>()
    private val v3Memory = V3FailureMemory(8000)
    private val v3Genome = V3StrategyGenome()
    private var v3GenomeBest = 0f
    private var v3LessonFlash = 0f
    private val v3CtxSalt = 0x5157L
    private val v3TrainCtxSalt = 0x5157L

    fun setV3FusionEnabled(on: Boolean) { v3FusionEnabled = on; v3LayerWhy = if (on) "V4融合已接管" else "V2基线模式" }
    fun isV3FusionEnabled(): Boolean = v3FusionEnabled

    private fun v3ActionIndexOf(d: P): Int = dirs.indexOfFirst { it == d }
    private fun v3RecordHead() {
        val h = snake.firstOrNull() ?: return
        v3RecentHeads.addLast(h.y * cols + h.x)
        while (v3RecentHeads.size > 24) v3RecentHeads.removeFirst()
    }
    private fun v3LoopRisk(): Boolean {
        if (v3RecentHeads.size < 8) return false
        val last8 = if (v3RecentHeads.size > 8) v3RecentHeads.drop(v3RecentHeads.size - 8) else v3RecentHeads
        return last8.toSet().size <= 5
    }
    private fun v3SelectGoal(): V3Goal {
        if (legalDirectionMask() == 0) return V3Goal.ESCAPE_DANGER
        if (v3LoopRisk()) { v3LoopHits++; return V3Goal.BREAK_LOOP }
        val region = freeRegion(snake)
        val ratio = region.toFloat() / max(1, snake.size)
        val danger = calculateDanger()
        if (danger >= 4) return V3Goal.ESCAPE_DANGER
        if (ratio < 1.05f) return V3Goal.PRESERVE_SPACE
        if (snake.size >= total * 0.45f && tailReachable(snake)) return V3Goal.REACH_TAIL
        if (snake.size >= total * 0.55f) return V3Goal.SURVIVE
        return V3Goal.GET_FOOD
    }
    private fun legalDirectionMask(): Int {
        var m = 0
        val head = snake.firstOrNull() ?: return 0
        dirs.forEachIndexed { i, d ->
            val nx = head.x + d.x; val ny = head.y + d.y
            if (nx in 0 until cols && ny in 0 until rows && !snake.contains(P(nx, ny))) m = m or (1 shl i)
        }
        return m
    }

    private fun v3ContextHash(): Long {
        val head = snake.firstOrNull() ?: return 0L
        val regionBucket = (freeRegion(snake) / 4).coerceIn(0, 60)
        val lenBucket = (snake.size / 8).coerceIn(0, 30)
        val foodDxBucket = ((food.x - head.x) / 3).coerceIn(-5, 5)
        val foodDyBucket = ((food.y - head.y) / 3).coerceIn(-5, 5)
        val headingBucket = directionIndex(dir)
        val dangerBucket = calculateDanger().coerceIn(1, 5)
        val tailBucket = if (tailReachable(snake)) 1 else 0
        var h = 1125899906842597L
        h = h * 31 + head.x; h = h * 31 + head.y
        h = h * 31 + foodDxBucket; h = h * 31 + foodDyBucket
        h = h * 31 + headingBucket; h = h * 31 + dangerBucket
        h = h * 31 + regionBucket; h = h * 31 + lenBucket; h = h * 31 + tailBucket
        return h xor v3CtxSalt
    }

    private fun v3PostCheck(originalDir: P, legal: List<Candidate>, state: Int): P {
        if (!v3FusionEnabled || legal.size <= 1) return originalDir
        val best = legal.firstOrNull { it.d == originalDir } ?: return originalDir
        val ctx = v3ContextHash()

        if (v3Memory.hardLesson(ctx, v3ActionIndexOf(originalDir))) {
            val alt = legal
                .filter { it.d != originalDir && v3ActionIndexOf(it.d) >= 0 && !v3Memory.hardLesson(ctx, v3ActionIndexOf(it.d)) }
                .maxByOrNull { it.region * v3Genome.spacePriority * 10f + (if (it.tailOk) v3Genome.tailPriority * 40f else 0f) }
            if (alt != null && alt.tailOk && alt.region >= best.region * 0.8f) {
                Log.d(LOG_TAG, "L5 TRIGGERED! Cause: 防止重蹈覆辙")
                v3LayerActive = 5; v3LayerWhy = "L5反事实：阻止重蹈覆辙"
                v3LessonFires++
                return alt.d
            }
        }

        if (v3LoopRisk()) {
            val alt = legal
                .filter { it.d != originalDir && it.tailOk }
                .maxByOrNull { it.region * v3Genome.spacePriority + v3Genome.loopAversion * 8f }
            if (alt != null && alt.tailOk && alt.region >= best.region * 0.8f) {
                Log.d(LOG_TAG, "L6 TRIGGERED! Cause: 打破循环")
                v3LayerActive = 6; v3LayerWhy = "L6基因：循环厌恶接管"
                v3LoopHits++
                return alt.d
            }
        }
        return originalDir
    }

    private fun v3AnalyzeDeath(cause: String) {
        if (!v3FusionEnabled) return
        val chosenAction = v3ActionIndexOf(ai.chosen)
        if (chosenAction < 0) return
        val ctx = v3ContextHash()
        val alt = ai.candidates
            .filter { it.legal && it.d != ai.chosen && v3ActionIndexOf(it.d) >= 0 }
            .maxByOrNull { it.region * 10f + (if (it.tailOk) 50f else 0f) }
        val severity = when (cause) {
            "SELF" -> 1.0f; "TRAP" -> 0.9f; "WALL" -> 0.85f; "HUNGER" -> 0.35f; else -> 0.5f
        }
        val lesson = v3Memory.remember(ctx, chosenAction, cause, severity, v3ActionIndexOf(alt?.d ?: ai.chosen))
        v3Regret = severity * lesson.confidence
        v3LessonFires++; v3LessonFlash = 1f
        v3Genome.selfAdjust(cause)
    }

    private fun v3TrainRecordLesson(cause: String, head: P, tailOk: Boolean, len: Int, action: Int) {
        if (!v3FusionEnabled || action < 0) return
        var h = 1125899906842597L
        h = h * 31 + head.x; h = h * 31 + head.y
        h = h * 31 + len; h = h * 31 + (if (tailOk) 1 else 0)
        val ctx = h xor v3TrainCtxSalt
        val severity = when (cause) {
            "SELF" -> 0.9f; "TRAP" -> 0.8f; "WALL" -> 0.7f; else -> 0.3f
        }
        v3Memory.remember(ctx, action, cause, severity, -1)
    }

    private fun v3EvolveGenome() {
        synchronized(v3Genome) {
            v3Genome.snapshot()
            val before = v3GenomeBest
            v3Genome.evolve()
            if (before > 0f && bestScoreAllTime < before) v3Genome.revert()
            else v3GenomeBest = bestScoreAllTime
        }
    }

    private var wRegion = 11f
    private var wMobility = 35f
    private var wTailGood = 180f
    private var wTailBad = -250f
    private var wFoodNear = 300f
    private var wFoodAte = 850f
    private var wEdge = 55f
    private var wSpace = 30f

    private val wRegion0 = 11f
    private val wMobility0 = 35f
    private val wTailGood0 = 180f
    private val wTailBad0 = -250f
    private val wFoodNear0 = 300f
    private val wFoodAte0 = 850f
    private val wEdge0 = 55f
    private val wSpace0 = 30f

    private var aggression = 1.15f
    private var safetyMargin = 1.08f
    private var shortcutBonus = 0.90f

    private var deathWall = 0
    private var deathSelf = 0
    private var deathTrap = 0
    private var totalGames = 0
    private var lastLearnAction = "初始化"
    private val recentScores = ArrayDeque<Int>()
    private var bestRecentScore = 0
    private var generationsWithoutImprovement = 0
    private var previousGenerationBest = Float.NEGATIVE_INFINITY

    private companion object {
        const val V2_FOOD_DIR = 4
        const val V2_DANGER = 16
        const val V2_MOBILITY = 5
        const val V2_SPACE = 4
        const val V2_HUNGER = 5
        const val V2_LENGTH = 4
        const val V2_TAIL = 2
        const val V2_HEADING = 1
        const val V2_STATE_COUNT = V2_FOOD_DIR * V2_DANGER * V2_MOBILITY * V2_SPACE * V2_HUNGER * V2_LENGTH * V2_TAIL * V2_HEADING
        const val V2_ACTIONS = 4
        const val V2_Q_SIZE = V2_STATE_COUNT * V2_ACTIONS
        const val V2_LOCKS = 64
        const val GAMMA = 0.94f
        const val ALPHA_FAST = 0.18f
        const val ALPHA_NORMAL = 0.055f
        const val EPS_START = 0.22f
        const val EPS_MIN = 0.015f
        const val REWARD_STEP = -0.05f
        const val REWARD_FOOD = 10.0f
        const val REWARD_TAIL = 0.55f
        const val REWARD_DANGER = -0.30f
        const val REWARD_SPACE_DELTA = 0.08f
        const val DEATH_WALL = -14.0f
        const val DEATH_SELF = -18.0f
        const val DEATH_TRAP = -20.0f
        const val DEATH_HUNGER = -12.0f
        const val LOG_TAG = "SnakeTrain"
        const val HEARTBEAT_TIMEOUT_MS = 7_200_000L

        const val BEAM_ENABLED = true
        const val BEAM_WIDTH = 3
        const val BEAM_DEPTH_SHORT = 5
        const val BEAM_DEPTH_LONG = 7
        const val BEAM_MIN_LENGTH = 10
        const val BEAM_MAX_NODES = 80
        const val BEAM_WEIGHT = 0.30f
        const val BEAM_FOOD_WEIGHT = 1.0f
        const val BEAM_SPACE_WEIGHT = 1.2f
        const val BEAM_TAIL_WEIGHT = 1.1f
        const val BEAM_SURVIVAL_WEIGHT = 2.0f
        const val BEAM_DANGER_WEIGHT = 1.5f
        const val BEAM_LOOP_WEIGHT = 0.8f
        const val BEAM_LONG_LENGTH = 35
        const val BEAM_DEPTH_MAX = 8
    }

    private val qV2 = FloatArray(V2_Q_SIZE)
    private val qTarget = FloatArray(V2_Q_SIZE)
    private val nV2 = IntArray(V2_Q_SIZE)
    @Volatile private var trainingRunId = 0L
    private val trainingLifecycleLock = Any()
    private val targetLock = Any()
    private val targetUpdateCounter = java.util.concurrent.atomic.AtomicInteger(0)

    private fun isTrainingRunActive(runId: Long): Boolean = trainActive && trainingRunId == runId

    private val qLocks = Array(V2_LOCKS) { Any() }
    @Volatile private var v2LearningSteps = 0L
    @Volatile private var v2Episodes = 0L
    @Volatile private var v2Epsilon = EPS_START
    private var lastV2State = -1
    private var lastV2Action = -1

    private fun qIndex(state: Int, action: Int): Int = state * V2_ACTIONS + action
    private fun qLock(index: Int): Any = qLocks[index and (V2_LOCKS - 1)]
    private fun qStateLock(state: Int): Any = qLocks[state and (V2_LOCKS - 1)]

    private fun qRead(state: Int, action: Int): Float {
        if (state !in 0 until V2_STATE_COUNT || action !in 0 until V2_ACTIONS) return 0f
        return synchronized(qLock(state)) { qV2[qIndex(state, action)] }
    }
    private fun qVisit(state: Int, action: Int): Int {
        if (state !in 0 until V2_STATE_COUNT || action !in 0 until V2_ACTIONS) return 0
        return synchronized(qLock(state)) { nV2[qIndex(state, action)] }
    }
    private fun qMax(state: Int, legalMask: Int = 15): Float {
        if (state !in 0 until V2_STATE_COUNT) return 0f
        var bestAction = -1; var bestQ = -Float.MAX_VALUE
        synchronized(qLock(state)) {
            for (a in 0 until 4) {
                if ((legalMask and (1 shl a)) == 0) continue
                val v = qV2[qIndex(state, a)]
                if (v > bestQ) { bestQ = v; bestAction = a }
            }
            if (bestAction < 0) return 0f
            synchronized(targetLock) { return qTarget[qIndex(state, bestAction)] }
        }
    }

    private data class Experience(
        val state: Int, val action: Int, val reward: Float,
        val nextState: Int, val nextMask: Int, val terminal: Boolean,
        val tdError: Float = 0f
    )
    private val replayBuffer = ArrayList<Experience>(5000)
    private val REPLAY_CAPACITY = 5000

    private fun qUpdate(state: Int, action: Int, reward: Float, nextState: Int, nextMask: Int, terminal: Boolean) {
        if (state !in 0 until V2_STATE_COUNT || action !in 0 until V2_ACTIONS) return
        visitedStates.add(state)
        val effectiveReward = reward
        val idx = qIndex(state, action)
        val nextBest = if (terminal) 0f else qMax(nextState, nextMask)
        val oldValue = synchronized(qStateLock(state)) { qV2[idx] }
        val tdErr = if (terminal) effectiveReward - oldValue else effectiveReward + GAMMA * nextBest - oldValue
        synchronized(replayBuffer) {
            replayBuffer.add(Experience(state, action, effectiveReward, nextState, nextMask, terminal, tdErr))
            if (replayBuffer.size > REPLAY_CAPACITY) replayBuffer.removeAt(0)
        }
        synchronized(qStateLock(state)) {
            val visits = nV2[idx]
            val alpha = if (visits < 12) ALPHA_FAST else ALPHA_NORMAL
            val target = if (terminal) effectiveReward else effectiveReward + GAMMA * nextBest
            val old = qV2[idx]
            val updated = old + alpha * (target - old)
            qV2[idx] = updated.coerceIn(-10f, 10f)
            nV2[idx] = if (visits < Int.MAX_VALUE) visits + 1 else visits
        }
        synchronized(replayBuffer) {
            if (replayBuffer.size > 10) repeat(2) {
                val e = replayBuffer[Random.nextInt(replayBuffer.size)]
                evoUpdate(e.state, e.action, e.reward, e.nextState, e.nextMask, e.terminal)
            }
        }
        v2LearningSteps++
        val cnt = targetUpdateCounter.incrementAndGet()
        if (cnt >= 50 && targetUpdateCounter.compareAndSet(cnt, 0)) {
            synchronized(targetLock) {
                for (i in qTarget.indices) qTarget[i] = qTarget[i] + 0.01f * (qV2[i] - qTarget[i])
            }
        }
    }

    private fun evoUpdate(state: Int, action: Int, reward: Float, nextState: Int, nextMask: Int, terminal: Boolean) {
        if (state !in 0 until V2_STATE_COUNT || action !in 0 until V2_ACTIONS) return
        val idx = qIndex(state, action)
        val nextBest = if (terminal) 0f else qMax(nextState, nextMask)
        synchronized(qStateLock(state)) {
            val visits = nV2[idx]
            val alpha = if (visits < 12) ALPHA_FAST else ALPHA_NORMAL
            val target = if (terminal) reward else reward + GAMMA * nextBest
            val old = qV2[idx]
            val updated = old + alpha * (target - old)
            qV2[idx] = updated.coerceIn(-10f, 10f)
            nV2[idx] = if (visits < Int.MAX_VALUE) visits + 1 else visits
        }
    }

    private fun currentEpsilon(): Float {
        if (!trainingMode && !reinforceTraining) return 0f
        val e = v2Epsilon
        if (v2LearningSteps > 0L && v2LearningSteps % 4096L == 0L) v2Epsilon = max(EPS_MIN, v2Epsilon * 0.985f)
        return e
    }

    private inner class TinyBrain {
        var w1 = FloatArray(8 * 32) { Random.nextFloat() * 2f - 1f }
        var w2 = FloatArray(32 * 16) { Random.nextFloat() * 2f - 1f }
        var w3 = FloatArray(16 * 4) { Random.nextFloat() * 2f - 1f }

        fun think(inputs: FloatArray): FloatArray {
            val h1 = FloatArray(32)
            for (i in 0 until 32) { var s = 0f; for (j in 0 until 8) s += inputs[j] * w1[j * 32 + i]; h1[i] = max(0f, s) }
            val h2 = FloatArray(16)
            for (i in 0 until 16) { var s = 0f; for (j in 0 until 32) s += h1[j] * w2[j * 16 + i]; h2[i] = max(0f, s) }
            val outputs = FloatArray(4)
            for (i in 0 until 4) { var s = 0f; for (j in 0 until 16) s += h2[j] * w3[j * 4 + i]; outputs[i] = s }
            return outputs
        }

        fun copyFrom(src: TinyBrain) {
            System.arraycopy(src.w1, 0, w1, 0, w1.size)
            System.arraycopy(src.w2, 0, w2, 0, w2.size)
            System.arraycopy(src.w3, 0, w3, 0, w3.size)
        }
        fun breed(child: TinyBrain) {
            val mut = if (generation < 10) 0.18f else if (generation < 30) 0.10f else 0.05f
            for (i in w1.indices) child.w1[i] = w1[i] + (Random.nextFloat() - 0.5f) * mut
            for (i in w2.indices) child.w2[i] = w2[i] + (Random.nextFloat() - 0.5f) * mut
            for (i in w3.indices) child.w3[i] = w3[i] + (Random.nextFloat() - 0.5f) * mut
        }
        fun crossover(other: TinyBrain, child: TinyBrain, dynamicMut: Float) {
            val s1 = w1.size / 2; val s2 = w2.size / 2; val s3 = w3.size / 2
            System.arraycopy(w1, 0, child.w1, 0, s1)
            System.arraycopy(other.w1, s1, child.w1, s1, w1.size - s1)
            System.arraycopy(w2, 0, child.w2, 0, s2)
            System.arraycopy(other.w2, s2, child.w2, s2, w2.size - s2)
            System.arraycopy(w3, 0, child.w3, 0, s3)
            System.arraycopy(other.w3, s3, child.w3, s3, w3.size - s3)
            val baseMut = if (generation < 10) 0.12f else 0.06f
            val mut = max(baseMut, dynamicMut.coerceIn(0.06f, 0.30f))
            for (i in child.w1.indices) child.w1[i] += (Random.nextFloat() - 0.5f) * mut
            for (i in child.w2.indices) child.w2[i] += (Random.nextFloat() - 0.5f) * mut
            for (i in child.w3.indices) child.w3[i] += (Random.nextFloat() - 0.5f) * mut
        }
    }

    private fun evolveNextGeneration() {
        evolving = true
        try {
            v3EvolveGenome()
            generation++
            val scoresCopy = synchronized(sharedLock) { currentScores.copyOf() }
            val sortedIndices = (0 until POPULATION_SIZE).filter { !scoresCopy[it].isNaN() }.sortedByDescending { scoresCopy[it] }
            val bestBrains = if (sortedIndices.isNotEmpty()) {
                sortedIndices.take(minOf(10, sortedIndices.size)).map { TinyBrain().also { c -> c.copyFrom(population[it]) } }
            } else {
                (0 until minOf(10, POPULATION_SIZE)).map { TinyBrain().also { c -> c.copyFrom(population[it]) } }
            }
            if (bestBrains.isEmpty()) return

            val generationBest = if (sortedIndices.isNotEmpty()) scoresCopy[sortedIndices[0]] else 0f
            if (generationBest > previousGenerationBest + 0.001f) generationsWithoutImprovement = 0
            else generationsWithoutImprovement++
            previousGenerationBest = max(previousGenerationBest, generationBest)
            if (generationBest > bestScoreThisGen) bestScoreThisGen = generationBest
            if (generationBest > bestScoreAllTime) bestScoreAllTime = generationBest

            val dynamicMut = when {
                generationsWithoutImprovement >= 20 -> 0.30f
                generationsWithoutImprovement >= 10 -> 0.22f
                generationsWithoutImprovement >= 5 -> 0.16f
                else -> 0.12f
            }

            val eliteCount = 10
            val crossoverCount = 25
            val mutatedEliteCount = 10
            val immigrantCount = 5

            for (i in 0 until POPULATION_SIZE) {
                try {
                    when {
                        i < eliteCount -> population[i] = TinyBrain().also { it.copyFrom(bestBrains[i % bestBrains.size]) }
                        i < eliteCount + crossoverCount -> {
                            val p1 = bestBrains[Random.nextInt(bestBrains.size)]
                            var p2 = bestBrains[Random.nextInt(bestBrains.size)]
                            if (bestBrains.size > 1) while (p2 === p1) p2 = bestBrains[Random.nextInt(bestBrains.size)]
                            val child = TinyBrain(); p1.crossover(p2, child, dynamicMut); population[i] = child
                        }
                        i < eliteCount + crossoverCount + mutatedEliteCount -> {
                            val parent = bestBrains[Random.nextInt(bestBrains.size)]
                            val child = TinyBrain(); parent.breed(child); population[i] = child
                        }
                        else -> population[i] = TinyBrain()
                    }
                } catch (t: Throwable) { Log.e(LOG_TAG, "breed agent=$i failed", t); population[i] = TinyBrain() }
            }

            synchronized(sharedLock) { for (i in 0 until POPULATION_SIZE) currentScores[i] = 0f }

            val personality = when {
                v3Genome.dangerAversion > 1.8f && v3Genome.spacePriority > 1.6f -> "稳健保守型"
                v3Genome.foodPriority > 1.6f && v3Genome.hungerUrgency > 1.4f -> "激进捕食型"
                v3Genome.loopAversion > 1.6f -> "反循环型"
                v3Genome.tailPriority > 1.5f -> "追尾保命型"
                else -> "均衡探索型"
            }
            evoHistory.addLast(EvoRecord(generation, generationBest, eliteCount, crossoverCount,
                mutatedEliteCount + immigrantCount, personality,
                intArrayOf(deathWall, deathSelf, deathTrap), System.currentTimeMillis()))
            while (evoHistory.size > 24) evoHistory.pollFirst()

            val baseRatio = (generation / 30f).coerceIn(0f, 0.45f)
            val scoreBonus = (generationBest / 25000f).coerceIn(0f, 0.10f)
            nnWeight = (baseRatio + scoreBonus).coerceIn(0f, 0.50f)
            qWeight = (1.0f - nnWeight).coerceIn(0.50f, 1.0f)
            bestScoreThisGen = 0f

            Log.d(LOG_TAG, "EVOLVE gen=$generation best=$generationBest nnW=$nnWeight qW=$qWeight stall=$generationsWithoutImprovement")
            Thread { try { saveTrainingState() } catch (_: Exception) {} }.apply { isDaemon = true; start() }
        } catch (t: Throwable) { Log.e(LOG_TAG, "evolveNextGeneration failed", t) }
        finally { evolving = false }
    }

    private fun buildInputs(head: P, target: P, currentBody: ArrayDeque<P>): FloatArray {
        val inputs = FloatArray(8)
        inputs[0] = if (isSafeForBody(head.x, head.y - 1, currentBody)) 0f else 1f
        inputs[1] = if (isSafeForBody(head.x, head.y + 1, currentBody)) 0f else 1f
        inputs[2] = if (isSafeForBody(head.x - 1, head.y, currentBody)) 0f else 1f
        inputs[3] = if (isSafeForBody(head.x + 1, head.y, currentBody)) 0f else 1f
        inputs[4] = if (target.y < head.y) 1f else 0f
        inputs[5] = if (target.y > head.y) 1f else 0f
        inputs[6] = if (target.x < head.x) 1f else 0f
        inputs[7] = if (target.x > head.x) 1f else 0f
        return inputs
    }

    private fun isSafeForBody(nx: Int, ny: Int, body: ArrayDeque<P>): Boolean {
        val p = P(nx, ny)
        if (!inside(p)) return false
        if (body.contains(p) && p != body.last()) return false
        return true
    }

    var onScoreChanged: ((Int) -> Unit)? = null
    var onMoneyChanged: ((Int) -> Unit)? = null

    private val prefs = context.getSharedPreferences("snake_prefs", Context.MODE_PRIVATE)

    private val vibrator: Vibrator? = if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
        (context.getSystemService(Context.VIBRATOR_MANAGER_SERVICE) as? VibratorManager)?.defaultVibrator
    } else {
        @Suppress("DEPRECATION") context.getSystemService(Context.VIBRATOR_SERVICE) as? Vibrator
    }

    private val toneGen: ToneGenerator? = try { ToneGenerator(AudioManager.STREAM_MUSIC, 85) } catch (_: Throwable) { null }

    private var bgm: BgmPlayer? = null
    private var bodyColor = Color.rgb(46, 204, 113)
    private var headColor = Color.rgb(39, 174, 96)
    private var bgColor = Color.BLACK
    private var gridColor = Color.CYAN
    private var rainbowSkin = false
    private val hsv = IntArray(360) { Color.HSVToColor(floatArrayOf(it.toFloat(), 1f, 1f)) }
    private val particles = mutableListOf<Particle>()
    private val floats = mutableListOf<FloatText>()

    private val paint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val text = Paint(Paint.ANTI_ALIAS_FLAG)
    private val panel = Paint(Paint.ANTI_ALIAS_FLAG)
    private val border = Paint(Paint.ANTI_ALIAS_FLAG)
    private val gridPaint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val snakePaint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val headPaint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val foodPaint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val barPaint = Paint(Paint.ANTI_ALIAS_FLAG)

    private var flash = 0f
    private val hungerKillLimit = 500
    private val safeFollowLength = 32
    private var restartCountdown = 0L

    private var trainingMode = false
    private var reinforceTraining = false

    @Volatile private var lastHeartbeat = 0L
    @Volatile private var watchDogThread: Thread? = null
    @Volatile private var watchdogRestartCount = 0

    private fun heartbeat() { lastHeartbeat = System.currentTimeMillis() }

    private fun startWatchDog() {
        stopWatchDog()
        lastHeartbeat = System.currentTimeMillis()
        watchDogThread = Thread {
            while (true) {
                try { Thread.sleep(1000) } catch (_: Exception) {}
                if (!reinforceTraining) continue
                val now = System.currentTimeMillis()
                if (now - lastHeartbeat > HEARTBEAT_TIMEOUT_MS) {
                    watchdogRestartCount++
                    try { restartTrainingSafely() } catch (_: Exception) {}
                    try { Thread.sleep(3000) } catch (_: Exception) {}
                }
            }
        }.also { it.priority = Thread.MIN_PRIORITY; it.start() }
    }

    private fun stopWatchDog() { watchDogThread?.interrupt(); watchDogThread = null }

    override fun onSaveInstanceState(): Parcelable? {
        val superState = super.onSaveInstanceState()
        val bundle = Bundle()
        bundle.putParcelable("super", superState)
        bundle.putBoolean("reinforceTraining", reinforceTraining)
        bundle.putBoolean("trainingMode", trainingMode)
        return bundle
    }

    override fun onRestoreInstanceState(state: Parcelable?) {
        if (state is Bundle) {
            val wasReinforce = state.getBoolean("reinforceTraining", false)
            trainingMode = state.getBoolean("trainingMode", false)
            super.onRestoreInstanceState(state.getParcelable("super"))
            if (wasReinforce) { startParallelTraining(resetCounters = false); startWatchDog() }
        } else super.onRestoreInstanceState(state)
    }

    private var renderSkipCounter = 0
    private val reinforceButtonRect = RectF()
    private var lastReinforceTap = 0L
    @Volatile private var trainActive = false
    private val trainThreads: MutableList<Thread> = mutableListOf()
    private val TRAIN_THREADS = 8

    private val aiPool: ExecutorService = run {
        val cores = Runtime.getRuntime().availableProcessors().coerceIn(4, 8)
        Executors.newFixedThreadPool(cores) { r -> Thread(r, "snake-ai").apply { isDaemon = true; priority = Thread.NORM_PRIORITY } }
    }

    private val tlVisited: ThreadLocal<BooleanArray> = ThreadLocal.withInitial { BooleanArray(cols * rows) }
    private val tlQueue: ThreadLocal<IntArray> = ThreadLocal.withInitial { IntArray(cols * rows) }

    private var aiStepStartNs = 0L
    private var aiStepBudgetNs = 15_000_000L

    private fun budgetFor(speedMs: Long): Long = when {
        speedMs >= 150L -> 35_000_000L
        speedMs >= 80L -> 18_000_000L
        speedMs >= 55L -> 12_000_000L
        else -> 8_000_000L
    }

    private fun hungerForceEat(): Int = when {
        snake.size < 20 -> 50; snake.size < 35 -> 70; snake.size < 55 -> 100; snake.size < 80 -> 140; else -> 200
    }

    private fun vibrateEat() {
        if (reinforceTraining || trainingMode) return
        vibrator?.let { try { if (Build.VERSION.SDK_INT >= 26) it.vibrate(VibrationEffect.createOneShot(18, VibrationEffect.DEFAULT_AMPLITUDE)) else { @Suppress("DEPRECATION") it.vibrate(18) } } catch (_: Throwable) {} }
    }

    private fun vibrateDeath() {
        if (reinforceTraining || trainingMode) return
        vibrator?.let { try { if (Build.VERSION.SDK_INT >= 26) it.vibrate(VibrationEffect.createOneShot(120, VibrationEffect.DEFAULT_AMPLITUDE)) else { @Suppress("DEPRECATION") it.vibrate(120) } } catch (_: Throwable) {} }
    }

    private fun playEatSound() {
        if (reinforceTraining || trainingMode) return
        try { toneGen?.startTone(ToneGenerator.TONE_PROP_BEEP, 55) } catch (_: Throwable) {}
    }

    private val frame = object : Choreographer.FrameCallback {
        override fun doFrame(ns: Long) {
            if (!running) return
            if (lastFrame == 0L) lastFrame = ns
            val dt = ((ns - lastFrame) / 1_000_000L).coerceAtMost(100L)
            lastFrame = ns
            if (reinforceTraining) { if ((++renderSkipCounter % 2) == 0) invalidate(); Choreographer.getInstance().postFrameCallback(this); return }
            if (gameOver) restartCountdown = 0L
            else {
                accumulator += dt
                var stepCount = 0
                val maxSteps = if (trainingMode) 10 else Int.MAX_VALUE
                while (accumulator >= gameSpeed && stepCount < maxSteps) {
                    updateGame()
                    if (gameOver && !trainingMode) break
                    accumulator -= gameSpeed
                    stepCount++
                }
                if (stepCount >= maxSteps) accumulator = 0L
            }
            updateEffects(dt / 16f)
            val shouldRender = if (trainingMode) (++renderSkipCounter % 2) == 0 else true
            if (shouldRender) invalidate()
            Choreographer.getInstance().postFrameCallback(this)
        }
    }

    init {
        highScore = prefs.getInt("high_score", 0)
        money = prefs.getInt("money", 0)
        trainingMode = prefs.getBoolean("training_mode", false)
        aggression = prefs.getFloat("learn_aggression", 1.15f)
        safetyMargin = prefs.getFloat("learn_safety", 1.08f)
        shortcutBonus = prefs.getFloat("learn_shortcut", 0.90f)
        wRegion = prefs.getFloat("w_region", wRegion0)
        wMobility = prefs.getFloat("w_mobility", wMobility0)
        wTailGood = prefs.getFloat("w_tail_good", wTailGood0)
        wTailBad = prefs.getFloat("w_tail_bad", wTailBad0)
        wFoodNear = prefs.getFloat("w_food_near", wFoodNear0)
        wFoodAte = prefs.getFloat("w_food_ate", wFoodAte0)
        wEdge = prefs.getFloat("w_edge", wEdge0)
        wSpace = prefs.getFloat("w_space", wSpace0)

        fun fixW(v: Float, base: Float): Float = v.coerceIn(base * 0.85f, base * 1.15f)
        wRegion = fixW(wRegion, wRegion0); wMobility = fixW(wMobility, wMobility0)
        wTailGood = fixW(wTailGood, wTailGood0); wFoodNear = fixW(wFoodNear, wFoodNear0)
        wFoodAte = fixW(wFoodAte, wFoodAte0); wEdge = fixW(wEdge, wEdge0)
        wSpace = fixW(wSpace, wSpace0)
        wTailBad = wTailBad.coerceIn(wTailBad0 * 1.15f, wTailBad0 * 0.85f)
        aggression = aggression.coerceIn(0.95f, 1.35f)
        safetyMargin = safetyMargin.coerceIn(1.0f, 1.20f)

        lastLearnAction = prefs.getString("last_learn_action", "初始化") ?: "初始化"

        v3Genome.foodPriority = prefs.getFloat("v3_g_food", 1.00f)
        v3Genome.spacePriority = prefs.getFloat("v3_g_space", 1.25f)
        v3Genome.tailPriority = prefs.getFloat("v3_g_tail", 0.90f)
        v3Genome.dangerAversion = prefs.getFloat("v3_g_danger", 1.40f)
        v3Genome.loopAversion = prefs.getFloat("v3_g_loop", 0.80f)
        v3Genome.hungerUrgency = prefs.getFloat("v3_g_hunger", 0.80f)
        v3Genome.normalize()

        v3LessonFires = prefs.getInt("v3_lesson_fires", 0)
        v3LoopHits = prefs.getInt("v3_loop_hits", 0)
        deathWall = prefs.getInt("stat_wall", 0)
        deathSelf = prefs.getInt("stat_self", 0)
        deathTrap = prefs.getInt("stat_trap", 0)
        totalGames = prefs.getInt("stat_total", 0)

        bgm = BgmPlayer()
        updateCurrentSkin()
        updateCurrentBoard()
        loadTrainingState()
        reset()
    }

    fun getAIMode(): Int = aiMode
    fun setAIMode(m: Int) { aiMode = m; invalidate() }

    fun setTrainingMode(b: Boolean) {
        trainingMode = b
        if (b) { aiMode = 1; bgm?.stop(); reset() }
        else { stopParallelTraining(); if (running) bgm?.start(); reset() }
        invalidate()
    }

    fun setReinforceTraining(enable: Boolean) {
        if (enable) { startParallelTraining(); startWatchDog() }
        else { stopParallelTraining(); stopWatchDog() }
        invalidate()
    }

    fun isReinforceTraining(): Boolean = reinforceTraining
    fun isTrainingMode(): Boolean = trainingMode

    private fun restartTrainingSafely() {
        synchronized(sharedLock) { trainActive = false; reinforceTraining = false }
        val oldThreads = synchronized(trainThreads) { trainThreads.toList() }
        for (t in oldThreads) { try { t.interrupt() } catch (_: Throwable) {} }
        for (t in oldThreads) { try { t.join(500) } catch (_: InterruptedException) { break } }
        synchronized(trainThreads) { trainThreads.clear() }
        Thread.sleep(200)
        synchronized(sharedLock) { reinforceTraining = true }
        startParallelTraining(resetCounters = false)
        startWatchDog()
    }

    private fun startParallelTraining(resetCounters: Boolean = true) {
        synchronized(trainingLifecycleLock) {
            if (trainThreads.any { it.isAlive }) return
            if (trainActive) return

            trainingRunId++
            val myRunId = trainingRunId

            reinforceTraining = true
            trainingMode = true
            aiMode = 1
            bgm?.stop()
            gameOver = false
            trainActive = true
            trainThreads.clear()

            if (resetCounters) {
                currentAgentIndex = 0
                completedAgents = 0
                uniqueCompletedAgents = 0
                bestScoreThisGen = 0f
                completedAgentIds.clear()
                java.util.Arrays.fill(agentCompleted, false)
                synchronized(sharedLock) { for (i in 0 until POPULATION_SIZE) currentScores[i] = 0f }
            }

            generationToken++
            val myGenerationToken = generationToken
            generationTransitioning = false

            for (i in threadStatus.indices) {
                threadStatus[i].alive = false; threadStatus[i].agentId = -1
                threadStatus[i].score = 0; threadStatus[i].steps = 0; threadStatus[i].phase = "空闲"
            }

            Log.d(LOG_TAG, "GEN_START gen=$generation token=$myGenerationToken run=$myRunId pop=$POPULATION_SIZE th=$TRAIN_THREADS")

            for (i in 0 until TRAIN_THREADS) {
                val threadIdx = i
                val t = Thread({
                    val game = TrainGame(seed = System.nanoTime() + i * 999983L, runId = myRunId, statusIndex = threadIdx)
                    threadStatus[threadIdx].alive = true

                    while (isTrainingRunActive(myRunId) && !Thread.currentThread().isInterrupted) {
                        if (evolving || generationTransitioning || generationToken != myGenerationToken) {
                            threadStatus[threadIdx].phase = "进化"; Thread.yield(); continue
                        }

                        val agentId: Int
                        synchronized(sharedLock) {
                            if (currentAgentIndex >= POPULATION_SIZE) agentId = -1
                            else { agentId = currentAgentIndex; currentAgentIndex++ }
                        }

                        if (agentId < 0) { threadStatus[threadIdx].phase = "等待"; Thread.yield(); continue }

                        // ★ 修复 1035：不在 synchronized lambda 中 continue
                        var invalidAgent = false
                        synchronized(sharedLock) {
                            if (agentId !in 0 until POPULATION_SIZE || agentCompleted[agentId]) {
                                Log.e(LOG_TAG, "INVALID_AGENT_ASSIGNMENT agent=$agentId gen=$generation")
                                invalidAgent = true
                            }
                        }
                        if (invalidAgent) {
                            threadStatus[threadIdx].phase = "等待"
                            continue
                        }

                        threadStatus[threadIdx].agentId = agentId
                        threadStatus[threadIdx].phase = "训练"
                        Log.d(LOG_TAG, "AGENT_START gen=$generation agent=$agentId thread=$threadIdx")

                        var episodeCompleted = false
                        try {
                            episodeCompleted = game.playOneGame(agentId = agentId, expectedGenerationToken = myGenerationToken)
                        } catch (t: Throwable) { Log.e(LOG_TAG, "Agent $agentId crashed outside playOneGame", t) }

                        if (!episodeCompleted) { threadStatus[threadIdx].phase = "等待"; continue }

                        // ★ 修复 1054 / 1060：不在 synchronized lambda 中让 if 处于表达式位置
                        var shouldEvolve = false
                        synchronized(sharedLock) {
                            if (generationToken != myGenerationToken) {
                                Log.w(LOG_TAG, "STALE_AGENT_RESULT agent=$agentId expected=$myGenerationToken actual=$generationToken")
                            } else if (agentId in 0 until POPULATION_SIZE && !agentCompleted[agentId]) {
                                agentCompleted[agentId] = true
                                completedAgentIds.add(agentId)
                                completedAgents++
                                uniqueCompletedAgents++
                                Log.d(LOG_TAG, "AGENT_COMPLETE gen=$generation agent=$agentId done=$completedAgents/$POPULATION_SIZE")
                                val generationFinished = completedAgents == POPULATION_SIZE &&
                                        currentAgentIndex == POPULATION_SIZE &&
                                        !generationTransitioning
                                if (generationFinished) {
                                    generationTransitioning = true
                                    shouldEvolve = true
                                    Log.d(LOG_TAG, "GEN_COMPLETE gen=$generation done=$completedAgents/$POPULATION_SIZE")
                                } else {
                                    // 保持 if 有 else，避免 Kotlin 把同步块最后一句 if 当表达式
                                }
                            } else {
                                // generationToken 不一致或该 agent 已完成 → 不结算
                            }
                        }

                        if (shouldEvolve) {
                            synchronized(evolveLock) {
                                if (isTrainingRunActive(myRunId) && generationToken == myGenerationToken) {
                                    try { evolveNextGeneration() } catch (t: Throwable) { Log.e(LOG_TAG, "evolveNextGeneration failed", t) }
                                    finally {
                                        synchronized(sharedLock) {
                                            currentAgentIndex = 0; completedAgents = 0; uniqueCompletedAgents = 0
                                            completedAgentIds.clear(); java.util.Arrays.fill(agentCompleted, false)
                                            generationToken++; generationTransitioning = false
                                        }
                                        Log.d(LOG_TAG, "GEN_NEXT_READY gen=$generation")
                                    }
                                } else synchronized(sharedLock) { generationTransitioning = false }
                            }
                        }
                    }
                    threadStatus[threadIdx].alive = false; threadStatus[threadIdx].phase = "空闲"; threadStatus[threadIdx].agentId = -1
                }, "snake-train-$i")
                t.isDaemon = true
                t.priority = Thread.NORM_PRIORITY
                t.start()
                trainThreads.add(t)
            }
        }
    }

    private fun stopParallelTraining() {
        val threadsToJoin: List<Thread>
        synchronized(trainingLifecycleLock) {
            if (!trainActive && trainThreads.none { it.isAlive }) { reinforceTraining = false; trainingMode = false; return }
            trainingRunId++; trainActive = false; reinforceTraining = false; trainingMode = false
            threadsToJoin = trainThreads.toList()
        }
        for (t in threadsToJoin) { try { t.interrupt() } catch (_: Throwable) {} }
        for (t in threadsToJoin) { try { t.join(5000L) } catch (_: Throwable) {} }
        synchronized(trainingLifecycleLock) { trainThreads.removeAll { !it.isAlive } }
        saveLearning(); saveTrainingState()
        if (running) bgm?.start()
        reset()
    }

    fun setForcedStrategy(s: Int) { forcedStrategy = s; invalidate() }

    fun updateCurrentSkin(id: String? = null) {
        when (prefs.getString("equipped_skin", "green")) {
            "blue" -> setSnakeColors(Color.rgb(52, 152, 219), Color.rgb(41, 128, 185), false)
            "red" -> setSnakeColors(Color.rgb(46, 204, 113), Color.rgb(192, 57, 43), false)
            "purple" -> setSnakeColors(Color.rgb(155, 89, 182), Color.rgb(142, 68, 173), false)
            "gold" -> setSnakeColors(Color.rgb(241, 196, 15), Color.rgb(243, 156, 18), false)
            "rainbow" -> setSnakeColors(Color.WHITE, Color.WHITE, true)
            else -> setSnakeColors(Color.rgb(46, 204, 113), Color.rgb(39, 174, 96), false)
        }
        invalidate()
    }

    private fun setSnakeColors(body: Int, head: Int, rainbow: Boolean) {
        bodyColor = body; headColor = head; rainbowSkin = rainbow
        snakePaint.color = body
        snakePaint.style = Paint.Style.STROKE
        snakePaint.strokeCap = Paint.Cap.ROUND
        snakePaint.strokeJoin = Paint.Join.ROUND
        snakePaint.strokeWidth = 0f
        headPaint.color = head
    }

    fun updateCurrentBoard(id: String? = null) {
        when (prefs.getString("equipped_board", "dark")) {
            "light" -> { bgColor = Color.rgb(240, 240, 240); gridColor = Color.rgb(200, 200, 200) }
            "neon" -> { bgColor = Color.rgb(10, 25, 47); gridColor = Color.CYAN }
            "forest" -> { bgColor = Color.rgb(27, 46, 26); gridColor = Color.rgb(46, 74, 45) }
            "cyberpunk" -> { bgColor = Color.rgb(43, 15, 59); gridColor = Color.MAGENTA }
            "rainbow_board" -> { bgColor = Color.BLACK; gridColor = Color.WHITE }
            else -> { bgColor = Color.BLACK; gridColor = Color.CYAN }
        }
        invalidate()
    }

    fun reset() {
        snake.clear(); queue.clear()
        if (aiMode == 2) { snake.add(P(0, 0)); dir = P(0, 1) }
        else { snake.add(P(cols / 2, rows / 2)); dir = P(1, 0) }
        score = 0; combo = 0; hunger = 0
        gameOver = false; deathCause = "无"; lastDeathInfo = ""
        gameSpeed = if (trainingMode && !reinforceTraining) 2L else gameSpeedStart
        accumulator = 0L; lastFrame = 0L
        particles.clear(); floats.clear()
        flash = 0f; restartCountdown = 0L
        lastV2State = -1; lastV2Action = -1
        ai = Snapshot(chosen = dir)
        placeFood()
        lastFreeRegion = freeRegion(snake).toFloat()
        onScoreChanged?.invoke(score)
        invalidate()
    }

    fun resume() {
        if (running) return
        running = true; lastFrame = 0L
        if (!trainingMode) bgm?.start()
        Choreographer.getInstance().postFrameCallback(frame)
    }

    fun pause() {
        running = false; bgm?.stop()
        Choreographer.getInstance().removeFrameCallback(frame)
    }

    private fun updateGame() {
        if (gameOver) return
        heartbeat()
        if (hunger >= hungerKillLimit) { die("HUNGER"); return }
        if (aiMode != 0) { queue.clear(); queue.add(chooseMove()) }
        if (queue.isNotEmpty()) {
            val requested = queue.removeFirst()
            if (!isReverse(requested, dir) && legalDirection(requested)) dir = requested
        }
        if (dir == P(0, 0)) return
        val oldState = buildState(snake, dir, food, hunger)
        val oldAction = dirs.indexOfFirst { it == dir }.coerceAtLeast(0)
        val nh = P(snake.first().x + dir.x, snake.first().y + dir.y)
        if (!inside(nh)) { qTerminalFromMove(oldState, oldAction, DEATH_WALL); die("WALL"); return }
        val ate = nh == food
        val body = snake.toList()
        val hitIndex = body.indexOf(nh)
        val tail = snake.last()
        if (hitIndex >= 0 && !(nh == tail && !ate)) {
            val sim = simulateOn(ArrayDeque(snake), dir)
            val region = freeRegion(sim.body)
            val cause = if (region < max(2, (snake.size * safetyMargin).toInt())) "TRAP" else "SELF"
            val reward = if (cause == "TRAP") DEATH_TRAP else DEATH_SELF
            qTerminalFromMove(oldState, oldAction, reward); die(cause); return
        }
        snake.addFirst(nh); v3RecordHead()
        var reward = REWARD_STEP
        if (ate) {
            val comboBonus = min(combo, 30) * 3
            val gain = 10 + comboBonus + snake.size
            score += gain; combo++; hunger = 0
            money += gain * 3 + 30
            if (score > highScore) highScore = score
            onScoreChanged?.invoke(score); onMoneyChanged?.invoke(money)
            prefs.edit().putInt("money", money).putInt("high_score", highScore).apply()
            gameSpeed = max(gameSpeedMin, gameSpeedStart - snake.size * 2L)
            vibrateEat(); playEatSound(); spawnFoodEffect(nh); placeFood()
            reward += REWARD_FOOD + combo * 0.06f
        } else {
            snake.removeLast(); hunger++; combo = max(0, combo - 1)
            val curFree = freeRegion(snake).toFloat()
            val spaceDelta = curFree - lastFreeRegion
            lastFreeRegion = curFree
            reward += spaceDelta * REWARD_SPACE_DELTA
            if (tailReachable(snake)) reward += REWARD_TAIL
            if (calculateDanger() >= 4) reward += REWARD_DANGER
            val hungerPenalty = -(hunger * hunger * 0.001f).coerceAtMost(0.15f)
            reward += hungerPenalty
        }
        val nextState = buildState(snake, dir, food, hunger)
        val nextMask = legalActionMask(snake, dir, food)
        qUpdate(oldState, oldAction, reward, nextState, nextMask, false)
        lastV2State = nextState; lastV2Action = oldAction
    }

    private fun directionIndex(d: P): Int = when (d) { P(0, -1) -> 0; P(0, 1) -> 1; P(-1, 0) -> 2; else -> 3 }

    private fun foodDirection(head: P, target: P): Int {
        val dx = target.x - head.x; val dy = target.y - head.y
        return if (abs(dx) >= abs(dy)) { if (dx >= 0) 3 else 2 } else { if (dy >= 0) 1 else 0 }
    }

    private fun dangerMask(body: ArrayDeque<P>, heading: P, target: P): Int {
        if (body.isEmpty()) return 15
        val h = body.first(); var mask = 0
        for (i in dirs.indices) {
            val d = dirs[i]
            if (isReverse(d, heading)) { mask = mask or (1 shl i); continue }
            val np = P(h.x + d.x, h.y + d.y)
            if (!inside(np)) { mask = mask or (1 shl i); continue }
            val ate = np == target
            if (body.contains(np) && !(np == body.last() && !ate)) { mask = mask or (1 shl i); continue }
            val sim = simulateForBody(body, d, target)
            if (sim.body.isEmpty()) { mask = mask or (1 shl i); continue }
            val region = freeRegion(sim.body)
            val tail = tailReachable(sim.body)
            val ratio = region.toFloat() / max(1, sim.body.size)
            if (!tail && sim.body.size > 8) mask = mask or (1 shl i)
            else if (ratio < 0.55f && sim.body.size > 12) mask = mask or (1 shl i)
        }
        return mask and 15
    }

    private fun buildState(body: ArrayDeque<P>, heading: P, target: P, hungerValue: Int): Int {
        if (body.isEmpty()) return 0
        val h = body.first()
        val foodD = foodDirection(h, target)
        val danger = dangerMask(body, heading, target)
        val mobility = countSafeMovesFor(body, heading, target).coerceIn(0, 4)
        val region = freeRegion(body)
        val ratio = region.toFloat() / max(1, body.size)
        val spaceBucket = when { ratio < 0.8f -> 0; ratio < 1.3f -> 1; ratio < 2.0f -> 2; else -> 3 }
        val hungerBucket = when { hungerValue < 10 -> 0; hungerValue < 25 -> 1; hungerValue < 50 -> 2; hungerValue < 100 -> 3; else -> 4 }
        val lengthBucket = when { body.size < 12 -> 0; body.size < 30 -> 1; body.size < 60 -> 2; else -> 3 }
        val tail = if (tailReachable(body)) 1 else 0
        val headingIndex = directionIndex(heading)
        var s = foodD
        s = s * V2_DANGER + danger
        s = s * V2_MOBILITY + mobility
        s = s * V2_SPACE + spaceBucket
        s = s * V2_HUNGER + hungerBucket
        s = s * V2_LENGTH + lengthBucket
        s = s * V2_TAIL + tail
        s = s * V2_HEADING + headingIndex
        return s.coerceIn(0, V2_STATE_COUNT - 1)
    }

    private fun legalActionMask(body: ArrayDeque<P>, heading: P, target: P): Int {
        if (body.isEmpty()) return 0
        val h = body.first(); var mask = 0
        for (i in dirs.indices) {
            val d = dirs[i]
            if (isReverse(d, heading)) continue
            val np = P(h.x + d.x, h.y + d.y)
            if (!inside(np)) continue
            val ate = np == target
            if (body.contains(np) && !(np == body.last() && !ate)) continue
            mask = mask or (1 shl i)
        }
        return mask
    }

    private fun qTerminalFromMove(state: Int, action: Int, reward: Float) { qUpdate(state, action, reward, state, 0, true) }

    private fun selectV2Action(state: Int, legal: List<Candidate>, training: Boolean): Candidate {
        if (legal.isEmpty()) return Candidate(dir, -1e9f, "无合法动作", false)
        if (forcedStrategy >= 0) return bestSurvivalStep(legal)
        val epsilon = if (training) currentEpsilon() else 0f
        if (training && Random.nextFloat() < epsilon) {
            val safe = legal.filter { it.tailOk || it.region >= max(5, snake.size / 2) }
            return if (safe.isNotEmpty()) safe[Random.nextInt(safe.size)] else legal[Random.nextInt(legal.size)]
        }
        var best = legal.first(); var bestValue = -Float.MAX_VALUE
        for (candidate in legal) {
            val action = dirs.indexOfFirst { it == candidate.d }
            if (action < 0) continue
            val q = qRead(state, action); val visits = qVisit(state, action)
            val safetyBonus = when {
                candidate.tailOk && candidate.region >= snake.size * 1.5f -> 2.2f
                candidate.tailOk -> 1.2f
                candidate.region >= snake.size -> 0.35f
                else -> -1.5f
            }
            val foodBonus = if (candidate.ate) 4.0f else if (candidate.foodDist >= 0) 0.7f / (candidate.foodDist + 1) else 0f
            val visitBonus = 0.12f / kotlin.math.sqrt((visits + 1).toFloat())
            val value = q + safetyBonus + foodBonus + visitBonus
            if (value > bestValue) { bestValue = value; best = candidate.copy(qValue = q) }
        }
        return best
    }

    private fun chooseMove(): P {
        aiStepStartNs = System.nanoTime(); aiStepBudgetNs = budgetFor(gameSpeed)
        if (v3FusionEnabled) { val v3g = v3SelectGoal(); v3Goal = v3g; v3GoalCounter[v3g.ordinal]++ }
        val futures: List<Future<Candidate>> = dirs.map { d -> aiPool.submit(Callable { evaluate(d) }) }
        val candidates = futures.map { try { it.get() } catch (_: Throwable) { Candidate(P(0, 0), -1e9f, "AI异常", false) } }
        val legal = candidates.filter { it.legal }
        if (legal.isEmpty()) { ai = Snapshot(strategy = "NO MOVE", reason = "四个方向都无法前进", danger = 5, chosen = dir, candidates = candidates); return dir }
        val danger = calculateDanger()
        val regionNow = freeRegion(snake)
        val foodDistNow = distance(snake.first(), food, snake, true)
        val state = buildState(snake, dir, food, hunger)

        val safeFood = findSafeFoodStep()
        if (safeFood != null) {
            val action = dirs.indexOfFirst { it == safeFood }.coerceAtLeast(0)
            val q = qRead(state, action)
            lastV2State = state; lastV2Action = action
            v3LayerActive = 1; v3LayerWhy = "L1安全食物层(硬安全)"
            ai = Snapshot(strategy = "V2 SAFE FOOD", reason = "安全路径可吃食物，吃后尾巴仍可达",
                danger = danger, region = regionNow, spaceRatio = regionNow.toFloat() / max(1, snake.size),
                tailReachable = tailReachable(snake), foodReachable = true, foodDistance = foodDistNow,
                hunger = hunger, chosen = safeFood, candidates = candidates, depth = 2, nodes = legal.size,
                hungerFactor = hungerFactorValue(), regionWeight = wRegion, strategyId = 10,
                qValue = q, nVisits = qVisit(state, action), forceEatActive = false, forceEatSafe = true, safeFollowMode = false)
            return v3PostCheck(safeFood, legal, state)
        }

        val tailStep = followTailStep(legal)
        if (tailStep != null && hunger < hungerForceEat()) {
            val action = dirs.indexOfFirst { it == tailStep }.coerceAtLeast(0)
            val q = qRead(state, action)
            lastV2State = state; lastV2Action = action
            v3LayerActive = 2; v3LayerWhy = "L2尾巴追踪层(空间循环)"
            ai = Snapshot(strategy = "V2 TAIL", reason = "食物路线风险较高，沿尾巴保持循环空间",
                danger = danger, region = regionNow, spaceRatio = regionNow.toFloat() / max(1, snake.size),
                tailReachable = true, foodReachable = foodDistNow >= 0, foodDistance = foodDistNow,
                hunger = hunger, chosen = tailStep, candidates = candidates, depth = 1, nodes = legal.size,
                hungerFactor = hungerFactorValue(), regionWeight = wRegion, strategyId = 11,
                qValue = q, nVisits = qVisit(state, action), forceEatActive = false, forceEatSafe = false, safeFollowMode = true)
            return v3PostCheck(tailStep, legal, state)
        }

        val forceThreshold = hungerForceEat()
        if (hunger >= forceThreshold && foodDistNow >= 0) {
            val safeFoodCandidates = legal.filter { it.tailOk && it.foodDist >= 0 }
            if (safeFoodCandidates.isNotEmpty()) {
                val selected = selectV2Action(state, safeFoodCandidates, training = trainingMode || reinforceTraining)
                val action = dirs.indexOfFirst { it == selected.d }.coerceAtLeast(0)
                lastV2State = state; lastV2Action = action
                v3LayerActive = 3; v3LayerWhy = "L3饥饿压制层(强制进食)"
                ai = Snapshot(strategy = "V2 HUNGER", reason = "饥饿压力提高食物收益，但仍受安全屏蔽",
                    danger = max(danger, 3), region = regionNow, spaceRatio = regionNow.toFloat() / max(1, snake.size),
                    tailReachable = selected.tailOk, foodReachable = true, foodDistance = selected.foodDist,
                    hunger = hunger, chosen = selected.d,
                    candidates = candidates.map { if (it.d == selected.d) it.copy(qValue = qRead(state, action)) else it },
                    depth = 1, nodes = legal.size, hungerFactor = hungerFactorValue(), regionWeight = wRegion,
                    strategyId = 12, qValue = qRead(state, action), nVisits = qVisit(state, action),
                    forceEatActive = true, forceEatSafe = true, safeFollowMode = false)
                return v3PostCheck(selected.d, legal, state)
            }
        }

        val shielded = legal.filter { val ratio = it.region.toFloat() / max(1, snake.size); it.tailOk || ratio >= 1.0f || (snake.size < 15 && ratio >= 0.75f) }
        val pool = if (shielded.isNotEmpty()) shielded else legal
        val brain = if (trainingMode || reinforceTraining) population[currentAgentIndex.coerceAtLeast(0) % POPULATION_SIZE] else population[0]
        val nnInputs = buildInputs(snake.first(), food, snake)
        val nnVals = brain.think(nnInputs)
        val de = checkFoodDeadEnd()
        deadEndPredicted = de.first; foodSpaceRatio = de.second
        var deadEndPenalty = 0f; if (de.first) deadEndPenalty = -5f
        val rSteps = when { snake.size > 60 -> 5; snake.size > 25 -> 3; else -> 0 }
        rolloutActive = rSteps > 0; rolloutSteps = rSteps

        var best = pool.first(); var bestValue = -Float.MAX_VALUE
        for (candidate in pool) {
            val action = dirs.indexOfFirst { it == candidate.d }; if (action < 0) continue
            val q = qRead(state, action); val nn = nnVals[action]; val rule = candidate.score
            val rolloutScore = if (rSteps > 0) rolloutN(candidate.d, rSteps) else 0f
            val mixed = qWeight * q + nnWeight * nn * 5f + rule * 0.001f + deadEndPenalty + rolloutScore * 0.5f
            if (mixed > bestValue) { bestValue = mixed; best = candidate.copy(qValue = q) }
        }

        val action = dirs.indexOfFirst { it == best.d }.coerceAtLeast(0)
        lastV2State = state; lastV2Action = action
        v3LayerActive = 4; v3LayerWhy = "L4混合决策(Q+NN+规则)"
        ai = Snapshot(strategy = "V4混合进化 (Q+NN+记忆)", reason = "规则过滤后，Q表与NN选出最优动作",
            danger = danger, region = regionNow, spaceRatio = regionNow.toFloat() / max(1, snake.size),
            tailReachable = tailReachable(snake), foodReachable = foodDistNow >= 0, foodDistance = foodDistNow,
            hunger = hunger, chosen = best.d, candidates = candidates.map { if (it.d == best.d) it.copy(qValue = qRead(state, action)) else it },
            depth = 1, nodes = pool.size, hungerFactor = hungerFactorValue(), regionWeight = wRegion,
            strategyId = 20, qValue = qRead(state, action), nVisits = qVisit(state, action),
            forceEatActive = false, forceEatSafe = false, safeFollowMode = false)
        return v3PostCheck(best.d, legal, state)
    }

    private fun hungerFactorValue(): Float = when { hunger >= 60 -> 4f; hunger >= 30 -> 2.5f; hunger >= 15 -> 1.6f; else -> 1f }

    private fun followTailStep(legal: List<Candidate>): P? {
        if (snake.size < 2) return null
        val path = shortestPath(snake.first(), snake.last(), snake, allowTail = true) ?: return null
        if (path.isEmpty()) return null
        val step = path.first(); if (legal.none { it.d == step }) return null
        val sim = simulate(snake.first(), step); if (sim.body.isEmpty()) return null
        if (!tailReachable(sim.body)) return null
        val r = freeRegion(sim.body)
        if (r < 3 && snake.size < total - 5) return null
        return step
    }

    private fun findSafeFoodStep(): P? {
        val path = shortestPath(snake.first(), food, snake, allowTail = true) ?: return null
        if (path.isEmpty()) return null
        val simBody = ArrayDeque(snake); var ate = false
        for (step in path) {
            val nh = P(simBody.first().x + step.x, simBody.first().y + step.y)
            if (!inside(nh)) return null
            val willEat = nh == food
            if (simBody.contains(nh) && !(nh == simBody.last() && !willEat)) return null
            simBody.addFirst(nh); if (!willEat) simBody.removeLast() else ate = true
        }
        if (!ate) return null
        if (!tailReachable(simBody)) return null
        val len = simBody.size; val freeLeft = total - len
        if (len > 180 && freeLeft < 4) return null
        if (len > 150 && freeLeft < 6) return null
        if (len > 120 && freeLeft < 10) return null
        if (len > 90 && freeLeft < 14) return null
        if (len > 60 && freeLeft < 20) return null
        if (len <= 60 && freeLeft >= 20) { val r = freeRegion(simBody); if (r < max(4, freeLeft / 3)) return null }
        return path.first()
    }

    private fun bestSurvivalStep(legal: List<Candidate>): Candidate {
        var best = legal.first(); var bestScore = -1e30f
        val len = snake.size; val tailPos = snake.last(); val bodySet = snake.toHashSet()
        val tailW = (wTailGood / wTailGood0).coerceIn(0.8f, 1.2f)
        val spaceW = (wSpace / wSpace0).coerceIn(0.8f, 1.2f)
        val foodW = (wFoodNear / wFoodNear0).coerceIn(0.8f, 1.2f)
        for (cand in legal) {
            val sim = simulate(snake.first(), cand.d); if (sim.body.isEmpty()) continue
            val nh = sim.body.first(); val r = freeRegion(sim.body)
            val t = tailReachable(sim.body); val mob = countSafeMoves(sim.body)
            val freeLeft = total - sim.body.size
            var sc = 0f
            if (t) sc += 50000f * tailW
            else { sc -= 200000f; if (sc > bestScore) { bestScore = sc; best = cand }; continue }
            sc += r * 250f * spaceW
            if (freeLeft > 0) sc += (r.toFloat() / freeLeft) * 15000f * spaceW
            sc += mob * 500f
            var bodyAdj = 0
            for (d in dirs) { val p = P(nh.x + d.x, nh.y + d.y); if (bodySet.contains(p) || sim.body.contains(p)) bodyAdj++ }
            sc += bodyAdj * 600f
            val dToTail = distance(nh, tailPos, sim.body, true)
            if (dToTail >= 0) { sc += 8000f / (dToTail + 1); if (dToTail > 6) sc -= (dToTail - 6) * 150f }
            val fd = distance(nh, food, sim.body, true)
            if (fd >= 0) sc += (500f * foodW) / (fd + 1)
            if (len >= 100) sc += r * 300f
            val nx = sim.body.first().x; val ny = sim.body.first().y
            val edge = min(min(nx, cols - 1 - nx), min(ny, rows - 1 - ny))
            sc -= max(0, 3 - edge) * 800f
            val hx0 = snake.first().x; val hy0 = snake.first().y
            val atEdgeNow = hx0 == 0 || hx0 == cols - 1 || hy0 == 0 || hy0 == rows - 1
            if (!atEdgeNow && edge == 0 && snake.size > 20) sc -= 6000f
            if (nx == 0 || nx == cols - 1 || ny == 0 || ny == rows - 1) sc -= 500f
            if (sim.ate) sc += 5000f
            if (sc > bestScore) { bestScore = sc; best = cand }
        }
        return best
    }

    private fun evaluate(d: P): Candidate {
        if (!legalDirection(d)) return Candidate(d, -1e9f, "撞墙/身体", false)
        val sim = simulate(snake.first(), d)
        val region = freeRegion(sim.body); val tail = tailReachable(sim.body)
        val foodDist = distance(sim.body.first(), food, sim.body, true)
        val ate = sim.ate; val mobility = countSafeMoves(sim.body)
        val hungerFactor = hungerFactorValue()
        val lenBoost = if (snake.size >= safeFollowLength) (snake.size.toFloat() / safeFollowLength).coerceIn(1f, 3f) else 1f
        val regionScoreVal = region * wRegion * lenBoost
        val mobilityScoreVal = mobility * wMobility
        val tailScoreVal = if (tail) wTailGood * lenBoost else wTailBad * lenBoost
        var foodScoreVal = if (foodDist >= 0) hungerFactor * aggression * (wFoodNear / (foodDist + 1)) else -450f * hungerFactor
        if (ate) foodScoreVal += wFoodAte * aggression
        var eatPenalty = 0f
        if (ate) {
            val afterSize = sim.body.size
            val needSpace = (afterSize * safetyMargin).toInt() + 2
            if (!tail || region < needSpace) eatPenalty = -7500f - snake.size * 100f
            else {
                val after = ArrayDeque(sim.body)
                val dx = after.last().x - after.first().x
                val dy = after.last().y - after.first().y
                val follow = when {
                    abs(dx) >= abs(dy) && dx != 0 -> P(if (dx > 0) 1 else -1, 0)
                    dy != 0 -> P(0, if (dy > 0) 1 else -1)
                    else -> null
                }
                if (follow != null && canSim(after, follow)) {
                    val next = simulateOn(after, follow)
                    val r2 = freeRegion(next.body); val t2 = tailReachable(next.body)
                    if (!t2 || r2 < (afterSize * 1.2f).toInt()) eatPenalty = -4500f - snake.size * 60f
                }
            }
        }
        val edge = min(min(sim.body.first().x, cols - 1 - sim.body.first().x), min(sim.body.first().y, rows - 1 - sim.body.first().y))
        val edgeScoreVal = -max(0, 2 - edge) * wEdge
        val spacePenalty = max(0f, snake.size * safetyMargin - region.toFloat())
        val spaceScoreVal = -spacePenalty * wSpace
        val totalScore = regionScoreVal + mobilityScoreVal + tailScoreVal + foodScoreVal + edgeScoreVal + spaceScoreVal + eatPenalty
        val reason = when {
            ate && eatPenalty < 0 -> "吃完会困死，避开"
            ate -> "马上吃到食物"
            tail -> "保持尾巴可达"
            else -> "扩大可用空间"
        }
        return Candidate(d = d, score = totalScore, reason = reason, legal = true,
            regionScore = regionScoreVal, mobilityScore = mobilityScoreVal, tailScore = tailScoreVal,
            foodScore = foodScoreVal, edgeScore = edgeScoreVal, spaceScore = spaceScoreVal,
            region = region, mobility = mobility, tailOk = tail, foodDist = foodDist, ate = ate)
    }

    private fun clampW(v: Float, lo: Float, hi: Float): Float = v.coerceIn(lo, hi)

    private fun adjustWeights(cause: String) {
        val beforeEdge = wEdge; val beforeTail = wTailGood; val beforeSpace = wSpace; val beforeFood = wFoodNear
        val beforeAgg = aggression; val beforeSafety = safetyMargin
        when (cause) {
            "WALL" -> { wEdge = clampW(wEdge * 1.03f, wEdge0 * 0.9f, wEdge0 * 1.1f); aggression = clampW(aggression * 0.99f, 0.95f, 1.35f) }
            "SELF" -> { wTailGood = clampW(wTailGood * 1.03f, wTailGood0 * 0.9f, wTailGood0 * 1.1f); wTailBad = clampW(wTailBad * 1.02f, wTailBad0 * 1.1f, wTailBad0 * 0.9f); safetyMargin = clampW(safetyMargin * 1.01f, 1.0f, 1.20f) }
            "TRAP" -> { wSpace = clampW(wSpace * 1.04f, wSpace0 * 0.9f, wSpace0 * 1.1f); wRegion = clampW(wRegion * 1.02f, wRegion0 * 0.9f, wRegion0 * 1.1f); safetyMargin = clampW(safetyMargin * 1.01f, 1.0f, 1.20f); aggression = clampW(aggression * 1.005f, 0.95f, 1.35f); wFoodAte = clampW(wFoodAte * 1.02f, wFoodAte0 * 0.9f, wFoodAte0 * 1.1f) }
            "HUNGER" -> { wFoodNear = clampW(wFoodNear * 1.04f, wFoodNear0 * 0.9f, wFoodNear0 * 1.1f); wFoodAte = clampW(wFoodAte * 1.03f, wFoodAte0 * 0.9f, wFoodAte0 * 1.1f); aggression = clampW(aggression * 1.02f, 0.95f, 1.35f); wSpace = clampW(wSpace * 0.98f, wSpace0 * 0.9f, wSpace0 * 1.1f); safetyMargin = clampW(safetyMargin * 0.99f, 1.0f, 1.20f) }
        }
        wRegion = wRegion * 0.95f + wRegion0 * 0.05f
        wMobility = wMobility * 0.95f + wMobility0 * 0.05f
        wEdge = wEdge * 0.95f + wEdge0 * 0.05f
        wSpace = wSpace * 0.95f + wSpace0 * 0.05f
        wFoodNear = wFoodNear * 0.95f + wFoodNear0 * 0.05f
        wTailGood = wTailGood * 0.95f + wTailGood0 * 0.05f
        wFoodAte = wFoodAte * 0.95f + wFoodAte0 * 0.05f
        lastLearnAction = when (cause) {
            "WALL" -> "边界${"%.0f→%.0f".format(beforeEdge, wEdge)} 攻${"%.2f→%.2f".format(beforeAgg, aggression)}"
            "SELF" -> "尾+${"%.0f→%.0f".format(beforeTail, wTailGood)} 安全${"%.2f→%.2f".format(beforeSafety, safetyMargin)}"
            "TRAP" -> "空间${"%.0f→%.0f".format(beforeSpace, wSpace)} 安全${"%.2f→%.2f".format(beforeSafety, safetyMargin)}"
            "HUNGER" -> "食近${"%.0f→%.0f".format(beforeFood, wFoodNear)} 攻${"%.2f→%.2f".format(beforeAgg, aggression)}"
            else -> "微调"
        }
    }

    private fun saveTrainingState() {
        try {
            val file = context.getFileStreamPath("snake_training.dat")
            val genCopy: Int; val scoreCopy: Float; val qCopy: FloatArray; val nCopy: IntArray; val popCopy: List<TinyBrain>
            synchronized(sharedLock) {
                genCopy = generation; scoreCopy = bestScoreAllTime
                qCopy = qV2.copyOf(); nCopy = nV2.copyOf()
                popCopy = population.map { b -> TinyBrain().apply {
                    System.arraycopy(b.w1, 0, w1, 0, b.w1.size)
                    System.arraycopy(b.w2, 0, w2, 0, b.w2.size)
                    System.arraycopy(b.w3, 0, w3, 0, b.w3.size)
                } }
            }
            DataOutputStream(BufferedOutputStream(FileOutputStream(file))).use { out ->
                out.writeInt(genCopy); out.writeFloat(scoreCopy)
                for (brain in popCopy) {
                    for (v in brain.w1) out.writeFloat(v)
                    for (v in brain.w2) out.writeFloat(v)
                    for (v in brain.w3) out.writeFloat(v)
                }
                for (q in qCopy) out.writeFloat(q)
                for (n in nCopy) out.writeInt(n)
            }
        } catch (e: Exception) { e.printStackTrace() }
    }

    private fun loadTrainingState() {
        try {
            val file = context.getFileStreamPath("snake_training.dat")
            if (!file.exists()) return
            DataInputStream(BufferedInputStream(FileInputStream(file))).use { input ->
                generation = input.readInt(); bestScoreAllTime = input.readFloat()
                for (i in 0 until POPULATION_SIZE) {
                    val brain = TinyBrain()
                    for (j in brain.w1.indices) brain.w1[j] = input.readFloat()
                    for (j in brain.w2.indices) brain.w2[j] = input.readFloat()
                    for (j in brain.w3.indices) brain.w3[j] = input.readFloat()
                    population[i] = brain
                }
                for (i in qV2.indices) qV2[i] = input.readFloat()
                for (i in nV2.indices) nV2[i] = input.readInt()
            }
        } catch (e: Exception) {
            e.printStackTrace(); generation = 0; bestScoreAllTime = 0f
            for (i in 0 until POPULATION_SIZE) population[i] = TinyBrain()
            java.util.Arrays.fill(qV2, 0f); java.util.Arrays.fill(nV2, 0)
        }
    }

    private fun saveLearning() {
        synchronized(sharedLock) {
            prefs.edit()
                .putFloat("learn_aggression", aggression).putFloat("learn_safety", safetyMargin)
                .putFloat("learn_shortcut", shortcutBonus)
                .putFloat("w_region", wRegion).putFloat("w_mobility", wMobility)
                .putFloat("w_tail_good", wTailGood).putFloat("w_tail_bad", wTailBad)
                .putFloat("w_food_near", wFoodNear).putFloat("w_food_ate", wFoodAte)
                .putFloat("w_edge", wEdge).putFloat("w_space", wSpace)
                .putString("last_learn_action", lastLearnAction)
                .putFloat("v3_g_food", v3Genome.foodPriority).putFloat("v3_g_space", v3Genome.spacePriority)
                .putFloat("v3_g_tail", v3Genome.tailPriority).putFloat("v3_g_danger", v3Genome.dangerAversion)
                .putFloat("v3_g_loop", v3Genome.loopAversion).putFloat("v3_g_hunger", v3Genome.hungerUrgency)
                .putInt("v3_lesson_fires", v3LessonFires).putInt("v3_loop_hits", v3LoopHits)
                .putInt("stat_wall", deathWall).putInt("stat_self", deathSelf)
                .putInt("stat_trap", deathTrap).putInt("stat_total", totalGames)
                .putInt("money", money).putInt("high_score", highScore)
                .apply()
        }
    }

    private fun die(cause: String) {
        gameOver = true; deathCause = cause
        v3AnalyzeDeath(cause)
        when (cause) { "WALL" -> deathWall++; "SELF" -> deathSelf++; "HUNGER" -> deathTrap++; else -> deathTrap++ }
        adjustWeights(cause); totalGames++; heartbeat()
        recentScores.addLast(score)
        while (recentScores.size > 50) recentScores.removeFirst()
        if (score > bestRecentScore) bestRecentScore = score
        aggression = when (cause) {
            "WALL" -> max(0.9f, aggression * 0.99f)
            "SELF" -> max(0.9f, aggression * 0.995f)
            "HUNGER" -> min(1.4f, aggression * 1.03f)
            else -> max(0.9f, aggression * 0.99f)
        }
        if (cause == "TRAP") safetyMargin = min(1.20f, safetyMargin * 1.01f)
        if (cause == "HUNGER") safetyMargin = max(1.0f, safetyMargin * 0.99f)
        safetyMargin = safetyMargin * 0.95f + 1.08f * 0.05f
        aggression = aggression * 0.95f + 1.15f * 0.05f
        safetyMargin = safetyMargin.coerceIn(1.0f, 1.20f)
        aggression = aggression.coerceIn(0.95f, 1.35f)
        lastDeathInfo = "死因=$cause 长度=${snake.size} 分=$score 空间=${ai.region} 需求=${(snake.size * safetyMargin).toInt()}"
        saveLearning()
        if (trainingMode) { reset(); return }
        flash = 1f; vibrateDeath(); restartCountdown = 0L; invalidate()
    }

    private fun simulate(head: P, d: P): Sim = simulateOn(ArrayDeque(snake), d)
    private fun simulateOn(src: ArrayDeque<P>, d: P): Sim {
        val b = ArrayDeque(src); if (b.isEmpty()) return Sim(b, false)
        val nh = P(b.first().x + d.x, b.first().y + d.y)
        if (!inside(nh)) return Sim(b, false)
        val ate = nh == food
        if (b.contains(nh) && !(nh == b.last() && !ate)) return Sim(b, false)
        b.addFirst(nh); if (!ate) b.removeLast(); return Sim(b, ate)
    }

    private fun rolloutN(startDir: P, maxSteps: Int): Float {
        var body = ArrayDeque(snake); var dir = startDir; var score = 0f
        for (step in 0 until maxSteps) {
            var bestNext: P? = null; var bestSpace = -1
            for (d in dirs) {
                val nh = P(body.first().x + d.x, body.first().y + d.y)
                if (!inside(nh)) continue
                val isTail = nh == body.last()
                if (body.contains(nh) && !isTail) continue
                var space = 0
                for (sd in dirs) {
                    val sx = nh.x + sd.x; val sy = nh.y + sd.y
                    if (sx in 0 until cols && sy in 0 until rows) { if (!body.any { it.x == sx && it.y == sy }) space++ }
                }
                if (space > bestSpace) { bestSpace = space; bestNext = d }
            }
            if (bestNext == null) return -50f + step * -10f
            val sim = simulateOn(body, bestNext)
            body = sim.body; score += 5f; if (sim.ate) score += 15f; dir = bestNext
        }
        return score
    }

    private fun simulateForBody(src: ArrayDeque<P>, d: P, target: P): Sim {
        val b = ArrayDeque(src); if (b.isEmpty()) return Sim(b, false)
        val nh = P(b.first().x + d.x, b.first().y + d.y)
        if (!inside(nh)) return Sim(b, false)
        val ate = nh == target
        if (b.contains(nh) && !(nh == b.last() && !ate)) return Sim(b, false)
        b.addFirst(nh); if (!ate) b.removeLast(); return Sim(b, ate)
    }

    private fun canSim(body: ArrayDeque<P>, d: P): Boolean {
        if (body.isEmpty()) return false
        val h = body.first()
        val nh = P(h.x + d.x, h.y + d.y)
        if (!inside(nh)) return false
        val ate = nh == food
        return !body.contains(nh) || (nh == body.last() && !ate)
    }

    private fun legalDirection(d: P): Boolean = d != P(0, 0) && !isReverse(d, dir) && canSim(snake, d)
    private fun isReverse(a: P, b: P): Boolean = a.x == -b.x && a.y == -b.y

    private fun directionOfFirst(body: ArrayDeque<P>): P {
        if (body.size < 2) return dir
        return P(body.elementAt(0).x - body.elementAt(1).x, body.elementAt(0).y - body.elementAt(1).y)
    }

    private fun inside(p: P): Boolean = p.x in 0 until cols && p.y in 0 until rows

    private fun shortestPath(start: P, target: P, body: Collection<P>, allowTail: Boolean): List<P>? {
        if (start == target) return emptyList()
        if (!inside(start) || !inside(target)) return null
        val visited = tlVisited.get(); val queue = tlQueue.get()
        val parent = IntArray(total) { -1 }; val parentDir = arrayOfNulls<P>(total)
        java.util.Arrays.fill(visited, 0, total, false)
        for (p in body) { if (!inside(p)) continue; visited[p.y * cols + p.x] = true }
        if (allowTail && body.isNotEmpty()) { val last = body.last(); if (inside(last)) visited[last.y * cols + last.x] = false }
        val startIndex = start.y * cols + start.x; val targetIndex = target.y * cols + target.x
        visited[startIndex] = true
        var head = 0; var tail = 0; queue[tail++] = startIndex; var found = false
        while (head < tail) {
            val curr = queue[head++]; if (curr == targetIndex) { found = true; break }
            val cx = curr % cols; val cy = curr / cols
            val candidates = arrayOf(
                P(0, -1) to if (cy > 0) curr - cols else -1,
                P(0, 1) to if (cy < rows - 1) curr + cols else -1,
                P(-1, 0) to if (cx > 0) curr - 1 else -1,
                P(1, 0) to if (cx < cols - 1) curr + 1 else -1
            )
            for ((d, ni) in candidates) {
                if (ni < 0 || ni >= total) continue
                if (visited[ni]) continue
                visited[ni] = true; parent[ni] = curr; parentDir[ni] = d
                if (tail < total) queue[tail++] = ni
            }
        }
        if (!found) return null
        val steps = ArrayList<P>(); var cur = targetIndex
        while (cur != startIndex) {
            val d = parentDir[cur] ?: return null
            steps.add(d); cur = parent[cur]; if (cur < 0) return null
        }
        steps.reverse(); return steps
    }

    private fun freeRegion(body: ArrayDeque<P>): Int {
        if (body.isEmpty()) return 0
        val visited = tlVisited.get(); val queue = tlQueue.get()
        java.util.Arrays.fill(visited, 0, total, false)
        for (p in body) { if (!inside(p)) continue; visited[p.y * cols + p.x] = true }
        val start = body.first(); if (!inside(start)) return 0
        val startIndex = start.y * cols + start.x; visited[startIndex] = true
        var head = 0; var tail = 0; queue[tail++] = startIndex; var count = 0
        while (head < tail) {
            val curr = queue[head++]; val cx = curr % cols; val cy = curr / cols; count++
            if (cx > 0) { val ni = curr - 1; if (!visited[ni]) { visited[ni] = true; if (tail < total) queue[tail++] = ni } }
            if (cx < cols - 1) { val ni = curr + 1; if (!visited[ni]) { visited[ni] = true; if (tail < total) queue[tail++] = ni } }
            if (cy > 0) { val ni = curr - cols; if (!visited[ni]) { visited[ni] = true; if (tail < total) queue[tail++] = ni } }
            if (cy < rows - 1) { val ni = curr + cols; if (!visited[ni]) { visited[ni] = true; if (tail < total) queue[tail++] = ni } }
        }
        return count
    }

    private fun distance(start: P, target: P, body: Collection<P>, allowTail: Boolean): Int {
        if (!inside(start) || !inside(target)) return -1
        if (start == target) return 0
        val visited = tlVisited.get(); val queue = tlQueue.get()
        java.util.Arrays.fill(visited, 0, total, false)
        for (p in body) { if (!inside(p)) continue; visited[p.y * cols + p.x] = true }
        if (allowTail && body.isNotEmpty()) { val last = body.last(); if (inside(last)) visited[last.y * cols + last.x] = false }
        val startIndex = start.y * cols + start.x; visited[startIndex] = true
        var head = 0; var tail = 0; queue[tail++] = startIndex; var dist = 0
        while (head < tail) {
            val layerSize = tail - head
            repeat(layerSize) {
                if (head >= tail) return@repeat
                val curr = queue[head++]; val cx = curr % cols; val cy = curr / cols
                if (cx == target.x && cy == target.y) return dist
                if (cx > 0) { val ni = curr - 1; if (!visited[ni]) { visited[ni] = true; if (tail < total) queue[tail++] = ni } }
                if (cx < cols - 1) { val ni = curr + 1; if (!visited[ni]) { visited[ni] = true; if (tail < total) queue[tail++] = ni } }
                if (cy > 0) { val ni = curr - cols; if (!visited[ni]) { visited[ni] = true; if (tail < total) queue[tail++] = ni } }
                if (cy < rows - 1) { val ni = curr + cols; if (!visited[ni]) { visited[ni] = true; if (tail < total) queue[tail++] = ni } }
            }
            dist++
        }
        return -1
    }

    private fun countSafeMoves(body: ArrayDeque<P>): Int = countSafeMovesFor(body, directionOfFirst(body), food)

    private fun countSafeMovesFor(body: ArrayDeque<P>, heading: P, target: P): Int {
        if (body.isEmpty()) return 0
        val h = body.first()
        return dirs.count { d ->
            if (isReverse(d, heading)) return@count false
            val nh = P(h.x + d.x, h.y + d.y)
            if (!inside(nh)) return@count false
            val ate = nh == target
            !body.contains(nh) || (nh == body.last() && !ate)
        }
    }

    private fun tailReachable(body: ArrayDeque<P>): Boolean = if (body.isEmpty()) false else distance(body.first(), body.last(), body, true) >= 0

    private fun checkFoodDeadEnd(): Pair<Boolean, Float> {
        if (snake.isEmpty()) return Pair(false, 10f)
        val visited = Array(cols) { BooleanArray(rows) }
        val queue = ArrayDeque<P>(); queue.addLast(food); visited[food.x][food.y] = true
        var space = 0
        while (!queue.isEmpty()) {
            val cur = queue.removeFirst(); space++
            for (d in dirs) {
                val nx = cur.x + d.x; val ny = cur.y + d.y
                if (nx in 0 until cols && ny in 0 until rows && !visited[nx][ny]) {
                    val isBody = snake.any { it.x == nx && it.y == ny }
                    if (!isBody) { visited[nx][ny] = true; queue.addLast(P(nx, ny)) }
                }
            }
        }
        val ratio = space.toFloat() / snake.size
        return Pair(ratio < 1.2f, ratio)
    }

    private fun calculateDanger(): Int {
        val region = freeRegion(snake)
        val ratio = region.toFloat() / max(1, snake.size)
        val mobility = countSafeMoves(snake)
        return when {
            mobility <= 0 -> 5; ratio < 1.5f -> 5; ratio < 2.2f -> 4
            ratio < 3.5f -> 3; ratio < 5f -> 2; else -> 1
        }
    }

    private fun placeFood() {
        val free = ArrayList<P>()
        for (x in 0 until cols) for (y in 0 until rows) { val p = P(x, y); if (!snake.contains(p)) free.add(p) }
        if (free.isNotEmpty()) food = free[Random.nextInt(free.size)]
    }

    private fun spawnFoodEffect(p: P) {
        repeat(14) { particles.add(Particle(p.x.toFloat(), p.y.toFloat(), Random.nextFloat() - 0.5f, Random.nextFloat() - 0.5f, 1f, Color.YELLOW)) }
        floats.add(FloatText(p.x.toFloat(), p.y.toFloat(), 1f, "+10"))
    }

    private fun updateEffects(dt: Float) {
        flash = max(0f, flash - dt * 0.035f)
        v3LessonFlash = max(0f, v3LessonFlash - dt * 0.8f)
        particles.forEach { it.x += it.vx * dt; it.y += it.vy * dt; it.life -= dt * 0.035f }
        particles.removeAll { it.life <= 0f }
        floats.forEach { it.y -= dt * 0.04f; it.life -= dt * 0.025f }
        floats.removeAll { it.life <= 0f }
    }

    override fun onSizeChanged(w: Int, h: Int, oldw: Int, oldh: Int) {
        val hudReserve = 760f + 292f; val availTop = 12f
        val availBottom = (h - hudReserve).coerceAtLeast(availTop + h * 0.30f)
        val availH = availBottom - availTop
        cell = min(w.toFloat() / cols, availH / rows)
        ox = (w - cols * cell) / 2f
        val baseOy = availTop + (availH - rows * cell) / 2f
        val moveDown = cell * 2.5f; val maxOy = availBottom - rows * cell
        oy = (baseOy + moveDown).coerceAtMost(maxOy)
    }

    override fun onDraw(c: Canvas) {
        super.onDraw(c)
        if (reinforceTraining) { c.drawColor(Color.BLACK); text.textAlign = Paint.Align.LEFT; drawTrainingDashboard(c); return }
        if (trainingMode) { c.drawColor(Color.BLACK); text.textAlign = Paint.Align.LEFT; drawDebug(c); return }
        c.drawColor(bgColor)
        gridPaint.color = gridColor; gridPaint.style = Paint.Style.STROKE; gridPaint.strokeWidth = 1f
        for (i in 0..cols) c.drawLine(ox + i * cell, oy, ox + i * cell, oy + rows * cell, gridPaint)
        for (i in 0..rows) c.drawLine(ox, oy + i * cell, ox + cols * cell, oy + i * cell, gridPaint)
        drawFood(c); drawSnake(c); drawParticles(c); drawDebug(c)
        if (gameOver) drawGameOver(c)
    }

    private fun drawFood(c: Canvas) {
        val cx = ox + (food.x + 0.5f) * cell; val cy = oy + (food.y + 0.5f) * cell
        foodPaint.color = Color.argb(90, 255, 80, 80); c.drawCircle(cx, cy, cell * 0.38f, foodPaint)
        foodPaint.color = Color.RED; c.drawCircle(cx, cy, cell * 0.22f, foodPaint)
        foodPaint.color = Color.WHITE; c.drawCircle(cx, cy, cell * 0.07f, foodPaint)
    }

    private fun drawSnake(c: Canvas) {
        if (snake.isEmpty()) return
        snakePaint.strokeWidth = max(8f, cell * 0.62f)
        val list = snake.toList()
        for (i in 0 until list.size - 1) {
            val a = list[i]; val b = list[i + 1]
            snakePaint.color = if (rainbowSkin) hsv[(i * 23 + score) % 360] else bodyColor
            c.drawLine(ox + (a.x + 0.5f) * cell, oy + (a.y + 0.5f) * cell, ox + (b.x + 0.5f) * cell, oy + (b.y + 0.5f) * cell, snakePaint)
        }
        val h = snake.first()
        headPaint.color = headColor
        c.drawCircle(ox + (h.x + 0.5f) * cell, oy + (h.y + 0.5f) * cell, cell * 0.36f, headPaint)
        val ex = when { dir.x > 0 -> 0.12f; dir.x < 0 -> -0.12f; else -> 0f }
        val ey = when { dir.y > 0 -> 0.12f; dir.y < 0 -> -0.12f; else -> 0f }
        paint.color = Color.WHITE
        c.drawCircle(ox + (h.x + 0.5f) * cell + cell * (0.13f + ex), oy + (h.y + 0.5f) * cell + cell * (0.13f + ey), cell * 0.075f, paint)
        c.drawCircle(ox + (h.x + 0.5f) * cell - cell * (0.13f - ex), oy + (h.y + 0.5f) * cell - cell * (0.13f - ey), cell * 0.075f, paint)
    }

    private fun drawParticles(c: Canvas) {
        particles.forEach {
            paint.color = Color.argb((it.life * 255).toInt().coerceIn(0, 255), Color.red(it.color), Color.green(it.color), Color.blue(it.color))
            c.drawCircle(ox + (it.x + 0.5f) * cell, oy + (it.y + 0.5f) * cell, max(2f, cell * 0.05f), paint)
        }
        text.textAlign = Paint.Align.CENTER; text.textSize = cell * 0.3f
        floats.forEach {
            text.color = Color.argb((it.life * 255).toInt().coerceIn(0, 255), 255, 215, 0)
            c.drawText(it.text, ox + (it.x + 0.5f) * cell, oy + (it.y + 0.3f) * cell, text)
        }
    }

    private fun drawDangerGauge(c: Canvas, cx: Float, cy: Float, r: Float, danger: Int) {
        val arcPaint = Paint(Paint.ANTI_ALIAS_FLAG)
        arcPaint.style = Paint.Style.STROKE; arcPaint.strokeWidth = 13f; arcPaint.strokeCap = Paint.Cap.ROUND
        val oval = RectF(cx - r, cy - r, cx + r, cy + r)
        arcPaint.color = Color.rgb(50, 50, 50); c.drawArc(oval, -90f, 360f, false, arcPaint)
        arcPaint.color = when (danger) {
            1 -> Color.GREEN; 2 -> Color.rgb(150, 255, 80); 3 -> Color.YELLOW
            4 -> Color.rgb(255, 150, 0); else -> Color.RED
        }
        c.drawArc(oval, -90f, 360f * (danger.coerceIn(1, 5) / 5f), false, arcPaint)
    }

    private val prevWeights = FloatArray(8) { 1f }

    private fun drawWeightBars(c: Canvas, left: Float, top: Float, w: Float, h: Float) {
        val names = listOf("区域", "机动", "尾+", "尾-", "食近", "食吃", "边界", "空间")
        val values = floatArrayOf(
            wRegion / wRegion0, wMobility / wMobility0, wTailGood / wTailGood0, wTailBad / wTailBad0,
            wFoodNear / wFoodNear0, wFoodAte / wFoodAte0, wEdge / wEdge0, wSpace / wSpace0
        )
        val barW = w / names.size; val maxRatio = 2.0f
        names.forEachIndexed { i, name ->
            val x = left + i * barW; val ratio = values[i].coerceIn(0f, maxRatio)
            val barH = h * (ratio / maxRatio)
            barPaint.style = Paint.Style.FILL; barPaint.color = Color.rgb(40, 40, 40)
            c.drawRect(x + 3f, top, x + barW - 8f, top + h, barPaint)
            barPaint.color = Color.rgb(100, 100, 100)
            val baseY = top + h - h * (1f / maxRatio)
            c.drawLine(x + 3f, baseY, x + barW - 8f, baseY, barPaint)
            val prevRatio = prevWeights.getOrElse(i) { 1f }
            val delta = ratio - prevRatio; prevWeights[i] = ratio
            barPaint.color = when {
                delta > 0.05f -> Color.rgb(46, 204, 113)
                delta < -0.05f -> Color.rgb(46, 204, 113)
                ratio > 1.3f -> Color.rgb(46, 204, 113)
                ratio > 1.1f -> Color.rgb(241, 196, 15)
                ratio < 0.8f -> Color.rgb(52, 152, 219)
                else -> Color.rgb(46, 204, 113)
            }
            c.drawRect(x + 3f, top + h - barH, x + barW - 8f, top + h, barPaint)
            text.textAlign = Paint.Align.CENTER; text.textSize = 12f; text.color = Color.LTGRAY
            c.drawText(name, x + (barW - 5f) / 2f, top + h + 15f, text)
            text.color = Color.WHITE
            c.drawText("${(values[i] * 100f).toInt()}%", x + (barW - 5f) / 2f, top + h + 30f, text)
        }
        text.textAlign = Paint.Align.LEFT
    }

    private fun drawLearningCurve(c: Canvas, left: Float, top: Float, w: Float, h: Float) {
        barPaint.style = Paint.Style.FILL; barPaint.color = Color.rgb(25, 25, 25)
        c.drawRect(left, top, left + w, top + h, barPaint)
        if (recentScores.size < 2) {
            text.textAlign = Paint.Align.CENTER; text.textSize = 13f; text.color = Color.GRAY
            c.drawText("数据不足", left + w / 2f, top + h / 2f, text)
            text.textAlign = Paint.Align.LEFT; return
        }
        val scores = recentScores.toList(); val maxScore = scores.max().coerceAtLeast(1)
        val stepX = w / (scores.size - 1).coerceAtLeast(1)
        val areaPath = Path(); areaPath.moveTo(left, top + h)
        scores.forEachIndexed { i, s -> areaPath.lineTo(left + i * stepX, top + h - h * (s.toFloat() / maxScore)) }
        areaPath.lineTo(left + w, top + h); areaPath.close()
        barPaint.color = Color.argb(60, 120, 255, 180); c.drawPath(areaPath, barPaint)
        val linePath = Path()
        scores.forEachIndexed { i, s ->
            val x = left + i * stepX; val y = top + h - h * (s.toFloat() / maxScore)
            if (i == 0) linePath.moveTo(x, y) else linePath.lineTo(x, y)
        }
        val curvePaint = Paint(Paint.ANTI_ALIAS_FLAG)
        curvePaint.style = Paint.Style.STROKE; curvePaint.strokeWidth = 3f
        curvePaint.color = Color.rgb(120, 255, 180); c.drawPath(linePath, curvePaint)
        text.textSize = 12f; text.color = Color.LTGRAY
        c.drawText("max $maxScore", left + 5f, top + 14f, text)
    }

    private fun drawDeathPie(c: Canvas, cx: Float, cy: Float, r: Float) {
        val totalD = deathWall + deathSelf + deathTrap
        barPaint.style = Paint.Style.FILL
        if (totalD == 0) { barPaint.color = Color.rgb(60, 60, 60); c.drawCircle(cx, cy, r, barPaint); return }
        val oval = RectF(cx - r, cy - r, cx + r, cy + r); var start = -90f
        val sweepW = 360f * deathWall / totalD
        if (sweepW > 0f) { barPaint.color = Color.rgb(255, 100, 100); c.drawArc(oval, start, sweepW, true, barPaint); start += sweepW }
        val sweepS = 360f * deathSelf / totalD
        if (sweepS > 0f) { barPaint.color = Color.rgb(100, 150, 255); c.drawArc(oval, start, sweepS, true, barPaint); start += sweepS }
        val sweepT = 360f * deathTrap / totalD
        if (sweepT > 0f) { barPaint.color = Color.rgb(255, 200, 100); c.drawArc(oval, start, sweepT, true, barPaint) }
    }

    private fun drawQHeatmap(c: Canvas, left: Float, top: Float, w: Float, h: Float) {
        val grid = 10; val cellW = w / grid; val cellH = h / grid
        barPaint.style = Paint.Style.FILL; barPaint.color = Color.rgb(35, 35, 35)
        c.drawRect(left, top, left + w, top + h, barPaint)
        val sampleList = visitedStates.take(100); var maxAbs = 0.001f
        for (s in sampleList) for (a in 0 until 4) { val qv = qRead(s, a); if (abs(qv) > maxAbs) maxAbs = abs(qv) }
        for (i in 0 until 100) {
            val px = left + (i % grid) * cellW; val py = top + (i / grid) * cellH
            if (i >= sampleList.size) barPaint.color = Color.rgb(30, 30, 35)
            else {
                val s = sampleList[i]; var bestQ = -Float.MAX_VALUE
                for (a in 0 until 4) { val qv = qRead(s, a); if (qv > bestQ) bestQ = qv }
                val t = (bestQ / maxAbs).coerceIn(-1f, 1f)
                barPaint.color = if (t >= 0f) Color.rgb((60 * (1f - t)).toInt(), (60 + 195 * t).toInt(), 60)
                else { val nt = -t; Color.rgb((60 + 195 * nt).toInt(), (60 * (1f - nt)).toInt(), (60 * (1f - nt)).toInt()) }
            }
            c.drawRect(px, py, px + cellW - 1f, py + cellH - 1f, barPaint)
        }
    }

    private fun drawV3Panel(c: Canvas, w: Float, mainTop: Float) {
        if (mainTop < 290f) return
        val panelH = 272f; val left = (width - w) / 2f; val top = mainTop - 14f - panelH
        panel.color = Color.argb(232, 0, 0, 0)
        c.drawRoundRect(left, top, left + w, top + panelH, 22f, 22f, panel)
        val pulse = 0.55f + 0.45f * kotlin.math.sin(System.currentTimeMillis() / 160f)
        text.isFakeBoldText = true; text.textSize = 15f; text.color = Color.rgb(255, 200, 100)
        text.textAlign = Paint.Align.LEFT
        c.drawText("【V4融合 · AI层级链】", left + 16f, top + 24f, text)
        text.isFakeBoldText = true; text.textSize = 14f; val goalColor = v3Goal.color
        text.color = Color.argb((90 + 165 * pulse).toInt().coerceIn(0, 255), (goalColor shr 16) and 0xFF, (goalColor shr 8) and 0xFF, goalColor and 0xFF)
        c.drawText("目标: ${v3Goal.label}", left + w - 210f, top + 24f, text)
        text.textSize = 12f
        text.color = if (v3FusionEnabled) Color.rgb(46, 204, 113) else Color.rgb(120, 120, 120)
        c.drawText(if (v3FusionEnabled) "融合:开" else "融合:关", left + w - 70f, top + 24f, text)
        val layerNames = arrayOf("L1安全食物", "L2尾巴", "L3饥饿", "L4混合", "L5反事实", "L6基因")
        val layerColors = intArrayOf(
            Color.rgb(46, 204, 113), Color.rgb(155, 89, 182), Color.rgb(230, 126, 34),
            Color.rgb(52, 152, 219), Color.rgb(231, 76, 60), Color.rgb(241, 196, 15)
        )
        val chipGap = 6f; val chipW = (w - 32f - chipGap * 5f) / 6f
        val chipY = top + 34f; val chipH = 24f
        for (i in 0 until 6) {
            val cx = left + 16f + i * (chipW + chipGap)
            val active = (v3LayerActive == i + 1) && v3FusionEnabled
            panel.color = if (active) Color.argb((120 + 135 * pulse).toInt().coerceIn(0, 255), (layerColors[i] shr 16) and 0xFF, (layerColors[i] shr 8) and 0xFF, layerColors[i] and 0xFF)
            else Color.rgb(30, 30, 40)
            c.drawRoundRect(cx, chipY, cx + chipW, chipY + chipH, 8f, 8f, panel)
            text.isFakeBoldText = active; text.textSize = 10f
            text.color = if (active) Color.WHITE else Color.rgb(140, 140, 150)
            text.textAlign = Paint.Align.CENTER
            c.drawText(layerNames[i], cx + chipW / 2f, chipY + chipH / 2f + 4f, text)
        }
        text.textAlign = Paint.Align.LEFT
        text.isFakeBoldText = false; text.textSize = 12f; text.color = Color.rgb(180, 190, 205)
        val whyLine = if (v3FusionEnabled) { if (v3Regret > 0.01f) "$v3LayerWhy  遗憾=${"%.2f".format(v3Regret)}" else v3LayerWhy } else "V3层级已关闭，运行V2基线决策"
        c.drawText(whyLine, left + 16f, top + 76f, text)
        text.isFakeBoldText = true; text.textSize = 13f; text.color = Color.rgb(255, 150, 255)
        c.drawText("【V3基因柱状图】", left + 16f, top + 98f, text)
        val geneNames = arrayOf("食", "空", "尾", "危", "循", "饿")
        val gv = v3Genome.values()
        val geneColors = intArrayOf(
            Color.rgb(46, 204, 113), Color.rgb(52, 152, 219), Color.rgb(155, 89, 182),
            Color.rgb(231, 76, 60), Color.rgb(241, 196, 15), Color.rgb(230, 126, 34)
        )
        val geneAreaLeft = left + 16f; val geneAreaW = w * 0.52f
        val barGap = 5f; val geneBarW = (geneAreaW - barGap * 5f) / 6f
        val geneBaseY = top + 158f; val geneMaxH = 44f
        for (i in 0 until 6) {
            val bx = geneAreaLeft + i * (geneBarW + barGap)
            val frac = (gv[i] / 2.6f).coerceIn(0.05f, 1f); val bh = geneMaxH * frac
            panel.color = Color.rgb(30, 30, 40)
            c.drawRoundRect(bx, geneBaseY - geneMaxH, bx + geneBarW, geneBaseY, 4f, 4f, panel)
            panel.color = geneColors[i]
            c.drawRoundRect(bx, geneBaseY - bh, bx + geneBarW, geneBaseY, 4f, 4f, panel)
            text.isFakeBoldText = false; text.textSize = 11f; text.color = Color.rgb(160, 165, 175)
            text.textAlign = Paint.Align.CENTER
            c.drawText(geneNames[i], bx + geneBarW / 2f, geneBaseY + 12f, text)
            text.textSize = 9f; text.color = Color.rgb(210, 210, 220)
            c.drawText(String.format("%.2f", gv[i]), bx + geneBarW / 2f, geneBaseY - bh - 3f, text)
        }
        text.textAlign = Paint.Align.LEFT
        val infoX = left + w * 0.60f
        text.isFakeBoldText = false; text.textSize = 12f; text.color = Color.rgb(180, 190, 205)
        c.drawText("失败记忆: ${v3Memory.size()} 条", infoX, top + 118f, text)
        c.drawText("教训触发: ${v3LessonFires} 次", infoX, top + 136f, text)
        c.drawText("循环打断: ${v3LoopHits} 次", infoX, top + 154f, text)
        c.drawText("Beam 命中: $beamSelected/$beamCalls", infoX, top + 172f, text)
        text.textSize = 12f
        if (v3LessonFlash > 0.01f) {
            val a = (v3LessonFlash * 255f).toInt().coerceIn(0, 255)
            text.isFakeBoldText = true
            text.color = Color.argb(a, 255, 90 + ((60 * pulse).toInt()), 40)
            c.drawText("⚠ 新教训已写入: ${v3Memory.worstLessonText()}", left + 16f, top + 196f, text)
        } else {
            text.isFakeBoldText = false; text.color = Color.rgb(130, 135, 145)
            c.drawText("最近教训: ${v3Memory.worstLessonText()}", left + 16f, top + 196f, text)
        }
        text.isFakeBoldText = true; text.textSize = 13f; text.color = Color.rgb(255, 150, 255)
        c.drawText("【V3目标分布饼图】", left + 16f, top + 224f, text)
        val pieCx = left + w - 64f; val pieCy = top + 206f; val pieR = 42f
        val totalCnt = v3GoalCounter.sum()
        if (totalCnt <= 0) { panel.color = Color.rgb(30, 30, 40); c.drawCircle(pieCx, pieCy, pieR, panel) }
        else {
            var startAngle = -90f
            for (g in V3Goal.values()) {
                val cnt = v3GoalCounter[g.ordinal]; if (cnt <= 0) continue
                val sweep = cnt * 360f / totalCnt
                panel.color = g.color
                c.drawArc(pieCx - pieR, pieCy - pieR, pieCx + pieR, pieCy + pieR, startAngle, sweep, true, panel)
                startAngle += sweep
            }
            panel.color = Color.argb(232, 0, 0, 0); c.drawCircle(pieCx, pieCy, pieR * 0.45f, panel)
        }
        text.isFakeBoldText = false; text.textSize = 11f; var ly = top + 242f
        for (g in V3Goal.values()) {
            val cnt = v3GoalCounter[g.ordinal]
            val pct = if (totalCnt > 0) cnt * 100 / totalCnt else 0
            text.color = g.color; c.drawText("■", left + 18f, ly, text)
            text.color = Color.rgb(170, 175, 185)
            c.drawText("${g.label} $pct%", left + 34f, ly, text)
            ly += 14f; if (ly > top + panelH - 6f) break
        }
        text.isFakeBoldText = false; text.textSize = 14f; text.color = Color.WHITE
    }

    private fun drawTrainingDashboard(c: Canvas) {
        val W = width.toFloat(); val pad = W * 0.022f; var y = pad
        panel.color = Color.rgb(28, 24, 48)
        c.drawRoundRect(pad, y, W - pad, y + W * 0.155f, pad * 0.7f, pad * 0.7f, panel)
        text.textAlign = Paint.Align.LEFT; text.isFakeBoldText = true
        text.textSize = W * 0.062f; text.color = Color.rgb(150, 230, 255)
        c.drawText("🧬 第 $generation 代", pad * 1.6f, y + W * 0.068f, text)
        text.textSize = W * 0.034f
        text.color = if (evolving || generationTransitioning) Color.rgb(255, 180, 80) else Color.rgb(120, 230, 150)
        val headState = if (evolving || generationTransitioning) "⚙ 进化繁殖中..." else "▶ 训练运行中"
        text.textAlign = Paint.Align.RIGHT
        c.drawText(headState, W - pad * 1.6f, y + W * 0.06f, text)
        text.textAlign = Paint.Align.LEFT; text.textSize = W * 0.032f; text.color = Color.rgb(200, 200, 220)
        c.drawText("已分配 $currentAgentIndex/$POPULATION_SIZE   已完成 $completedAgents/$POPULATION_SIZE   总局数 $totalGames",
            pad * 1.6f, y + W * 0.118f, text)
        y += W * 0.155f + pad * 0.6f
        val barH = W * 0.022f
        panel.color = Color.rgb(50, 48, 66)
        c.drawRoundRect(pad, y, W - pad, y + barH, barH / 2, barH / 2, panel)
        val frac = (completedAgents.toFloat() / POPULATION_SIZE).coerceIn(0f, 1f)
        panel.color = Color.rgb(80, 220, 150)
        if (frac > 0.01f) c.drawRoundRect(pad, y, pad + (W - 2 * pad) * frac, y + barH, barH / 2, barH / 2, panel)
        y += barH + pad
        val cardW = (W - 3 * pad) / 2f; val cardH = W * 0.118f
        val phaseColor = mapOf(
            "捕食" to Color.rgb(255, 170, 60), "避险" to Color.rgb(255, 90, 90),
            "搜索" to Color.rgb(90, 170, 255), "进化" to Color.rgb(200, 130, 255),
            "等待" to Color.rgb(130, 130, 140), "空闲" to Color.rgb(100, 100, 110),
            "训练" to Color.rgb(120, 220, 150)
        )
        for (ti in 0 until 8) {
            val col = ti % 2; val row = ti / 2
            val x0 = pad + col * (cardW + pad); val y0 = y + row * (cardH + pad * 0.55f)
            val st = threadStatus[ti]
            panel.color = Color.rgb(24, 26, 38)
            c.drawRoundRect(x0, y0, x0 + cardW, y0 + cardH, pad * 0.5f, pad * 0.5f, panel)
            paint.color = phaseColor[st.phase] ?: Color.GRAY
            c.drawCircle(x0 + pad * 0.8f, y0 + pad * 0.9f, pad * 0.32f, paint)
            text.textSize = W * 0.029f; text.isFakeBoldText = true; text.color = Color.WHITE
            c.drawText("线程$ti · Agent ${if (st.agentId >= 0) st.agentId else "-"}", x0 + pad * 1.5f, y0 + pad * 1.15f, text)
            text.textAlign = Paint.Align.RIGHT; text.color = paint.color
            c.drawText(st.phase, x0 + cardW - pad * 0.7f, y0 + pad * 1.15f, text)
            text.textAlign = Paint.Align.LEFT; text.textSize = W * 0.045f; text.color = Color.rgb(150, 235, 170)
            c.drawText("${st.score}", x0 + pad * 0.9f, y0 + cardH - pad * 0.55f, text)
            text.textSize = W * 0.026f; text.color = Color.rgb(160, 165, 185); text.textAlign = Paint.Align.RIGHT
            c.drawText("步 ${st.steps}", x0 + cardW - pad * 0.7f, y0 + cardH - pad * 0.6f, text)
            text.textAlign = Paint.Align.LEFT
        }
        y += 4 * cardH + 3 * pad * 0.55f + pad * 0.4f
        val metrics = arrayOf(
            "本代最佳" to "%.0f".format(bestScoreThisGen), "历史最佳" to "%.0f".format(bestScoreAllTime),
            "Q权重" to "%.2f".format(qWeight), "NN权重" to "%.2f".format(nnWeight),
            "回放" to "${replayBuffer.size}", "ε" to "%.3f".format(v2Epsilon),
            "学习步" to "$v2LearningSteps", "Beam" to "$beamSelected/$beamCalls"
        )
        val mW = (W - 5 * pad) / 4f; val mH = W * 0.105f
        for (mi in metrics.indices) {
            val col = mi % 4; val row = mi / 4
            val x0 = pad + col * (mW + pad); val y0 = y + row * (mH + pad * 0.5f)
            panel.color = Color.rgb(30, 30, 44)
            c.drawRoundRect(x0, y0, x0 + mW, y0 + mH, pad * 0.4f, pad * 0.4f, panel)
            text.textSize = W * 0.024f; text.isFakeBoldText = false; text.color = Color.rgb(150, 155, 175)
            c.drawText(metrics[mi].first, x0 + pad * 0.5f, y0 + pad * 0.95f, text)
            text.textSize = W * 0.040f; text.isFakeBoldText = true; text.color = Color.WHITE
            c.drawText(metrics[mi].second, x0 + pad * 0.5f, y0 + mH - pad * 0.5f, text)
        }
        y += 2 * mH + pad * 0.5f + pad
        text.textSize = W * 0.034f; text.isFakeBoldText = true; text.color = Color.rgb(200, 170, 255)
        c.drawText("🧪 进化繁殖历程", pad * 0.4f, y, text); y += pad * 0.7f
        val fullHistory = evoHistory.toList()
        val history = if (fullHistory.size > 10) fullHistory.drop(fullHistory.size - 10) else fullHistory
        val rowH = W * 0.052f
        if (history.isEmpty()) {
            text.textSize = W * 0.028f; text.isFakeBoldText = false; text.color = Color.rgb(140, 140, 155)
            c.drawText("（等待第一代50只完成后开始进化…）", pad * 0.6f, y + rowH * 0.6f, text)
            y += rowH
        }
        for (rec in history) {
            text.textSize = W * 0.026f; text.isFakeBoldText = true; text.color = Color.WHITE
            c.drawText("G${rec.gen}", pad * 0.5f, y + rowH * 0.62f, text)
            val barX = pad * 2.6f; val barW = W * 0.46f; val bh2 = rowH * 0.42f
            val total = (rec.eliteN + rec.crossN + rec.breedN).coerceAtLeast(1)
            var bx = barX
            val seg = arrayOf(rec.eliteN to Color.rgb(70, 220, 130), rec.crossN to Color.rgb(80, 150, 255), rec.breedN to Color.rgb(255, 160, 70))
            for ((cnt, col) in seg) {
                val wseg = barW * (cnt.toFloat() / total)
                if (wseg > 0.5f) { panel.color = col; c.drawRect(bx, y, bx + wseg, y + bh2, panel) }
                bx += wseg
            }
            text.textSize = W * 0.025f; text.isFakeBoldText = false; text.color = Color.rgb(180, 240, 190)
            c.drawText("最佳%.0f".format(rec.bestScore), barX + barW + pad * 0.5f, y + rowH * 0.55f, text)
            text.color = Color.rgb(230, 200, 140); text.textAlign = Paint.Align.RIGHT
            c.drawText(rec.personality, W - pad * 0.5f, y + rowH * 0.55f, text)
            text.textAlign = Paint.Align.LEFT; y += rowH + pad * 0.18f
        }
        y += pad * 0.4f
        text.textSize = W * 0.032f; text.isFakeBoldText = true; text.color = Color.rgb(255, 150, 150)
        c.drawText("☠ 死因分布", pad * 0.4f, y, text); y += pad * 0.7f
        val deaths = arrayOf("撞墙" to deathWall, "撞自己" to deathSelf, "被困" to deathTrap)
        val maxDeath = max(1, max(deathWall, max(deathSelf, deathTrap)))
        val dRowH = W * 0.05f
        for ((name, cnt) in deaths) {
            text.textSize = W * 0.027f; text.isFakeBoldText = false; text.color = Color.WHITE
            c.drawText(name, pad * 0.6f, y + dRowH * 0.6f, text)
            val dx0 = pad * 2.4f; val dW = W * 0.55f
            panel.color = Color.rgb(60, 50, 60)
            c.drawRect(dx0, y + dRowH * 0.18f, dx0 + dW, y + dRowH * 0.62f, panel)
            panel.color = Color.rgb(235, 90, 90)
            val wf = dW * (cnt.toFloat() / maxDeath)
            if (wf > 0.5f) c.drawRect(dx0, y + dRowH * 0.18f, dx0 + wf, y + dRowH * 0.62f, panel)
            text.color = Color.rgb(220, 220, 230)
            c.drawText("$cnt", dx0 + dW + pad * 0.5f, y + dRowH * 0.6f, text)
            y += dRowH + pad * 0.15f
        }
        y += pad * 0.3f
        val bottom0 = y
        panel.color = Color.rgb(20, 30, 34)
        c.drawRoundRect(pad, bottom0, W - pad, height - pad, pad * 0.6f, pad * 0.6f, panel)
        text.textSize = W * 0.033f; text.isFakeBoldText = true; text.color = Color.rgb(120, 230, 200)
        val nowDoing = when {
            evolving || generationTransitioning -> "🧬 正在繁殖下一代：精英保留 + 交叉 + 变异"
            completedAgents >= POPULATION_SIZE - 2 -> "⏳ 本代即将完成，准备进化"
            else -> "🐍 8只小蛇并行训练，吃满CPU搜索+学习"
        }
        c.drawText(nowDoing, pad * 1.4f, bottom0 + pad * 1.4f, text)
        text.textSize = W * 0.026f; text.isFakeBoldText = false; text.color = Color.rgb(170, 200, 210)
        val why = v3LayerWhy
        c.drawText(why.take(46), pad * 1.4f, bottom0 + pad * 2.6f, text)
        if (why.length > 46) c.drawText(why.substring(46), pad * 1.4f, bottom0 + pad * 3.6f, text)
        text.color = Color.rgb(150, 180, 200)
        c.drawText("目标: $v3Goal   循环命中$v3LoopHits  教训触发$v3LessonFires   已分配$currentAgentIndex 已完成$completedAgents",
            pad * 1.4f, bottom0 + pad * 4.8f, text)
    }

    private fun drawDebug(c: Canvas) {
        if (aiMode == 0 && !reinforceTraining) return
        val w = min(width * 0.97f, 720f); val h = 760f
        val left = (width - w) / 2f; val top = max(12f, height - h - 12f)
        drawV3Panel(c, w, top)
        panel.color = Color.argb(232, 0, 0, 0)
        c.drawRoundRect(left, top, left + w, top + h, 22f, 22f, panel)
        border.color = Color.argb(60, 46, 204, 113); border.style = Paint.Style.STROKE; border.strokeWidth = 1.5f
        c.drawRoundRect(left, top, left + w, top + h, 22f, 22f, border)
        text.textAlign = Paint.Align.LEFT; text.isFakeBoldText = true; text.textSize = 26f; text.color = Color.WHITE
        c.drawText(if (reinforceTraining) "混合进化中 · 世代 $generation" else ai.strategy, left + 16f, top + 36f, text)
        text.isFakeBoldText = false; text.textSize = 14f; text.color = Color.YELLOW
        c.drawText(if (reinforceTraining) "规则过滤 + Q表 + 神经网络 自我迭代" else ai.reason, left + 16f, top + 58f, text)
        val gaugeCX = left + 58f; val gaugeCY = top + 116f
        if (reinforceTraining) {
            val progRatio = completedAgents.toFloat() / POPULATION_SIZE
            val arcPaint = Paint(Paint.ANTI_ALIAS_FLAG)
            arcPaint.style = Paint.Style.STROKE; arcPaint.strokeWidth = 13f; arcPaint.strokeCap = Paint.Cap.ROUND
            val oval = RectF(gaugeCX - 42f, gaugeCY - 42f, gaugeCX + 42f, gaugeCY + 42f)
            arcPaint.color = Color.rgb(50, 50, 50); c.drawArc(oval, -90f, 360f, false, arcPaint)
            arcPaint.color = Color.rgb(46, 204, 113); c.drawArc(oval, -90f, 360f * progRatio, false, arcPaint)
            text.textAlign = Paint.Align.CENTER; text.isFakeBoldText = true; text.textSize = 22f; text.color = Color.WHITE
            c.drawText("$generation", gaugeCX, gaugeCY + 8f, text)
            text.isFakeBoldText = false; text.textSize = 11f; text.color = Color.LTGRAY
            c.drawText("世代", gaugeCX, gaugeCY + 28f, text)
        } else {
            drawDangerGauge(c, gaugeCX, gaugeCY, 42f, ai.danger)
            text.textAlign = Paint.Align.CENTER; text.isFakeBoldText = true; text.textSize = 26f; text.color = Color.WHITE
            c.drawText("${ai.danger}", gaugeCX, gaugeCY + 9f, text)
            text.isFakeBoldText = false; text.textSize = 12f; text.color = Color.LTGRAY
            c.drawText("危险", gaugeCX, gaugeCY + 28f, text)
        }
        text.textAlign = Paint.Align.LEFT; text.textSize = 16f; text.color = Color.WHITE
        c.drawText("局数 $totalGames", left + 118f, top + 86f, text)
        val avg = if (recentScores.isEmpty()) 0f else recentScores.average().toFloat()
        c.drawText("近50均分 ${"%.0f".format(avg)}   最佳 $bestRecentScore", left + 118f, top + 110f, text)
        val threadInfo = if (reinforceTraining) "${trainThreads.size} 线程" else "单局"
        c.drawText("模式 $threadInfo   主蛇长 ${snake.size}   Q覆盖${visitedStates.size}", left + 118f, top + 134f, text)
        if (reinforceTraining) {
            barPaint.style = Paint.Style.FILL; var meterY = top + 155f; val meterW = w - 32f
            text.textSize = 9f; text.color = Color.rgb(200, 180, 255)
            c.drawText("Q覆盖 ${visitedStates.size}/$V2_STATE_COUNT", left + 16f, meterY + 8f, text)
            barPaint.color = Color.rgb(30, 30, 40)
            c.drawRoundRect(left + 16f, meterY + 12f, left + 16f + meterW, meterY + 19f, 3f, 3f, barPaint)
            barPaint.color = Color.rgb(200, 150, 255)
            val qCovR = (visitedStates.size.toFloat() / V2_STATE_COUNT).coerceIn(0f, 1f)
            c.drawRoundRect(left + 16f, meterY + 12f, left + 16f + meterW * qCovR, meterY + 19f, 3f, 3f, barPaint)
            meterY += 24f
            text.color = Color.rgb(100, 220, 255)
            c.drawText("回放 ${replayBuffer.size}/$REPLAY_CAPACITY", left + 16f, meterY + 8f, text)
            barPaint.color = Color.rgb(30, 30, 40)
            c.drawRoundRect(left + 16f, meterY + 12f, left + 16f + meterW, meterY + 19f, 3f, 3f, barPaint)
            barPaint.color = Color.rgb(100, 200, 255)
            val rpR = replayBuffer.size.toFloat() / REPLAY_CAPACITY
            c.drawRoundRect(left + 16f, meterY + 12f, left + 16f + meterW * rpR, meterY + 19f, 3f, 3f, barPaint)
            meterY += 24f
            text.color = Color.rgb(241, 196, 15)
            c.drawText("ε ${"%.2f".format(v2Epsilon)}", left + 16f, meterY + 8f, text)
            barPaint.color = Color.rgb(30, 30, 40)
            c.drawRoundRect(left + 16f, meterY + 12f, left + 16f + meterW, meterY + 19f, 3f, 3f, barPaint)
            barPaint.color = Color.rgb(241, 196, 15)
            c.drawRoundRect(left + 16f, meterY + 12f, left + 16f + meterW * v2Epsilon, meterY + 19f, 3f, 3f, barPaint)
            meterY += 24f
            text.color = Color.rgb(200, 200, 200)
            c.drawText("Q ${"%.2f".format(qWeight)} / NN ${"%.2f".format(nnWeight)}", left + 16f, meterY + 8f, text)
            barPaint.color = Color.rgb(30, 30, 40)
            c.drawRoundRect(left + 16f, meterY + 12f, left + 16f + meterW, meterY + 19f, 3f, 3f, barPaint)
            barPaint.color = Color.rgb(231, 76, 60)
            c.drawRoundRect(left + 16f, meterY + 12f, left + 16f + meterW * qWeight, meterY + 19f, 3f, 3f, barPaint)
            barPaint.color = Color.rgb(46, 204, 113)
            c.drawRoundRect(left + 16f + meterW * qWeight, meterY + 12f, left + 16f + meterW, meterY + 19f, 3f, 3f, barPaint)
        }
        val wbY = top + 250f
        text.isFakeBoldText = true; text.textSize = 14f; text.color = Color.rgb(255, 200, 100)
        c.drawText("【权重柱状图】", left + 16f, wbY, text)
        text.isFakeBoldText = false
        drawWeightBars(c, left + 16f, wbY + 8f, w - 32f, 66f)
        val learnY = top + 290f
        text.isFakeBoldText = true; text.textSize = 14f; text.color = Color.rgb(255, 150, 255)
        c.drawText("【V2学习】", left + 16f, learnY, text)
        text.isFakeBoldText = false; text.color = Color.WHITE
        c.drawText("训练中", left + 118f, learnY, text)
        val barStartX = left + 118f; val barEndX = left + w - 16f; val barW = barEndX - barStartX
        var barY = top + 318f
        if (!reinforceTraining) {
            text.isFakeBoldText = true; text.textSize = 14f; text.color = Color.rgb(255, 200, 100)
            c.drawText("【四方向安全 / Q】", left + 16f, barY, text)
            text.isFakeBoldText = false; barY += 10f
            val dirNames = listOf("UP", "DN", "LF", "RT")
            ai.candidates.forEachIndexed { idx, cand ->
                text.textSize = 18f
                text.color = if (!cand.legal) Color.GRAY else if (cand.d == ai.chosen) Color.CYAN else Color.WHITE
                c.drawText(dirNames[idx], left + 16f, barY + 19f, text)
                if (!cand.legal) {
                    text.textSize = 14f; text.color = Color.GRAY
                    c.drawText("非法", barStartX, barY + 19f, text)
                } else {
                    val regionRatio = if (snake.isNotEmpty()) cand.region.toFloat() / snake.size else 0f
                    val safeScore = when {
                        cand.tailOk && regionRatio >= 1.5f -> 1.0f
                        cand.tailOk && regionRatio >= 1.0f -> 0.75f
                        regionRatio >= 1.0f -> 0.5f
                        regionRatio >= 0.6f -> 0.3f
                        else -> 0.15f
                    }
                    barPaint.color = Color.rgb(40, 40, 40); barPaint.style = Paint.Style.FILL
                    c.drawRoundRect(barStartX, barY, barEndX, barY + 24f, 4f, 4f, barPaint)
                    val barColor = when {
                        safeScore >= 0.9f -> Color.rgb(46, 204, 113)
                        safeScore >= 0.7f -> Color.rgb(241, 196, 15)
                        safeScore >= 0.5f -> Color.rgb(230, 126, 34)
                        else -> Color.rgb(231, 76, 60)
                    }
                    barPaint.color = barColor
                    c.drawRoundRect(barStartX, barY, barStartX + barW * safeScore, barY + 24f, 4f, 4f, barPaint)
                    text.textSize = 13f; text.color = Color.WHITE
                    c.drawText("空间${cand.region} 尾${if (cand.tailOk) "Y" else "N"} 食${if (cand.foodDist < 0) "∞" else cand.foodDist} Q${"%.2f".format(cand.qValue)}",
                        barStartX + 8f, barY + 18f, text)
                }
                barY += 28f
            }
        } else barY = top + 318f
        val chartY = barY + 20f; val chartH = 72f
        val curveX = left + 16f; val curveW = (w - 32f) * 0.55f
        text.isFakeBoldText = true; text.textSize = 14f; text.color = Color.rgb(120, 255, 180)
        c.drawText("【历史分数】", curveX, chartY, text)
        text.isFakeBoldText = false
        drawLearningCurve(c, curveX, chartY + 8f, curveW, chartH)
        val pieCX = left + w - 130f; val pieCY = chartY + chartH / 2f + 14f; val pieR = 34f
        text.isFakeBoldText = true; text.textSize = 14f; text.color = Color.rgb(255, 150, 150)
        c.drawText("【死亡统计】", pieCX - 52f, chartY, text)
        text.isFakeBoldText = false
        drawDeathPie(c, pieCX, pieCY, pieR)
        text.textSize = 13f; text.color = Color.rgb(255, 100, 100)
        c.drawText("W $deathWall", pieCX + 42f, pieCY - 16f, text)
        text.color = Color.rgb(100, 150, 255); c.drawText("S $deathSelf", pieCX + 42f, pieCY + 4f, text)
        text.color = Color.rgb(255, 200, 100); c.drawText("T $deathTrap", pieCX + 42f, pieCY + 24f, text)
        val heatY = chartY + chartH + 30f
        text.textAlign = Paint.Align.LEFT; text.isFakeBoldText = true; text.textSize = 14f; text.color = Color.rgb(200, 180, 255)
        c.drawText("【V2 Q表热度】", left + 16f, heatY, text)
        text.isFakeBoldText = false
        drawQHeatmap(c, left + 16f, heatY + 8f, w - 32f, 66f)
        val infoY = heatY + 8f + 66f + 22f
        var visited = 0; var sumQ = 0f; var cntQ = 0
        val sampleStep = max(1, V2_STATE_COUNT / 400)
        for (s in 0 until V2_STATE_COUNT step sampleStep) for (a in 0 until 4) {
            val idx = qIndex(s, a); if (nV2[idx] > 0) { visited++; sumQ += qV2[idx]; cntQ++ }
        }
        val avgQ = if (cntQ > 0) sumQ / cntQ else 0f
        text.textSize = 14f; text.color = Color.WHITE; text.textAlign = Paint.Align.LEFT
        if (reinforceTraining) {
            c.drawText("世代 $generation   已分配 $currentAgentIndex/$POPULATION_SIZE   已完成 $completedAgents/$POPULATION_SIZE   Q覆盖${visitedStates.size}",
                left + 16f, infoY, text)
            c.drawText("本代最佳 ${"%.0f".format(bestScoreThisGen)}   历史最佳 ${"%.0f".format(bestScoreAllTime)}",
                left + 16f, infoY + 18f, text)
            c.drawText("Q表权重 ${"%.2f".format(qWeight)}   神经网络权重 ${"%.2f".format(nnWeight)}",
                left + 16f, infoY + 36f, text)
            c.drawText("回放${replayBuffer.size}/$REPLAY_CAPACITY   ε${"%.2f".format(v2Epsilon)}   步${v2LearningSteps}",
                left + 16f, infoY + 54f, text)
            val avgBeamNodes = if (beamCalls > 0) beamTotalNodes.toFloat() / beamCalls else 0f
            c.drawText("Beam 命中$beamSelected 调用$beamCalls 成功$beamSuccess 节点$beamTotalNodes 均$avgBeamNodes",
                left + 16f, infoY + 72f, text)
            val learnStatus = when {
                generation < 3 -> "🧬 初始化种群，随机试错中..."
                v2Epsilon > 0.15f -> "🔍 探索阶段：尝试新策略"
                v2Epsilon < 0.05f && nnWeight >= 0.45f -> "🧠 收敛阶段：神经网络主导"
                bestScoreThisGen > bestScoreAllTime * 0.95f && bestScoreAllTime > 0 -> "🚀 突破中！分数上升"
                bestScoreThisGen < bestScoreAllTime * 0.3f && bestScoreAllTime > 1000 -> "⚡ 瓶颈期，等待变异突破"
                else -> "📊 正常进化中..."
            }
            text.textSize = 13f; text.isFakeBoldText = true; text.color = Color.rgb(100, 220, 255)
            c.drawText(learnStatus, left + 16f, infoY + 92f, text)
            if (deadEndPredicted) {
                text.color = Color.rgb(255, 80, 80)
                c.drawText("⚠️ 死局预判！食物周围空间仅 ${"%.1f".format(foodSpaceRatio)}x 蛇长", left + 16f, infoY + 112f, text)
            } else {
                text.color = Color.rgb(80, 200, 120)
                c.drawText("✅ 食物空间 ${"%.1f".format(foodSpaceRatio)}x 蛇长", left + 16f, infoY + 112f, text)
            }
            text.color = if (rolloutActive) Color.rgb(180, 180, 255) else Color.rgb(100, 100, 120)
            c.drawText(if (rolloutActive) "🔮 前瞻模拟${rolloutSteps}步（蛇长${snake.size}）" else "🔮 前瞻模拟：蛇短不启用",
                left + 16f, infoY + 130f, text)
            text.isFakeBoldText = false; text.color = Color.WHITE; text.textSize = 14f
        } else {
            c.drawText("局数 $totalGames   近50均分 ${"%.0f".format(avg)}   最佳 $bestRecentScore", left + 16f, infoY, text)
            c.drawText("V2覆盖 $visited   平均Q ${"%.2f".format(avgQ)}   学习步 $v2LearningSteps", left + 16f, infoY + 18f, text)
            c.drawText("ε ${"%.3f".format(v2Epsilon)}   攻击x${"%.2f".format(aggression)}   安全x${"%.2f".format(safetyMargin)}", left + 16f, infoY + 36f, text)
        }
        if (gameOver && !reinforceTraining) {
            text.color = Color.RED; text.isFakeBoldText = true; text.textSize = 16f
            c.drawText("死亡原因：$deathCause", left + 16f, infoY + 62f, text)
            text.isFakeBoldText = false
        }
        val btnW = 160f; val btnH = 42f
        val btnLeft = left + w - btnW - 16f; val btnTop = infoY + 48f
        reinforceButtonRect.set(btnLeft, btnTop, btnLeft + btnW, btnTop + btnH)
        val btnColor = if (reinforceTraining) Color.rgb(231, 76, 60) else Color.rgb(46, 204, 113)
        panel.color = btnColor; c.drawRoundRect(reinforceButtonRect, 12f, 12f, panel)
        text.textAlign = Paint.Align.CENTER; text.isFakeBoldText = true; text.textSize = 18f; text.color = Color.WHITE
        c.drawText(if (reinforceTraining) "停止进化" else "神经进化", reinforceButtonRect.centerX(), reinforceButtonRect.centerY() + 7f, text)
        text.isFakeBoldText = false; text.textAlign = Paint.Align.LEFT
    }

    private fun drawGameOver(c: Canvas) {
        paint.color = Color.argb(150, 0, 0, 0)
        c.drawRect(0f, 0f, width.toFloat(), height.toFloat(), paint)
        text.textAlign = Paint.Align.CENTER; text.isFakeBoldText = true
        text.textSize = 30f; text.color = Color.WHITE
        c.drawText("GAME OVER", width / 2f, height / 2f - 45, text)
        text.textSize = 15f; text.isFakeBoldText = false
        c.drawText("分数 $score   最高 $highScore   长度 ${snake.size}", width / 2f, height / 2f - 15, text)
        text.color = Color.YELLOW
        c.drawText("点击屏幕重新开始", width / 2f, height / 2f + 20, text)
        text.color = Color.LTGRAY; text.textSize = 11f
        c.drawText(lastDeathInfo, width / 2f, height / 2f + 48, text)
    }

    private var touchStartX = 0f
    private var touchStartY = 0f

    override fun onTouchEvent(e: MotionEvent): Boolean {
        when (e.action) {
            MotionEvent.ACTION_DOWN -> { touchStartX = e.x; touchStartY = e.y; return true }
            MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> {
                if (reinforceButtonRect.contains(e.x, e.y)) {
                    val now = System.currentTimeMillis()
                    if (now - lastReinforceTap > 400L) { lastReinforceTap = now; setReinforceTraining(!reinforceTraining) }
                    return true
                }
                if (reinforceTraining) return true
                if (gameOver) { reset(); return true }
                if (aiMode != 0) return true
                if (snake.isEmpty()) return true
                val dx = e.x - touchStartX; val dy = e.y - touchStartY
                val useSwipe = abs(dx) > 24f || abs(dy) > 24f
                val d = if (useSwipe) {
                    if (abs(dx) > abs(dy)) P(if (dx > 0) 1 else -1, 0) else P(0, if (dy > 0) 1 else -1)
                } else {
                    val hx = ox + (snake.first().x + 0.5f) * cell
                    val hy = oy + (snake.first().y + 0.5f) * cell
                    val rdx = e.x - hx; val rdy = e.y - hy
                    if (abs(rdx) > abs(rdy)) P(if (rdx > 0) 1 else -1, 0) else P(0, if (rdy > 0) 1 else -1)
                }
                if (!isReverse(d, dir)) { queue.clear(); queue.add(d) }
                return true
            }
            else -> return true
        }
    }

    override fun onDetachedFromWindow() {
        stopParallelTraining(); stopWatchDog()
        super.onDetachedFromWindow()
        bgm?.stop()
        try { toneGen?.release() } catch (_: Throwable) {}
        try { aiPool.shutdownNow() } catch (_: Throwable) {}
        saveTrainingState()
    }

    private inner class TrainGame(
        seed: Long,
        private val runId: Long,
        private val statusIndex: Int = 0
    ) {
        val rng = Random(seed)
        val gSnake = ArrayDeque<P>()
        var gDir = P(1, 0)
        var gFood = P(7, 7)
        var gScore = 0
        var gHunger = 0
        var gLastFreeRegion = 0f
        var gCombo = 0
        var gSteps = 0
        var gOver = false
        var lastDeathCause = "UNKNOWN"

        val vis = BooleanArray(total)
        val que = IntArray(total + 4)
        val par = IntArray(total)
        val parDir = arrayOfNulls<P>(total)

        private var currentAgentId = -1
        var gLastAction = -1

        fun playOneGame(agentId: Int, expectedGenerationToken: Long): Boolean {
            currentAgentId = agentId
            if (agentId !in 0 until POPULATION_SIZE) { Log.e(LOG_TAG, "INVALID_AGENT_ID=$agentId"); return false }
            if (generationToken != expectedGenerationToken) {
                Log.w(LOG_TAG, "STALE_GAME_START agent=$agentId expected=$expectedGenerationToken actual=$generationToken")
                return false
            }
            gSnake.clear(); gSnake.add(P(7, 7)); gSnake.add(P(6, 7)); gSnake.add(P(5, 7))
            gDir = P(1, 0); gScore = 0; gHunger = 0; gCombo = 0; gSteps = 0; gOver = false; gLastAction = -1
            lastDeathCause = "UNKNOWN"
            gLastFreeRegion = gFreeRegion(gSnake).toFloat(); gPlaceFood()
            val maxIterations = 8000; var iter = 0
            try {
                while (!gOver && isTrainingRunActive(runId) && generationToken == expectedGenerationToken && !Thread.currentThread().isInterrupted && iter < maxIterations) { gStep(); iter++ }
            } catch (t: Throwable) {
                Log.e(LOG_TAG, "TrainGame agent=$agentId crashed", t)
                if (isTrainingRunActive(runId) && generationToken == expectedGenerationToken) {
                    lastDeathCause = "EXCEPTION"; gOver = true
                    try { gDie(lastDeathCause) } catch (inner: Throwable) { Log.e(LOG_TAG, "gDie exception failed", inner) }
                    return true
                }
                return false
            }
            if (!isTrainingRunActive(runId) || generationToken != expectedGenerationToken || Thread.currentThread().isInterrupted) return false
            if (!gOver) {
                lastDeathCause = "TIMEOUT"; gOver = true
                gScore = max(0, gScore - 500)
                try { gDie(lastDeathCause) } catch (inner: Throwable) { Log.e(LOG_TAG, "gDie timeout failed", inner) }
                return true
            }
            try { gDie(lastDeathCause) } catch (inner: Throwable) { Log.e(LOG_TAG, "gDie normal failed", inner) }
            return true
        }

        fun gPlaceFood() {
            val free = ArrayList<P>(total)
            for (x in 0 until cols) for (y in 0 until rows) { val p = P(x, y); if (!gSnake.contains(p)) free.add(p) }
            if (free.isNotEmpty()) gFood = free[rng.nextInt(free.size)]
        }

        fun gStep() {
            heartbeat()
            val state = gBuildState()
            val mv = gChooseMove(state)
            val action = dirs.indexOfFirst { it == mv }.coerceAtLeast(0)
            gLastAction = action
            if (!gIsReverse(mv, gDir)) gDir = mv
            val nh = P(gSnake.first().x + gDir.x, gSnake.first().y + gDir.y)
            if (!gInside(nh)) { gTerminal(state, action, DEATH_WALL); lastDeathCause = "WALL"; gOver = true; return }
            val ate = nh == gFood; val tail = gSnake.last()
            if (gSnake.contains(nh) && !(nh == tail && !ate)) {
                val testSnake = ArrayDeque(gSnake); testSnake.addFirst(nh); if (!ate) testSnake.removeLast()
                val reg = gFreeRegion(testSnake)
                val cause = if (reg < max(2, (gSnake.size * safetyMargin).toInt())) "TRAP" else "SELF"
                gTerminal(state, action, if (cause == "TRAP") DEATH_TRAP else DEATH_SELF)
                lastDeathCause = cause; gOver = true; return
            }
            gSnake.addFirst(nh); var reward = REWARD_STEP
            if (ate) {
                gScore += 10 + min(gCombo, 30) * 3 + gSnake.size; gCombo++; gHunger = 0; gPlaceFood()
                reward += REWARD_FOOD + gCombo * 0.06f
            } else {
                gSnake.removeLast(); gHunger++; gCombo = max(0, gCombo - 1)
                val gCurFree = gFreeRegion(gSnake).toFloat(); val gSpaceDelta = gCurFree - gLastFreeRegion
                gLastFreeRegion = gCurFree; reward += gSpaceDelta * REWARD_SPACE_DELTA
                if (gTailReachable(gSnake)) reward += REWARD_TAIL
                if (gCalculateDanger() >= 4) reward += REWARD_DANGER
                reward += -(gHunger * gHunger * 0.001f).coerceAtMost(0.15f)
            }
            gSteps++
            if (statusIndex in threadStatus.indices) {
                val st = threadStatus[statusIndex]
                st.score = gScore; st.steps = gSteps
                st.phase = if (ate) "捕食" else if (gCalculateDanger() >= 3) "避险" else "搜索"
            }
            if (gHunger >= hungerKillLimit) { gTerminal(state, action, DEATH_HUNGER); lastDeathCause = "HUNGER"; gOver = true; return }
            val nextState = gBuildState(); val nextMask = gLegalMask()
            qUpdate(state, action, reward, nextState, nextMask, false)
        }

        private fun gTerminal(state: Int, action: Int, reward: Float) { qUpdate(state, action, reward, state, 0, true) }

        private fun beamSearchBestMove(): Pair<P, Float>? {
            if (!BEAM_ENABLED) return null
            if (gSnake.isEmpty()) return null
            if (gSnake.size < BEAM_MIN_LENGTH) return null

            beamCalls++

            try {
                val depth = when {
                    gSnake.size >= 50 -> BEAM_DEPTH_MAX
                    gSnake.size >= BEAM_LONG_LENGTH -> BEAM_DEPTH_LONG
                    else -> BEAM_DEPTH_SHORT
                }.coerceAtMost(BEAM_DEPTH_MAX)

                val width = if (gSnake.size >= BEAM_LONG_LENGTH) 4 else BEAM_WIDTH

                val initialMoves = dirs
                    .map { d -> gEvaluate(d) }
                    .filter { it.legal }
                    .sortedByDescending { it.score }
                    .take(width)

                if (initialMoves.isEmpty()) return null

                var beam = ArrayList<BeamNode>()
                var nodesExpanded = 0
                val startHeads = IntArray(4) { -1 }

                for (candidate in initialMoves) {
                    val node = simulateBeamMove(gSnake, gDir, gFood, candidate.d, candidate.d, startHeads)
                    if (node != null) {
                        beam.add(node)
                        nodesExpanded++
                    }
                }

                if (beam.isEmpty()) return null

                var depthStep = 0
                while (depthStep < depth - 1 && beam.isNotEmpty()) {
                    val next = ArrayList<BeamNode>()
                    var stop = false
                    for (node in beam) {
                        if (node.dead) continue
                        if (stop) break
                        val moves = dirs
                            .filter { !gIsReverse(it, node.dir) }
                            .mapNotNull { mv ->
                                simulateBeamMove(node.body, node.dir, node.food, mv, node.firstAction, node.recentHeadCells)
                            }
                            .sortedByDescending { it.score }
                            .take(width)
                        next.addAll(moves)
                        nodesExpanded += moves.size
                        if (nodesExpanded >= BEAM_MAX_NODES) {
                            stop = true
                        }
                    }
                    if (next.isEmpty()) {
                        beam = ArrayList()
                        break
                    }
                    beam = ArrayList(next.sortedByDescending { it.score }.take(width))
                    depthStep++
                }

                if (beam.isEmpty()) return null
                val best = beam.filter { !it.dead }.maxByOrNull { it.score }
                    ?: beam.maxByOrNull { it.score }
                    ?: return null

                beamSuccess++
                beamTotalNodes += nodesExpanded
                beamBestScore = best.score

                return Pair(best.firstAction, best.score)
            } catch (t: Throwable) {
                Log.e(LOG_TAG, "Beam search failed", t)
                return null
            }
        }

        private fun simulateBeamMove(
            sourceBody: ArrayDeque<P>,
            sourceDir: P,
            targetFood: P,
            move: P,
            firstAction: P,
            prevHeads: IntArray
        ): BeamNode? {
            if (sourceBody.isEmpty()) return null
            if (gIsReverse(move, sourceDir)) return null

            val body = ArrayDeque<P>()
            for (p in sourceBody) body.addLast(p)

            val head = body.first()
            val nextHead = P(head.x + move.x, head.y + move.y)

            if (!gInside(nextHead)) {
                return BeamNode(body, move, targetFood, -100f, 1, false, true, 0f, firstAction, prevHeads)
            }

            val ate = nextHead == targetFood
            val hitBody = body.contains(nextHead)

            if (hitBody && !(nextHead == body.last() && !ate)) {
                return BeamNode(body, move, targetFood, -100f, 1, false, true, 0f, firstAction, prevHeads)
            }

            body.addFirst(nextHead)
            if (!ate) body.removeLast()

            val region = gFreeRegion(body)
            val ratio = region.toFloat() / max(1, body.size)
            val tailOk = gTailReachable(body)
            val safeMoves = gCountSafeMoves(body)
            val foodDistance = gDistance(body.first(), targetFood, body, true).let { if (it < 0) 999 else it }
            val danger = calculateBeamDanger(body, move, targetFood)

            var score = 0f
            score += BEAM_SURVIVAL_WEIGHT
            score += ratio * BEAM_SPACE_WEIGHT
            if (tailOk) score += BEAM_TAIL_WEIGHT else if (body.size > 8) score -= BEAM_TAIL_WEIGHT * 1.5f

            if (ate) {
                score += 12f * BEAM_FOOD_WEIGHT
                val afterRegion = gFreeRegion(body)
                val afterTail = gTailReachable(body)
                val afterSafe = gCountSafeMoves(body)
                if (afterRegion < body.size * 0.8f) score -= 15f
                if (!afterTail && body.size > 12) score -= 12f
                if (afterSafe <= 1) score -= 8f
            } else {
                val foodProgress = 1f / (foodDistance + 1f)
                score += foodProgress * 8f * BEAM_FOOD_WEIGHT
            }

            score += safeMoves * 0.5f
            score -= danger * BEAM_DANGER_WEIGHT
            if (ratio < 0.7f && body.size > 8) score -= 8f
            if (!tailOk && body.size > 12) score -= 7f

            val nextCell = nextHead.y * cols + nextHead.x
            var loopHits = 0
            for (h in prevHeads) if (h == nextCell) loopHits++
            if (loopHits > 0) {
                score -= BEAM_LOOP_WEIGHT * loopHits
                if (loopHits >= 2) score -= BEAM_LOOP_WEIGHT
            }

            val newHeads = IntArray(4) { -1 }
            newHeads[0] = nextCell
            for (i in 1..3) newHeads[i] = prevHeads[i - 1]

            return BeamNode(body, move, targetFood, score, 1, ate, false, loopHits.toFloat(), firstAction, newHeads)
        }

        private fun calculateBeamDanger(body: ArrayDeque<P>, heading: P, target: P): Float {
            if (body.isEmpty()) return 5f
            val head = body.first()
            var danger = 0f
            for (d in dirs) {
                if (gIsReverse(d, heading)) continue
                val np = P(head.x + d.x, head.y + d.y)
                if (!gInside(np)) { danger += 1f; continue }
                val ate = np == target
                if (body.contains(np) && !(np == body.last() && !ate)) danger += 1f
            }
            val safeMoves = gCountSafeMoves(body)
            if (safeMoves <= 1) danger += 2f
            if (safeMoves == 0) danger += 5f
            return danger.coerceIn(0f, 5f)
        }

        fun gChooseMove(state: Int): P {
            val cands = dirs.map { gEvaluate(it) }
            val legal = cands.filter { it.legal }
            if (legal.isEmpty()) return gDir
            if (legal.size == 1) return legal.first().d

            val safeFood = gFindSafeFoodStep()
            val tailStep = if (gHunger < gHungerForceEat()) gFollowTailStep(legal) else null
            val threshold = gHungerForceEat()

            val candidatePool = when {
                gHunger >= threshold -> {
                    val safeFoodCandidates = legal.filter { it.tailOk && it.foodDist >= 0 }
                    if (safeFoodCandidates.isNotEmpty()) safeFoodCandidates else legal
                }
                else -> {
                    val shielded = legal.filter {
                        val ratio = it.region.toFloat() / max(1, gSnake.size)
                        it.tailOk || ratio >= 1.0f || (gSnake.size < 15 && ratio >= 0.75f)
                    }
                    if (shielded.isNotEmpty()) shielded else legal
                }
            }

            val boosted = candidatePool.map { c ->
                var extra = 0f
                if (safeFood != null && c.d == safeFood) extra += 3.0f
                if (tailStep != null && c.d == tailStep) extra += 1.5f
                c.copy(score = c.score + extra)
            }

            return gSelectAction(state, boosted).d
        }

        private fun gSelectAction(state: Int, legal: List<Candidate>): Candidate {
            if (legal.size == 1) return legal.first()
            if (rng.nextFloat() < currentEpsilon()) {
                val safe = legal.filter { it.tailOk || it.region >= max(5, gSnake.size / 2) }
                return if (safe.isNotEmpty()) safe[rng.nextInt(safe.size)] else legal[rng.nextInt(legal.size)]
            }
            if (currentAgentId !in 0 until POPULATION_SIZE) {
                Log.e(LOG_TAG, "Invalid currentAgentId=$currentAgentId")
                return legal.first()
            }
            val brain = population[currentAgentId]
            val nnInputs = buildInputs(gSnake.first(), gFood, gSnake)
            val nnVals = brain.think(nnInputs)

            val v3TrainCtx: Long = run {
                val h0 = gSnake.first()
                val foodDxBucket = ((gFood.x - h0.x) / 3).coerceIn(-5, 5)
                val foodDyBucket = ((gFood.y - h0.y) / 3).coerceIn(-5, 5)
                val regionBucket = (gFreeRegion(gSnake) / 4).coerceIn(0, 60)
                val lenBucket = (gSnake.size / 8).coerceIn(0, 30)
                val headingBucket = when (gDir) { P(0, -1) -> 0; P(0, 1) -> 1; P(-1, 0) -> 2; else -> 3 }
                val dangerBucket = gCalculateDanger().coerceIn(1, 5)
                val tailBucket = if (gTailReachable(gSnake)) 1 else 0
                var hh = 1125899906842597L
                hh = hh * 31 + h0.x; hh = hh * 31 + h0.y
                hh = hh * 31 + foodDxBucket; hh = hh * 31 + foodDyBucket
                hh = hh * 31 + headingBucket; hh = hh * 31 + dangerBucket
                hh = hh * 31 + regionBucket; hh = hh * 31 + lenBucket; hh = hh * 31 + tailBucket
                hh xor v3TrainCtxSalt
            }
            val de = gCheckFoodDeadEnd()
            deadEndPredicted = de.first; foodSpaceRatio = de.second
            var deadEndPenalty = 0f; if (de.first) deadEndPenalty = -5f
            val rSteps = when { gSnake.size > 60 -> 5; gSnake.size > 25 -> 3; else -> 0 }
            rolloutActive = rSteps > 0; rolloutSteps = rSteps

            val beamResult = if (BEAM_ENABLED && gSnake.size >= BEAM_MIN_LENGTH) beamSearchBestMove() else null
            val beamMove = beamResult?.first
            val beamValid = beamMove != null && legal.any { it.d == beamMove }

            var best = legal.first(); var bestValue = -Float.MAX_VALUE
            for (candidate in legal) {
                val a = dirs.indexOfFirst { it == candidate.d }; if (a < 0) continue
                val q = qRead(state, a); val nn = nnVals[a]; val rule = candidate.score
                val rolloutScore = if (rSteps > 0) gRolloutN(candidate.d, rSteps) else 0f
                val v3TrainPenalty = v3Memory.penaltyFor(v3TrainCtx, a) * (if (v3FusionEnabled) 45f else 0f)
                val qNorm = (q / 10f).coerceIn(-1f, 1f)
                val nnNorm = kotlin.math.tanh(nn * 0.25f).coerceIn(-1f, 1f)
                val ruleNorm = kotlin.math.tanh(rule / 1000f).coerceIn(-1f, 1f)
                val rolloutNorm = kotlin.math.tanh(rolloutScore / 30f).coerceIn(-1f, 1f)
                val memoryNorm = kotlin.math.tanh(v3TrainPenalty / 10f).coerceIn(-1f, 1f)
                val deadNorm = deadEndPenalty.coerceIn(-1f, 0f)
                val beamNorm = if (beamValid && candidate.d == beamMove) {
                    kotlin.math.tanh(beamResult!!.second / 20f).coerceIn(-1f, 1f)
                } else 0f
                val mixed = qWeight * qNorm + nnWeight * nnNorm +
                            0.30f * ruleNorm + 0.20f * rolloutNorm +
                            0.25f * memoryNorm + 0.20f * deadNorm +
                            BEAM_WEIGHT * beamNorm
                if (mixed > bestValue) { bestValue = mixed; best = candidate.copy(qValue = q) }
            }

            if (beamValid && best.d == beamMove) beamSelected++

            if (beamCalls > 0L && beamCalls % 100L == 0L && currentAgentId == 0) {
                Log.d(LOG_TAG, "Beam: calls=$beamCalls success=$beamSuccess selected=$beamSelected nodes=$beamTotalNodes best=$beamBestScore")
            }

            return best
        }

        private fun gCheckFoodDeadEnd(): Pair<Boolean, Float> {
            if (gSnake.isEmpty()) return Pair(false, 10f)
            val gVisited = BooleanArray(total); val queue = ArrayDeque<Int>()
            val start = gFood.y * cols + gFood.x; if (start !in gVisited.indices) return Pair(true, 0f)
            gVisited[start] = true; queue.addLast(start); var space = 0
            while (queue.isNotEmpty()) {
                val curr = queue.removeFirst(); space++
                val x = curr % cols; val y = curr / cols
                for (d in dirs) {
                    val nx = x + d.x; val ny = y + d.y
                    if (nx !in 0 until cols || ny !in 0 until rows) continue
                    val index = ny * cols + nx; if (gVisited[index]) continue
                    val p = P(nx, ny); if (gSnake.contains(p)) continue
                    gVisited[index] = true; queue.addLast(index)
                }
            }
            val ratio = space.toFloat() / max(1, gSnake.size)
            return Pair(ratio < 1.2f, ratio)
        }

        private fun gRolloutN(startDir: P, maxSteps: Int): Float {
            var body = ArrayDeque(gSnake); var dir = startDir; var score = 0f
            for (step in 0 until maxSteps) {
                if (body.isEmpty()) return score - 50f
                var bestNext: P? = null; var bestSpace = -1
                for (d in dirs) {
                    val nh = P(body.first().x + d.x, body.first().y + d.y)
                    if (!gInside(nh)) continue
                    val isTail = nh == body.last(); if (body.contains(nh) && !isTail) continue
                    var space = 0
                    for (sd in dirs) {
                        val sx = nh.x + sd.x; val sy = nh.y + sd.y
                        if (sx in 0 until cols && sy in 0 until rows) if (!body.any { it.x == sx && it.y == sy }) space++
                    }
                    if (space > bestSpace) { bestSpace = space; bestNext = d }
                }
                if (bestNext == null) return score - 50f
                val sim = gSimulateOn(body, bestNext); body = sim.body
                val region = gFreeRegion(body); val tailOk = gTailReachable(body); val mobility = gCountSafeMoves(body)
                val spaceRatio = region.toFloat() / max(1, body.size)
                score += spaceRatio.coerceIn(0f, 6f) * 0.8f
                score += mobility * 0.5f
                if (tailOk) score += 1.5f else if (body.size > 10) score -= 3.0f
                if (sim.ate) score += 8f
                val fd = gDistance(body.first(), gFood, body, true)
                if (fd >= 0) score += 3.0f / (fd + 1)
                score *= 0.92f
                dir = bestNext
            }
            return score
        }

        private fun gBuildState(): Int = buildState(gSnake, gDir, gFood, gHunger)
        private fun gLegalMask(): Int = legalActionMask(gSnake, gDir, gFood)

        fun gHungerForceEat(): Int = when { gSnake.size < 20 -> 50; gSnake.size < 35 -> 70; gSnake.size < 55 -> 100; gSnake.size < 80 -> 140; else -> 200 }

        fun gFollowTailStep(legal: List<Candidate>): P? {
            if (gSnake.size < 2) return null
            val path = gShortestPath(gSnake.first(), gSnake.last(), gSnake, true) ?: return null
            if (path.isEmpty()) return null
            val step = path.first(); if (legal.none { it.d == step }) return null
            val sim = gSimulate(step); if (sim.body.isEmpty()) return null
            if (!gTailReachable(sim.body)) return null
            return step
        }

        fun gFindSafeFoodStep(): P? {
            val path = gShortestPath(gSnake.first(), gFood, gSnake, true) ?: return null
            if (path.isEmpty()) return null
            val simBody = ArrayDeque(gSnake); var ate = false
            for (step in path) {
                val nh = P(simBody.first().x + step.x, simBody.first().y + step.y)
                if (!gInside(nh)) return null
                val willEat = nh == gFood
                if (simBody.contains(nh) && !(nh == simBody.last() && !willEat)) return null
                simBody.addFirst(nh); if (!willEat) simBody.removeLast() else ate = true
            }
            if (!ate) return null; if (!gTailReachable(simBody)) return null
            val len = simBody.size; val freeLeft = total - len
            if (len > 180 && freeLeft < 4) return null
            if (len > 150 && freeLeft < 6) return null
            if (len > 120 && freeLeft < 10) return null
            if (len > 90 && freeLeft < 14) return null
            if (len > 60 && freeLeft < 20) return null
            return path.first()
        }

        fun gEvaluate(d: P): Candidate {
            if (!gLegalDirection(d)) return Candidate(d, -1e9f, "非法", false)
            val sim = gSimulate(d); if (sim.body.isEmpty()) return Candidate(d, -1e9f, "非法", false)
            val region = gFreeRegion(sim.body); val tail = gTailReachable(sim.body)
            val foodDist = gDistance(sim.body.first(), gFood, sim.body, true)
            val ate = sim.ate; val mobility = gCountSafeMoves(sim.body)
            val hungerFactor = when { gHunger >= 60 -> 4f; gHunger >= 30 -> 2.5f; gHunger >= 15 -> 1.6f; else -> 1f }
            val regionScore = region * wRegion; val mobilityScore = mobility * wMobility
            val tailScore = if (tail) wTailGood else wTailBad
            var foodScore = if (foodDist >= 0) hungerFactor * aggression * (wFoodNear / (foodDist + 1)) else -450f * hungerFactor
            if (ate) foodScore += wFoodAte * aggression
            var eatPenalty = 0f
            if (ate) {
                val afterSize = sim.body.size; val needSpace = (afterSize * safetyMargin).toInt() + 2
                if (!tail || region < needSpace) eatPenalty = -7500f - gSnake.size * 100f
                else {
                    val after = ArrayDeque(sim.body)
                    val dx = after.last().x - after.first().x; val dy = after.last().y - after.first().y
                    val follow = when { abs(dx) >= abs(dy) && dx != 0 -> P(if (dx > 0) 1 else -1, 0); dy != 0 -> P(0, if (dy > 0) 1 else -1); else -> null }
                    if (follow != null && canSim(after, follow)) {
                        val next = simulateOn(after, follow)
                        val r2 = freeRegion(next.body); val t2 = tailReachable(next.body)
                        if (!t2 || r2 < (afterSize * 1.2f).toInt()) eatPenalty = -4500f - gSnake.size * 60f
                    }
                }
            }
            val edge = min(min(sim.body.first().x, cols - 1 - sim.body.first().x), min(sim.body.first().y, rows - 1 - sim.body.first().y))
            val edgeScore = -max(0, 2 - edge) * wEdge
            val spacePenalty = max(0f, gSnake.size * safetyMargin - region.toFloat())
            val spaceScore = -spacePenalty * wSpace
            val totalScore = regionScore + mobilityScore + tailScore + foodScore + edgeScore + spaceScore + eatPenalty
            return Candidate(d, totalScore, "", true, regionScore = regionScore, mobilityScore = mobilityScore,
                tailScore = tailScore, foodScore = foodScore, edgeScore = edgeScore, spaceScore = spaceScore,
                region = region, mobility = mobility, tailOk = tail, foodDist = foodDist, ate = ate)
        }

        fun gSimulate(d: P): Sim = gSimulateOn(ArrayDeque(gSnake), d)
        fun gSimulateOn(src: ArrayDeque<P>, d: P): Sim {
            val b = ArrayDeque(src); if (b.isEmpty()) return Sim(b, false)
            val nh = P(b.first().x + d.x, b.first().y + d.y)
            if (!gInside(nh)) return Sim(b, false)
            val ate = nh == gFood
            if (b.contains(nh) && !(nh == b.last() && !ate)) return Sim(b, false)
            b.addFirst(nh); if (!ate) b.removeLast(); return Sim(b, ate)
        }

        fun gLegalDirection(d: P): Boolean {
            if (d == P(0, 0)) return false
            if (gIsReverse(d, gDir)) return false
            if (gSnake.isEmpty()) return false
            val nh = P(gSnake.first().x + d.x, gSnake.first().y + d.y)
            if (!gInside(nh)) return false
            val ate = nh == gFood
            return !gSnake.contains(nh) || (nh == gSnake.last() && !ate)
        }

        fun gIsReverse(a: P, b: P): Boolean = a.x == -b.x && a.y == -b.y
        fun gInside(p: P): Boolean = p.x in 0 until cols && p.y in 0 until rows

        fun gFreeRegion(body: ArrayDeque<P>): Int {
            if (body.isEmpty()) return 0
            java.util.Arrays.fill(vis, 0, total, false)
            for (p in body) { if (!gInside(p)) continue; vis[p.y * cols + p.x] = true }
            val start = body.first(); if (!gInside(start)) return 0
            val si = start.y * cols + start.x; vis[si] = true
            var head = 0; var tail = 0; que[tail++] = si; var count = 0
            while (head < tail) {
                val curr = que[head++]; val cx = curr % cols; val cy = curr / cols; count++
                if (cx > 0) { val ni = curr - 1; if (!vis[ni]) { vis[ni] = true; if (tail < total) que[tail++] = ni } }
                if (cx < cols - 1) { val ni = curr + 1; if (!vis[ni]) { vis[ni] = true; if (tail < total) que[tail++] = ni } }
                if (cy > 0) { val ni = curr - cols; if (!vis[ni]) { vis[ni] = true; if (tail < total) que[tail++] = ni } }
                if (cy < rows - 1) { val ni = curr + cols; if (!vis[ni]) { vis[ni] = true; if (tail < total) que[tail++] = ni } }
            }
            return count
        }

        fun gDistance(start: P, target: P, body: Collection<P>, allowTail: Boolean): Int {
            if (!gInside(start) || !gInside(target)) return -1
            if (start == target) return 0
            java.util.Arrays.fill(vis, 0, total, false)
            for (p in body) { if (!gInside(p)) continue; vis[p.y * cols + p.x] = true }
            if (allowTail && body.isNotEmpty()) { val last = body.last(); if (gInside(last)) vis[last.y * cols + last.x] = false }
            val si = start.y * cols + start.x; vis[si] = true
            var head = 0; var tail = 0; que[tail++] = si; var dist = 0
            while (head < tail) {
                val layer = tail - head
                repeat(layer) {
                    if (head >= tail) return@repeat
                    val curr = que[head++]; val cx = curr % cols; val cy = curr / cols
                    if (cx == target.x && cy == target.y) return dist
                    if (cx > 0) { val ni = curr - 1; if (!vis[ni]) { vis[ni] = true; if (tail < total) que[tail++] = ni } }
                    if (cx < cols - 1) { val ni = curr + 1; if (!vis[ni]) { vis[ni] = true; if (tail < total) que[tail++] = ni } }
                    if (cy > 0) { val ni = curr - cols; if (!vis[ni]) { vis[ni] = true; if (tail < total) que[tail++] = ni } }
                    if (cy < rows - 1) { val ni = curr + cols; if (!vis[ni]) { vis[ni] = true; if (tail < total) que[tail++] = ni } }
                }
                dist++
            }
            return -1
        }

        fun gCountSafeMoves(body: ArrayDeque<P>): Int {
            if (body.isEmpty()) return 0
            val h = body.first()
            val prevDir = if (body.size < 2) gDir else P(body.elementAt(0).x - body.elementAt(1).x, body.elementAt(0).y - body.elementAt(1).y)
            return dirs.count { d ->
                val nh = P(h.x + d.x, h.y + d.y)
                gInside(nh) && (!body.contains(nh) || (nh == body.last() && nh != gFood)) && !gIsReverse(d, prevDir)
            }
        }

        fun gTailReachable(body: ArrayDeque<P>): Boolean = if (body.isEmpty()) false else gDistance(body.first(), body.last(), body, true) >= 0

        fun gShortestPath(start: P, target: P, body: Collection<P>, allowTail: Boolean): List<P>? {
            if (start == target) return emptyList()
            if (!gInside(start) || !gInside(target)) return null
            java.util.Arrays.fill(vis, 0, total, false)
            for (p in body) { if (!gInside(p)) continue; val idx = p.y * cols + p.x; vis[idx] = true }
            if (allowTail && body.isNotEmpty()) { val last = body.last(); if (gInside(last)) { val li = last.y * cols + last.x; vis[li] = false } }
            val si = start.y * cols + start.x; val ti = target.y * cols + target.x; vis[si] = true
            java.util.Arrays.fill(par, 0, total, -1)
            for (i in 0 until total) parDir[i] = null
            var head = 0; var tail = 0; que[tail++] = si; var found = false
            while (head < tail) {
                val curr = que[head++]; if (curr == ti) { found = true; break }
                val cx = curr % cols; val cy = curr / cols
                if (cy > 0) { val ni = curr - cols; if (!vis[ni]) { vis[ni] = true; par[ni] = curr; parDir[ni] = P(0, -1); if (tail < total) que[tail++] = ni } }
                if (cy < rows - 1) { val ni = curr + cols; if (!vis[ni]) { vis[ni] = true; par[ni] = curr; parDir[ni] = P(0, 1); if (tail < total) que[tail++] = ni } }
                if (cx > 0) { val ni = curr - 1; if (!vis[ni]) { vis[ni] = true; par[ni] = curr; parDir[ni] = P(-1, 0); if (tail < total) que[tail++] = ni } }
                if (cx < cols - 1) { val ni = curr + 1; if (!vis[ni]) { vis[ni] = true; par[ni] = curr; parDir[ni] = P(1, 0); if (tail < total) que[tail++] = ni } }
            }
            if (!found) return null
            val steps = ArrayList<P>(); var cur = ti
            while (cur != si) { val d = parDir[cur] ?: return null; steps.add(d); cur = par[cur]; if (cur < 0) return null }
            steps.reverse(); return steps
        }

        fun gCalculateDanger(): Int {
            val region = gFreeRegion(gSnake); val ratio = region.toFloat() / max(1, gSnake.size)
            val mobility = gCountSafeMoves(gSnake)
            return when {
                mobility <= 0 -> 5; ratio < 1.5f -> 5; ratio < 2.2f -> 4
                ratio < 3.5f -> 3; ratio < 5f -> 2; else -> 1
            }
        }

        fun gDie(cause: String) {
            var shouldSave = false
            synchronized(sharedLock) {
                when (cause) { "WALL" -> deathWall++; "SELF" -> deathSelf++; else -> deathTrap++ }
                totalGames++; recentScores.addLast(gScore)
                while (recentScores.size > 50) recentScores.removeFirst()
                if (gScore > bestRecentScore) bestRecentScore = gScore
                val index = currentAgentId
                if (index in 0 until POPULATION_SIZE) {
                    currentScores[index] = gScore.toFloat()
                    if (gScore.toFloat() > bestScoreThisGen) bestScoreThisGen = gScore.toFloat()
                    if (gScore.toFloat() > bestScoreAllTime) bestScoreAllTime = gScore.toFloat()
                } else {
                    Log.e(LOG_TAG, "gDie invalid agent index=$index")
                }
                v2Episodes++; shouldSave = totalGames % 200 == 0
            }
            try { if (v3FusionEnabled && gSnake.isNotEmpty()) v3TrainRecordLesson(cause, gSnake.first(), gTailReachable(gSnake), gSnake.size, gLastAction) }
            catch (t: Throwable) { Log.e(LOG_TAG, "v3TrainRecordLesson failed", t) }
            adjustWeights(cause)
            safetyMargin = (safetyMargin * 0.95f + 1.08f * 0.05f).coerceIn(1.0f, 1.20f)
            aggression = (aggression * 0.95f + 1.15f * 0.05f).coerceIn(0.95f, 1.35f)
            if (shouldSave) { try { saveLearning() } catch (_: Throwable) {} }
        }
    }

    private class BgmPlayer {
        private var audioTrack: AudioTrack? = null
        @Volatile private var playing = false
        private var thread: Thread? = null

        fun start() {
            if (playing) return
            playing = true
            thread = Thread {
                try {
                    val sr = 22050; val pcm = generateMelody(sr)
                    val track = AudioTrack.Builder()
                        .setAudioAttributes(AudioAttributes.Builder().setUsage(AudioAttributes.USAGE_GAME).setContentType(AudioAttributes.CONTENT_TYPE_MUSIC).build())
                        .setAudioFormat(AudioFormat.Builder().setEncoding(AudioFormat.ENCODING_PCM_16BIT).setSampleRate(sr).setChannelMask(AudioFormat.CHANNEL_OUT_MONO).build())
                        .setBufferSizeInBytes(pcm.size * 2).setTransferMode(AudioTrack.MODE_STATIC).build()
                    track.write(pcm, 0, pcm.size)
                    if (Build.VERSION.SDK_INT >= 23) track.setLoopPoints(0, pcm.size, -1)
                    audioTrack = track
                    if (playing) track.play()
                } catch (_: Throwable) {}
            }.also { it.start() }
        }

        fun stop() {
            playing = false
            try { audioTrack?.pause() } catch (_: Throwable) {}
            try { audioTrack?.flush() } catch (_: Throwable) {}
            try { audioTrack?.release() } catch (_: Throwable) {}
            audioTrack = null; thread = null
        }

        private fun generateMelody(sampleRate: Int): ShortArray {
            val N = 0f; val E5 = 659.25f; val G5 = 783.99f; val C6 = 1046.50f
            val D5 = 587.33f; val F5 = 698.46f; val A5 = 880.00f
            val C5 = 523.25f; val E4 = 329.63f; val G4 = 392.00f
            val B4 = 493.88f; val A4 = 440.00f
            val notes = listOf(
                E5 to 180, G5 to 180, C6 to 180, G5 to 180, E5 to 180, G5 to 180, C6 to 260, N to 100,
                D5 to 180, F5 to 180, A5 to 180, F5 to 180, D5 to 180, F5 to 180, A5 to 260, N to 100,
                E5 to 180, G5 to 180, C6 to 180, G5 to 180, E5 to 180, G5 to 180, C6 to 180, E4 to 180,
                F5 to 180, A5 to 180, C6 to 180, A5 to 180, G5 to 260, D5 to 260, C5 to 420, N to 260,
                C5 to 180, E5 to 180, G5 to 180, E5 to 180, A4 to 180, C5 to 180, E5 to 180, C5 to 180,
                G4 to 180, B4 to 180, D5 to 180, G5 to 180, E5 to 220, D5 to 220, C5 to 420, N to 260,
                E5 to 180, D5 to 180, C5 to 180, D5 to 180, E5 to 260, G5 to 260, C6 to 400, N to 200
            )
            val out = ArrayList<Short>()
            for ((freq, durMs) in notes) {
                val n = durMs * sampleRate / 1000
                if (freq == N || freq <= 0f) repeat(n) { out.add(0) }
                else {
                    val period = (sampleRate / freq).toInt().coerceAtLeast(1)
                    for (i in 0 until n) {
                        val phase = (i % period) / period.toFloat()
                        val t = i.toFloat() / n
                        val env = when { t < 0.05f -> t / 0.05f; t > 0.70f -> (1f - t) / 0.30f; else -> 1f }.coerceIn(0f, 1f)
                        val v = (if (phase < 0.5f) 1f else -1f) * env * 0.06f
                        out.add((v * Short.MAX_VALUE).toInt().coerceIn(Short.MIN_VALUE.toInt(), Short.MAX_VALUE.toInt()).toShort())
                    }
                }
            }
            return out.toShortArray()
        }
    }
}
