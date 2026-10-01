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
import kotlin.math.tanh
import kotlin.random.Random
import java.util.LinkedHashMap

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
        val d: P,
        val score: Float,
        val reason: String,
        val legal: Boolean,
        val regionScore: Float = 0f,
        val mobilityScore: Float = 0f,
        val tailScore: Float = 0f,
        val foodScore: Float = 0f,
        val edgeScore: Float = 0f,
        val spaceScore: Float = 0f,
        val region: Int = 0,
        val mobility: Int = 0,
        val tailOk: Boolean = false,
        val foodDist: Int = -1,
        val ate: Boolean = false,
        val qValue: Float = 0f
    )

    private data class Snapshot(
        var strategy: String = "V2 AUTO",
        var reason: String = "初始化",
        var danger: Int = 1,
        var region: Int = 1,
        var spaceRatio: Float = 1f,
        var tailReachable: Boolean = false,
        var foodReachable: Boolean = false,
        var foodDistance: Int = -1,
        var hunger: Int = 0,
        var chosen: P = P(0, 0),
        var candidates: List<Candidate> = emptyList(),
        var depth: Int = 0,
        var nodes: Int = 0,
        var hungerFactor: Float = 1f,
        var regionWeight: Float = 11f,
        var strategyId: Int = -1,
        var qValue: Float = 0f,
        var nVisits: Int = 0,
        var forceEatActive: Boolean = false,
        var forceEatSafe: Boolean = false,
        var safeFollowMode: Boolean = false
    )

    private data class Sim(
        val body: ArrayDeque<P>,
        val ate: Boolean
    )

    private data class Particle(
        var x: Float,
        var y: Float,
        var vx: Float,
        var vy: Float,
        var life: Float,
        val color: Int
    )

    private data class FloatText(
        var x: Float,
        var y: Float,
        var life: Float,
        val text: String
    )

    private val snake = ArrayDeque<P>()
    private val queue = ArrayDeque<P>()

    private val dirs = listOf(
        P(0, -1),
        P(0, 1),
        P(-1, 0),
        P(1, 0)
    )

    private var dir = P(1, 0)
    private var food = P(5, 5)

    private var score = 0
    private var highScore = 0
    private var money = 0

    private var gameOver = false
    private var running = false

    private var aiMode = 1

    // ===== AI V3 =====
    private val v3Engine = AIEngineV3()
    private var v3PrevState: V3State? = null
    private var v3PrevScore: Int = 0
    private var v3Enabled = true

    // V3 50 Agent 训练
    private val v3PopulationLock = Any()
    private val v3TrainingShared = V3SharedLearning()
    private var v3Population: List<AIEngineV3> = emptyList()
    private var v3AgentResults: Array<V3AgentResult?> = arrayOfNulls(0)
    private val v3EvolveLock = Any()
    @Volatile private var v3Evolving = false
    private val completedAgentIds = HashSet<Int>()
    @Volatile var v3FallbackCount = 0
    @Volatile var v3ExceptionCount = 0

    private fun toV3State(): V3State {
        val bodyArr = IntArray(snake.size)
        for (i in snake.indices) {
            val p = snake.elementAt(i)
            bodyArr[i] = p.y * cols + p.x
        }
        val dirV3 = when {
            dir.x == 1 -> V3Action.RIGHT
            dir.x == -1 -> V3Action.LEFT
            dir.y == -1 -> V3Action.UP
            else -> V3Action.DOWN
        }
        val currentHash = bodyArr.contentHashCode().toLong() * 31 + food.y * cols + food.x + dirV3.ordinal
        val prevHashes = v3PrevState?.recentHashes ?: LongArray(0)
        return V3State(
            width = cols,
            height = rows,
            body = bodyArr,
            food = food.y * cols + food.x,
            direction = dirV3,
            score = score,
            steps = 0,
            stepsSinceFood = hunger,
            hunger = hunger.toFloat(),
            gameOver = gameOver,
            recentHashes = (prevHashes + currentHash).takeLast(16).toLongArray()
        )
    }

    private fun v3ActionToDir(a: V3Action): P = when(a) {
        V3Action.UP -> P(0, -1)
        V3Action.RIGHT -> P(1, 0)
        V3Action.DOWN -> P(0, 1)
        V3Action.LEFT -> P(-1, 0)
    }
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

    // ===== 神经进化新增变量 =====
    private val POPULATION_SIZE = 50
    init {
        v3Population = List(POPULATION_SIZE) { AIEngineV3(v3TrainingShared) }
        v3AgentResults = arrayOfNulls(POPULATION_SIZE)
    }
    @Volatile
    private var generation = 0
    @Volatile
    private var currentAgentIndex = 0
    private var completedAgents = 0
    private val currentScores = FloatArray(POPULATION_SIZE)
    @Volatile private var deadEndPredicted = false
    @Volatile private var rolloutActive = false
    @Volatile private var rolloutSteps = 0
    @Volatile private var foodSpaceRatio = 1f
    @Volatile private var evolving = false
    private val visitedStates = java.util.Collections.newSetFromMap(java.util.concurrent.ConcurrentHashMap<Int, Boolean>())
    // =============================

    /*
     * =========================
     * V2 RULE WEIGHTS
     * =========================
     */
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

    /*
     * ============================================================
     * V2 REAL RL CORE
     * ============================================================
     */

    private companion object {
        const val V2_FOOD_DIR = 4
        const val V2_DANGER = 16
        const val V2_MOBILITY = 5
        const val V2_SPACE = 4
        const val V2_HUNGER = 5
        const val V2_LENGTH = 4
        const val V2_TAIL = 2
        const val V2_HEADING = 1

        const val V2_STATE_COUNT =
            V2_FOOD_DIR *
            V2_DANGER *
            V2_MOBILITY *
            V2_SPACE *
            V2_HUNGER *
            V2_LENGTH *
            V2_TAIL *
            V2_HEADING

        const val V2_ACTIONS = 4
        const val V2_Q_SIZE = V2_STATE_COUNT * V2_ACTIONS

        const val V2_LOCKS = 64

        const val GAMMA = 0.94f
        const val ALPHA_FAST = 0.18f
        const val ALPHA_NORMAL = 0.055f

        const val EPS_START = 0.22f
        const val EPS_MIN = 0.015f

        const val REWARD_STEP = -0.02f
        const val REWARD_FOOD = 10.0f
        const val REWARD_SPACE = 0.035f
        const val REWARD_TAIL = 0.55f
        const val REWARD_DANGER = -0.30f
        const val REWARD_HUNGER = -0.025f
        const val REWARD_SPACE_DELTA = 0.08f

        const val DEATH_WALL = -14.0f
        const val DEATH_SELF = -18.0f
        const val DEATH_TRAP = -20.0f
        const val DEATH_HUNGER = -12.0f
    }

    @Volatile private var trainingRunId = 0L
    private val trainingLifecycleLock = Any()
    private fun isTrainingRunActive(runId: Long): Boolean =
        trainActive && trainingRunId == runId


    private fun performV3Evolution(runId: Long) {
        synchronized(v3EvolveLock) {
            if (!isTrainingRunActive(runId)) return
            if (v3Evolving) return
            v3Evolving = true
            try {
                val results = synchronized(v3PopulationLock) {
                    v3AgentResults.map { it }.filterNotNull()
                }
                if (results.size != POPULATION_SIZE) return

                val oldGen = generation
                val next = V3EvolutionManager.evolve(results, oldGen, 5)
                if (next.size != POPULATION_SIZE) return
                if (!isTrainingRunActive(runId)) return

                synchronized(v3PopulationLock) {
                    v3Population = next
                    for (agent in next) {
                        agent.setTraining(true)
                        agent.setGeneration(oldGen + 1)
                        agent.resetEpisode()
                    }
                    java.util.Arrays.fill(v3AgentResults, null)
                completedAgentIds.clear()
                }
                synchronized(sharedLock) {
                    generation = oldGen + 1
                    completedAgents = 0
                    currentAgentIndex = 0
                    for (i in 0 until POPULATION_SIZE) currentScores[i] = 0f
                }
                try { saveTrainingState() } catch (_: Throwable) {}
            } catch (e: Throwable) {
                e.printStackTrace()
            } finally {
                v3Evolving = false
            }
        }
    }

    private fun evolveNextGeneration() {
        // V2 已废弃
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

    /*
     * =========================
     * CALLBACKS
     * =========================
     */

    var onScoreChanged: ((Int) -> Unit)? = null
    var onMoneyChanged: ((Int) -> Unit)? = null

    private val prefs =
        context.getSharedPreferences("snake_prefs", Context.MODE_PRIVATE)

    /*
     * =========================
     * EFFECTS / AUDIO
     * =========================
     */

    private val vibrator: Vibrator? =
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
            (context.getSystemService(Context.VIBRATOR_MANAGER_SERVICE)
                    as? VibratorManager)?.defaultVibrator
        } else {
            @Suppress("DEPRECATION")
            context.getSystemService(Context.VIBRATOR_SERVICE) as? Vibrator
        }

    private val toneGen: ToneGenerator? = try {
        ToneGenerator(AudioManager.STREAM_MUSIC, 85)
    } catch (_: Throwable) {
        null
    }

    private var bgm: BgmPlayer? = null

    private var bodyColor = Color.rgb(46, 204, 113)
    private var headColor = Color.rgb(39, 174, 96)
    private var bgColor = Color.BLACK
    private var gridColor = Color.CYAN
    private var rainbowSkin = false

    private val hsv =
        IntArray(360) {
            Color.HSVToColor(
                floatArrayOf(it.toFloat(), 1f, 1f)
            )
        }

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

    private val autoBeamHunger = 120
    private val hungerKillLimit = 500
    private val safeFollowLength = 32

    private var beamNodes = 0
    private var restartCountdown = 0L

    private var trainingMode = false
    private var reinforceTraining = false

    // === 卡死自动检测 ===
    @Volatile private var lastHeartbeat = 0L
    @Volatile private var watchDogThread: Thread? = null
    @Volatile private var watchdogRestartCount = 0

    private fun heartbeat() {
        lastHeartbeat = System.currentTimeMillis()
    }

    private fun startWatchDog() {
        stopWatchDog()
        lastHeartbeat = System.currentTimeMillis()
        watchDogThread = Thread {
            while (true) {
                try { Thread.sleep(1000) } catch (_: Exception) {}
                if (!reinforceTraining) continue
                val now = System.currentTimeMillis()
                if (now - lastHeartbeat > 4000) {
                    watchdogRestartCount++
                    try {
                        restartTrainingSafely()
                    } catch (_: Exception) {}
                    try { Thread.sleep(3000) } catch (_: Exception) {}
                }
            }
        }.also { it.priority = Thread.MIN_PRIORITY; it.start() }
    }

    private fun stopWatchDog() {
        watchDogThread?.interrupt()
        watchDogThread = null
    }

    // 保存/恢复状态：切出去再切回来保持强化学习
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
            reinforceTraining = state.getBoolean("reinforceTraining", false)
            trainingMode = state.getBoolean("trainingMode", false)
            super.onRestoreInstanceState(state.getParcelable("super"))
        } else {
            super.onRestoreInstanceState(state)
        }
    }

    private var renderSkipCounter = 0

    private val reinforceButtonRect = RectF()
    private var lastReinforceTap = 0L

    @Volatile
    private var trainActive = false

    private val trainThreads: MutableList<Thread> =
        mutableListOf()

    private val TRAIN_THREADS = 6

    private val aiPool: ExecutorService = run {
        val cores =
            Runtime.getRuntime()
                .availableProcessors()
                .coerceIn(4, 8)

        Executors.newFixedThreadPool(cores) { r ->
            Thread(r, "snake-ai").apply {
                isDaemon = true
                priority = Thread.NORM_PRIORITY
            }
        }
    }

    private val tlVisited: ThreadLocal<BooleanArray> =
        ThreadLocal.withInitial {
            BooleanArray(cols * rows)
        }

    private val tlQueue: ThreadLocal<IntArray> =
        ThreadLocal.withInitial {
            IntArray(cols * rows)
        }

    private var aiStepStartNs = 0L
    private var aiStepBudgetNs = 15_000_000L

    private fun timeLeft(): Boolean =
        System.nanoTime() - aiStepStartNs < aiStepBudgetNs

    private fun budgetFor(speedMs: Long): Long =
        when {
            speedMs >= 150L -> 35_000_000L
            speedMs >= 80L -> 18_000_000L
            speedMs >= 55L -> 12_000_000L
            else -> 8_000_000L
        }

    private fun hungerForceEat(): Int =
        when {
            snake.size < 20 -> 50
            snake.size < 35 -> 70
            snake.size < 55 -> 100
            snake.size < 80 -> 140
            else -> 200
        }

    private fun vibrateEat() {
        vibrator?.let {
            try {
                if (Build.VERSION.SDK_INT >= 26) {
                    it.vibrate(
                        VibrationEffect.createWaveform(
                            longArrayOf(0, 12, 25, 12),
                            -1
                        )
                    )
                } else {
                    @Suppress("DEPRECATION")
                    it.vibrate(longArrayOf(0, 12, 25, 12), -1)
                }
            } catch (_: Throwable) {
            }
        }
    }

    private fun vibrateDeath() {
        vibrator?.let {
            try {
                if (Build.VERSION.SDK_INT >= 26) {
                    it.vibrate(
                        VibrationEffect.createOneShot(
                            120,
                            VibrationEffect.DEFAULT_AMPLITUDE
                        )
                    )
                } else {
                    @Suppress("DEPRECATION")
                    it.vibrate(120)
                }
            } catch (_: Throwable) {
            }
        }
    }

    private fun playEatSound() {
        try {
            toneGen?.startTone(
                ToneGenerator.TONE_PROP_BEEP,
                55
            )
        } catch (_: Throwable) {
        }
    }

    /*
     * =========================
     * FRAME LOOP
     * =========================
     */

    private val frame = object : Choreographer.FrameCallback {

        override fun doFrame(ns: Long) {
            if (!running) return

            if (lastFrame == 0L) {
                lastFrame = ns
            }

            val dt =
                ((ns - lastFrame) / 1_000_000L)
                    .coerceAtMost(100L)

            lastFrame = ns

            if (reinforceTraining) {
                if ((++renderSkipCounter % 2) == 0) {
                    invalidate()
                }

                Choreographer
                    .getInstance()
                    .postFrameCallback(this)

                return
            }

            if (gameOver) {
                restartCountdown = 0L
            } else {
                accumulator += dt

                var stepCount = 0
                val maxSteps =
                    if (trainingMode) 10 else Int.MAX_VALUE

                while (
                    accumulator >= gameSpeed &&
                    stepCount < maxSteps
                ) {
                    updateGame()

                    if (gameOver && !trainingMode) {
                        break
                    }

                    accumulator -= gameSpeed
                    stepCount++
                }

                if (stepCount >= maxSteps) {
                    accumulator = 0L
                }
            }

            updateEffects(dt / 16f)

            val shouldRender =
                if (trainingMode) {
                    (++renderSkipCounter % 2) == 0
                } else {
                    true
                }

            if (shouldRender) {
                invalidate()
            }

            Choreographer
                .getInstance()
                .postFrameCallback(this)
        }
    }

    /*
     * =========================
     * INIT
     * =========================
     */

    init {
        highScore = prefs.getInt("high_score", 0)
        money = prefs.getInt("money", 0)

        trainingMode =
            prefs.getBoolean("training_mode", false)

        aggression =
            prefs.getFloat(
                "learn_aggression",
                1.15f
            )

        safetyMargin =
            prefs.getFloat(
                "learn_safety",
                1.08f
            )

        shortcutBonus =
            prefs.getFloat(
                "learn_shortcut",
                0.90f
            )

        wRegion =
            prefs.getFloat(
                "w_region",
                wRegion0
            )

        wMobility =
            prefs.getFloat(
                "w_mobility",
                wMobility0
            )

        wTailGood =
            prefs.getFloat(
                "w_tail_good",
                wTailGood0
            )

        wTailBad =
            prefs.getFloat(
                "w_tail_bad",
                wTailBad0
            )

        wFoodNear =
            prefs.getFloat(
                "w_food_near",
                wFoodNear0
            )

        wFoodAte =
            prefs.getFloat(
                "w_food_ate",
                wFoodAte0
            )

        wEdge =
            prefs.getFloat(
                "w_edge",
                wEdge0
            )

        wSpace =
            prefs.getFloat(
                "w_space",
                wSpace0
            )

        fun fixW(v: Float, base: Float): Float =
            v.coerceIn(
                base * 0.85f,
                base * 1.15f
            )

        wRegion = fixW(wRegion, wRegion0)
        wMobility = fixW(wMobility, wMobility0)
        wTailGood = fixW(wTailGood, wTailGood0)
        wFoodNear = fixW(wFoodNear, wFoodNear0)
        wFoodAte = fixW(wFoodAte, wFoodAte0)
        wEdge = fixW(wEdge, wEdge0)
        wSpace = fixW(wSpace, wSpace0)

        wTailBad =
            wTailBad.coerceIn(
                wTailBad0 * 1.15f,
                wTailBad0 * 0.85f
            )

        aggression =
            aggression.coerceIn(0.95f, 1.35f)

        safetyMargin =
            safetyMargin.coerceIn(1.0f, 1.20f)

        lastLearnAction =
            prefs.getString(
                "last_learn_action",
                "初始化"
            ) ?: "初始化"

        deathWall =
            prefs.getInt("stat_wall", 0)

        deathSelf =
            prefs.getInt("stat_self", 0)

        deathTrap =
            prefs.getInt("stat_trap", 0)

        totalGames =
            prefs.getInt("stat_total", 0)

        bgm = BgmPlayer()

        updateCurrentSkin()
        updateCurrentBoard()

        loadTrainingState()
        reset()
    }

    fun getAIMode(): Int = aiMode

    fun setAIMode(m: Int) {
        aiMode = m
        invalidate()
    }

    fun setTrainingMode(b: Boolean) {
        trainingMode = b

        if (b) {
            aiMode = 1
            bgm?.stop()
            reset()
        } else {
            stopParallelTraining()

            if (running) {
                bgm?.start()
            }

            reset()
        }

        invalidate()
    }

    fun setReinforceTraining(enable: Boolean) {
        if (enable) {
            startParallelTraining()
            startWatchDog()
        } else {
            stopParallelTraining()
            stopWatchDog()
        }

        invalidate()
    }

    fun isReinforceTraining(): Boolean =
        reinforceTraining

    fun isTrainingMode(): Boolean =
        trainingMode

    /*
     * =========================
     * PARALLEL TRAINING (神经进化 + Q表融合)
     * =========================
     */

    private fun startReinforceTrainingInternal() {
        try {
            reinforceTraining = true
            startParallelTraining()
            heartbeat()
        } catch (_: Exception) {}
    }

    private fun restartTrainingSafely() {
        synchronized(sharedLock) {
            trainActive = false
            reinforceTraining = false
        }
        val oldThreads = synchronized(trainThreads) { trainThreads.toList() }
        for (t in oldThreads) { try { t.interrupt() } catch (_: Throwable) {} }
        for (t in oldThreads) {
            try { t.join(500) } catch (_: InterruptedException) { break }
        }
        synchronized(trainThreads) { trainThreads.clear() }
        Thread.sleep(200)
        synchronized(sharedLock) { reinforceTraining = true }
        startParallelTraining()
    }

    private fun startParallelTraining() {
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

            currentAgentIndex = 0
            completedAgents = 0
            synchronized(v3PopulationLock) {
                completedAgentIds.clear()
                java.util.Arrays.fill(v3AgentResults, null)
            }
            0f = 0f
            for (i in 0 until POPULATION_SIZE) {
                currentScores[i] = 0f
            }

                    for (i in 0 until TRAIN_THREADS) {
                val t = Thread(
                    {
                        while (isTrainingRunActive(myRunId) && !Thread.currentThread().isInterrupted) {
                            if (v3Evolving) {
                                Thread.yield()
                                continue
                            }
                            var agentId = -1
                            synchronized(sharedLock) {
                                if (currentAgentIndex < POPULATION_SIZE) {
                                    agentId = currentAgentIndex++
                                }
                            }
                            if (agentId < 0) {
                                Thread.yield()
                                continue
                            }
                            val agent = synchronized(v3PopulationLock) { v3Population[agentId] }
                            val game = TrainGame(
                                seed = System.nanoTime() + agentId * 999983L,
                                runId = myRunId,
                                v3 = agent
                            )

                            if (agentId == -1) {
                                Thread.yield()
                                continue
                            }

                            var result: V3AgentResult? = null
                            try {
                                result = game.playOneGame(agentId)
                            } catch (e: InterruptedException) {
                                Thread.currentThread().interrupt()
                                break
                            } catch (e: Throwable) {
                                e.printStackTrace()
                                result = V3AgentResult(agent = agent, fitness = -1000f, score = 0, food = 0, survivalSteps = 0, deathReason = V3DeathReason.UNKNOWN)
                            }
                            if (isTrainingRunActive(myRunId)) {
                                val finalResult = result ?: V3AgentResult(agent = agent, fitness = -1000f, score = 0, food = 0, survivalSteps = 0, deathReason = V3DeathReason.UNKNOWN)
                                var accepted = false
                                synchronized(v3PopulationLock) {
                                    if (agentId !in completedAgentIds) {
                                        completedAgentIds.add(agentId)
                                        v3AgentResults[agentId] = finalResult
                                        accepted = true
                                    }
                                }
                                if (accepted) {
                                    var shouldEvolve = false
                                    synchronized(sharedLock) {
                                        completedAgents++
                                        if (completedAgents >= POPULATION_SIZE) shouldEvolve = true
                                    }
                                    if (shouldEvolve) performV3Evolution(myRunId)
                                }
                            }
                        }
                    },
                    "snake-train-$i"
                )

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
            if (!trainActive && trainThreads.none { it.isAlive }) {
                reinforceTraining = false
                trainingMode = false
                return
            }
            trainingRunId++
            trainActive = false
            reinforceTraining = false
            trainingMode = false
            threadsToJoin = trainThreads.toList()
        }

        for (t in threadsToJoin) { try { t.interrupt() } catch (_: Throwable) {} }
        for (t in threadsToJoin) { try { t.join(5000L) } catch (_: Throwable) {} }

        synchronized(trainingLifecycleLock) {
            trainThreads.removeAll { !it.isAlive }
        }

        saveLearning()
        saveTrainingState()
        if (running) bgm?.start()
        reset()
    }

    fun setForcedStrategy(s: Int) {
        forcedStrategy = s
        invalidate()
    }

    /*
     * =========================
     * SKIN / BOARD
     * =========================
     */

    fun updateCurrentSkin(id: String? = null) {
        when (
            prefs.getString(
                "equipped_skin",
                "green"
            )
        ) {
            "blue" ->
                setSnakeColors(
                    Color.rgb(52, 152, 219),
                    Color.rgb(41, 128, 185),
                    false
                )

            "red" ->
                setSnakeColors(
                    Color.rgb(46, 204, 113),
                    Color.rgb(192, 57, 43),
                    false
                )

            "purple" ->
                setSnakeColors(
                    Color.rgb(155, 89, 182),
                    Color.rgb(142, 68, 173),
                    false
                )

            "gold" ->
                setSnakeColors(
                    Color.rgb(241, 196, 15),
                    Color.rgb(243, 156, 18),
                    false
                )

            "rainbow" ->
                setSnakeColors(
                    Color.WHITE,
                    Color.WHITE,
                    true
                )

            else ->
                setSnakeColors(
                    Color.rgb(46, 204, 113),
                    Color.rgb(39, 174, 96),
                    false
                )
        }

        invalidate()
    }

    private fun setSnakeColors(
        body: Int,
        head: Int,
        rainbow: Boolean
    ) {
        bodyColor = body
        headColor = head
        rainbowSkin = rainbow

        snakePaint.color = body
        snakePaint.style = Paint.Style.STROKE
        snakePaint.strokeCap = Paint.Cap.ROUND
        snakePaint.strokeJoin = Paint.Join.ROUND
        snakePaint.strokeWidth = 0f

        headPaint.color = head
    }

    fun updateCurrentBoard(id: String? = null) {
        when (
            prefs.getString(
                "equipped_board",
                "dark"
            )
        ) {
            "light" -> {
                bgColor = Color.rgb(
                    240,
                    240,
                    240
                )

                gridColor = Color.rgb(
                    200,
                    200,
                    200
                )
            }

            "neon" -> {
                bgColor = Color.rgb(
                    10,
                    25,
                    47
                )

                gridColor = Color.CYAN
            }

            "forest" -> {
                bgColor = Color.rgb(
                    27,
                    46,
                    26
                )

                gridColor = Color.rgb(
                    46,
                    74,
                    45
                )
            }

            "cyberpunk" -> {
                bgColor = Color.rgb(
                    43,
                    15,
                    59
                )

                gridColor = Color.MAGENTA
            }

            "rainbow_board" -> {
                bgColor = Color.BLACK
                gridColor = Color.WHITE
            }

            else -> {
                bgColor = Color.BLACK
                gridColor = Color.CYAN
            }
        }

        invalidate()
    }

    /*
     * =========================
     * RESET / LIFECYCLE
     * =========================
     */

    fun reset() {
        snake.clear()
        queue.clear()

        if (aiMode == 2) {
            snake.add(P(0, 0))
            dir = P(0, 1)
        } else {
            snake.add(
                P(
                    cols / 2,
                    rows / 2
                )
            )

            dir = P(1, 0)
        }

        score = 0
        combo = 0
        hunger = 0

        gameOver = false
        deathCause = "无"
        lastDeathInfo = ""

        gameSpeed =
            if (
                trainingMode &&
                !reinforceTraining
            ) {
                2L
            } else {
                gameSpeedStart
            }

        accumulator = 0L
        lastFrame = 0L

        particles.clear()
        floats.clear()

        flash = 0f
        restartCountdown = 0L

        lastV2State = -1
        lastV2Action = -1

        ai =
            Snapshot(
                chosen = dir
            )

        placeFood()
        lastFreeRegion = freeRegion(snake).toFloat()
        v3PrevState = null
        v3PrevScore = 0

        onScoreChanged?.invoke(score)

        invalidate()
    }

    fun resume() {
        if (running) return

        running = true
        lastFrame = 0L

        if (!trainingMode) {
            bgm?.start()
        }

        Choreographer
            .getInstance()
            .postFrameCallback(frame)
    }

    fun pause() {
        running = false

        bgm?.stop()

        Choreographer
            .getInstance()
            .removeFrameCallback(frame)
    }

    /*
     * =========================
     * MAIN GAME UPDATE
     * =========================
     */

    private fun updateGame() {
        if (gameOver) return

        if (hunger >= hungerKillLimit) {
            die("HUNGER")
            return
        }

        if (aiMode != 0) {
            queue.clear()
            queue.add(chooseMove())
        }

        if (queue.isNotEmpty()) {
            val requested =
                queue.removeFirst()

            if (
                !isReverse(requested, dir) &&
                legalDirection(requested)
            ) {
                dir = requested
            }
        }

        if (dir == P(0, 0)) return

        val oldState =
            buildState(
                snake,
                dir,
                food,
                hunger
            )

        val oldAction =
            dirs.indexOfFirst {
                it == dir
            }.coerceAtLeast(0)

        val nh =
            P(
                snake.first().x + dir.x,
                snake.first().y + dir.y
            )

        if (!inside(nh)) {
            qTerminalFromMove(
                oldState,
                oldAction,
                DEATH_WALL
            )

            die("WALL")
            return
        }

        val ate = nh == food

        val body = snake.toList()
        val hitIndex =
            body.indexOf(nh)

        val tail = snake.last()

        if (
            hitIndex >= 0 &&
            !(nh == tail && !ate)
        ) {
            val sim =
                simulateOn(
                    ArrayDeque(snake),
                    dir
                )

            val region =
                freeRegion(sim.body)

            val cause =
                if (
                    region <
                    max(
                        2,
                        (
                            snake.size *
                                safetyMargin
                        ).toInt()
                    )
                ) {
                    "TRAP"
                } else {
                    "SELF"
                }

            val reward =
                if (cause == "TRAP") {
                    DEATH_TRAP
                } else {
                    DEATH_SELF
                }

            qTerminalFromMove(
                oldState,
                oldAction,
                reward
            )

            die(cause)
            return
        }

        snake.addFirst(nh)

        var reward = REWARD_STEP

        if (ate) {
            val comboBonus =
                min(combo, 30) * 3

            val lenBonus =
                snake.size

            val gain =
                10 +
                    comboBonus +
                    lenBonus

            score += gain
            combo++

            hunger = 0

            money +=
                gain * 3 +
                    30

            if (score > highScore) {
                highScore = score
            }

            onScoreChanged?.invoke(score)
            onMoneyChanged?.invoke(money)

            prefs.edit()
                .putInt("money", money)
                .putInt("high_score", highScore)
                .apply()

            gameSpeed =
                max(
                    gameSpeedMin,
                    gameSpeedStart -
                        snake.size * 2L
                )

            vibrateEat()
            playEatSound()

            spawnFoodEffect(nh)

            placeFood()

            reward +=
                REWARD_FOOD +
                    combo * 0.06f
        } else {
            snake.removeLast()

            hunger++

            combo =
                max(
                    0,
                    combo - 1
                )

            // 空间奖励改成变化量：变大才奖，变小才罚
            val curFree = freeRegion(snake).toFloat()
            val spaceDelta = curFree - lastFreeRegion
            lastFreeRegion = curFree
            reward += spaceDelta * REWARD_SPACE_DELTA

            if (tailReachable(snake)) {
                reward += REWARD_TAIL
            }

            if (calculateDanger() >= 4) {
                reward += REWARD_DANGER
            }

            // 饥饿惩罚递增：越饿罚越重
            val hungerPenalty = -(hunger * hunger * 0.001f).coerceAtMost(0.15f)
            reward += hungerPenalty
        }

        val nextState =
            buildState(
                snake,
                dir,
                food,
                hunger
            )

        val nextMask =
            legalActionMask(
                snake,
                dir,
                food
            )

        
                    }

    /*
     * =========================
     * V2 STATE
     * =========================
     */

    private fun directionIndex(d: P): Int =
        when {
            d == P(0, -1) -> 0
            d == P(0, 1) -> 1
            d == P(-1, 0) -> 2
            else -> 3
        }

    private fun foodDirection(
        head: P,
        target: P
    ): Int {
        val dx = target.x - head.x
        val dy = target.y - head.y

        return if (abs(dx) >= abs(dy)) {
            if (dx >= 0) 3 else 2
        } else {
            if (dy >= 0) 1 else 0
        }
    }

    private fun dangerMask(
        body: ArrayDeque<P>,
        heading: P,
        target: P
    ): Int {
        if (body.isEmpty()) return 15

        val h = body.first()

        var mask = 0

        for (i in dirs.indices) {
            val d = dirs[i]

            if (isReverse(d, heading)) {
                mask = mask or (1 shl i)
                continue
            }

            val np =
                P(
                    h.x + d.x,
                    h.y + d.y
                )

            if (!inside(np)) {
                mask = mask or (1 shl i)
                continue
            }

            val ate =
                np == target

            if (
                body.contains(np) &&
                !(np == body.last() && !ate)
            ) {
                mask = mask or (1 shl i)
                continue
            }

            val sim =
                simulateForBody(
                    body,
                    d,
                    target
                )

            if (sim.body.isEmpty()) {
                mask = mask or (1 shl i)
                continue
            }

            val region =
                freeRegion(sim.body)

            val tail =
                tailReachable(sim.body)

            val ratio =
                region.toFloat() /
                    max(
                        1,
                        sim.body.size
                    )

            if (
                !tail &&
                sim.body.size > 8
            ) {
                mask = mask or (1 shl i)
            } else if (
                ratio < 0.55f &&
                sim.body.size > 12
            ) {
                mask = mask or (1 shl i)
            }
        }

        return mask and 15
    }

    private fun buildState(
        body: ArrayDeque<P>,
        heading: P,
        target: P,
        hungerValue: Int
    ): Int {
        if (body.isEmpty()) return 0

        val h = body.first()

        val foodD =
            foodDirection(
                h,
                target
            )

        val danger =
            dangerMask(
                body,
                heading,
                target
            )

        val mobility =
            countSafeMovesFor(
                body,
                heading,
                target
            ).coerceIn(0, 4)

        val region =
            freeRegion(body)

        val ratio =
            region.toFloat() /
                max(
                    1,
                    body.size
                )

        val spaceBucket =
            when {
                ratio < 0.8f -> 0
                ratio < 1.3f -> 1
                ratio < 2.0f -> 2
                else -> 3
            }

        val hungerBucket =
            when {
                hungerValue < 10 -> 0
                hungerValue < 25 -> 1
                hungerValue < 50 -> 2
                hungerValue < 100 -> 3
                else -> 4
            }

        val lengthBucket =
            when {
                body.size < 12 -> 0
                body.size < 30 -> 1
                body.size < 60 -> 2
                else -> 3
            }

        val tail =
            if (tailReachable(body)) 1 else 0

        val headingIndex =
            directionIndex(heading)

        var s = foodD

        s = s * V2_DANGER + danger
        s = s * V2_MOBILITY + mobility
        s = s * V2_SPACE + spaceBucket
        s = s * V2_HUNGER + hungerBucket
        s = s * V2_LENGTH + lengthBucket
        s = s * V2_TAIL + tail
        s = s * V2_HEADING + headingIndex

        return s.coerceIn(
            0,
            V2_STATE_COUNT - 1
        )
    }

    private fun legalActionMask(
        body: ArrayDeque<P>,
        heading: P,
        target: P
    ): Int {
        if (body.isEmpty()) return 0

        val h = body.first()
        var mask = 0

        for (i in dirs.indices) {
            val d = dirs[i]

            if (isReverse(d, heading)) {
                continue
            }

            val np =
                P(
                    h.x + d.x,
                    h.y + d.y
                )

            if (!inside(np)) {
                continue
            }

            val ate =
                np == target

            if (
                body.contains(np) &&
                !(np == body.last() && !ate)
            ) {
                continue
            }

            mask =
                mask or
                    (1 shl i)
        }

        return mask
    }

    private fun qTerminalFromMove(
        state: Int,
        action: Int,
        reward: Float
    ) {
            }

    /*
     * =========================
     * V2 ACTION SELECTION
     * =========================
     */

    private fun selectV2Action(
        state: Int,
        legal: List<Candidate>,
        training: Boolean
    ): Candidate {
        if (legal.isEmpty()) {
            return Candidate(
                dir,
                -1e9f,
                "无合法动作",
                false
            )
        }

        if (forcedStrategy >= 0) {
            return bestSurvivalStep(legal)
        }

        val epsilon =
            if (training) {
                0.1f
            } else {
                0f
            }

        if (
            training &&
            Random.nextFloat() < epsilon
        ) {
            val safe =
                legal.filter {
                    it.tailOk ||
                        it.region >=
                        max(
                            5,
                            snake.size / 2
                        )
                }

            if (safe.isNotEmpty()) {
                return safe[
                    Random.nextInt(
                        safe.size
                    )
                ]
            }

            return legal[
                Random.nextInt(
                    legal.size
                )
            ]
        }

        var best =
            legal.first()

        var bestValue =
            -Float.MAX_VALUE

        for (candidate in legal) {
            val action =
                dirs.indexOfFirst {
                    it == candidate.d
                }

            if (action < 0) continue

            val q =
                0f

            val visits =
                qVisit(
                    state,
                    action
                )

            val safetyBonus =
                when {
                    candidate.tailOk &&
                        candidate.region >= snake.size * 1.5f ->
                        2.2f

                    candidate.tailOk ->
                        1.2f

                    candidate.region >= snake.size ->
                        0.35f

                    else ->
                        -1.5f
                }

            val foodBonus =
                if (
                    candidate.ate
                ) {
                    4.0f
                } else if (
                    candidate.foodDist >= 0
                ) {
                    0.7f /
                        (
                            candidate.foodDist + 1
                        )
                } else {
                    0f
                }

            val visitBonus =
                0.12f /
                    kotlin.math.sqrt(
                        (visits + 1).toFloat()
                    )

            val value =
                q +
                    safetyBonus +
                    foodBonus +
                    visitBonus

            if (value > bestValue) {
                bestValue = value
                best =
                    candidate.copy(
                        qValue = q
                    )
            }
        }

        return best
    }

    /*
     * =========================
     * MAIN AI (Q表 + 神经网络混合，规则只做安全掩码)
     * =========================
     */

    private fun chooseMove(): P {
        // AI V3 路径
        if (v3Enabled && aiMode == 1) {
            return try {
                val state = toV3State()
                val ateFood = score > v3PrevScore
                v3PrevState?.let { prev ->
                    v3Engine.feedback(nextState = state, ateFood = ateFood, died = gameOver)
                }
                v3PrevScore = score
                val action = v3Engine.act(state)
                v3PrevState = state
                v3ActionToDir(action)
            } catch (e: Exception) {
                e.printStackTrace()
                dir
            }
        }

        aiStepStartNs =
            System.nanoTime()

        aiStepBudgetNs =
            budgetFor(gameSpeed)

        val futures:
            List<Future<Candidate>> =
            dirs.map { d ->
                aiPool.submit(
                    Callable {
                        evaluate(d)
                    }
                )
            }

        val candidates =
            futures.map {
                try {
                    it.get()
                } catch (_: Throwable) {
                    Candidate(
                        P(0, 0),
                        -1e9f,
                        "AI异常",
                        false
                    )
                }
            }

        val legal =
            candidates.filter {
                it.legal
            }

        if (legal.isEmpty()) {
            ai =
                Snapshot(
                    strategy = "NO MOVE",
                    reason =
                        "四个方向都无法前进",
                    danger = 5,
                    chosen = dir,
                    candidates = candidates
                )

            return dir
        }

        val danger =
            calculateDanger()

        val regionNow =
            freeRegion(snake)

        val foodDistNow =
            distance(
                snake.first(),
                food,
                snake,
                true
            )

        val state =
            buildState(
                snake,
                dir,
                food,
                hunger
            )

        /*
         * 第一层：真正安全的食物路线。
         * 这是硬安全层，不交给探索破坏。
         */
        val safeFood =
            findSafeFoodStep()

        if (safeFood != null) {
            val action =
                dirs.indexOfFirst {
                    it == safeFood
                }.coerceAtLeast(0)

            val q =
                0f

                        
            ai =
                Snapshot(
                    strategy = "V2 SAFE FOOD",
                    reason =
                        "安全路径可吃食物，吃后尾巴仍可达",
                    danger = danger,
                    region = regionNow,
                    spaceRatio =
                        regionNow.toFloat() /
                            max(
                                1,
                                snake.size
                            ),
                    tailReachable =
                        tailReachable(snake),
                    foodReachable = true,
                    foodDistance = foodDistNow,
                    hunger = hunger,
                    chosen = safeFood,
                    candidates = candidates,
                    depth = 2,
                    nodes = legal.size,
                    hungerFactor =
                        hungerFactorValue(),
                    regionWeight = wRegion,
                    strategyId = 10,
                    qValue = q,
                    nVisits =
                        qVisit(
                            state,
                            action
                        ),
                    forceEatActive = false,
                    forceEatSafe = true,
                    safeFollowMode = false
                )

            return safeFood
        }

        /*
         * 第二层：尾巴安全层。
         */
        val tailStep =
            followTailStep(legal)

        if (
            tailStep != null &&
            hunger < hungerForceEat()
        ) {
            val action =
                dirs.indexOfFirst {
                    it == tailStep
                }.coerceAtLeast(0)

            val q =
                0f

                        
            ai =
                Snapshot(
                    strategy = "V2 TAIL",
                    reason =
                        "食物路线风险较高，沿尾巴保持循环空间",
                    danger = danger,
                    region = regionNow,
                    spaceRatio =
                        regionNow.toFloat() /
                            max(
                                1,
                                snake.size
                            ),
                    tailReachable = true,
                    foodReachable =
                        foodDistNow >= 0,
                    foodDistance = foodDistNow,
                    hunger = hunger,
                    chosen = tailStep,
                    candidates = candidates,
                    depth = 1,
                    nodes = legal.size,
                    hungerFactor =
                        hungerFactorValue(),
                    regionWeight = wRegion,
                    strategyId = 11,
                    qValue = q,
                    nVisits =
                        qVisit(
                            state,
                            action
                        ),
                    forceEatActive = false,
                    forceEatSafe = false,
                    safeFollowMode = true
                )

            return tailStep
        }

        /*
         * 第三层：饥饿压力。
         * 仍然只允许尾巴/空间安全动作。
         */
        val forceThreshold =
            hungerForceEat()

        if (
            hunger >= forceThreshold &&
            foodDistNow >= 0
        ) {
            val safeFoodCandidates =
                legal.filter {
                    it.tailOk &&
                        it.foodDist >= 0
                }

            if (
                safeFoodCandidates.isNotEmpty()
            ) {
                val selected =
                    selectV2Action(
                        state,
                        safeFoodCandidates,
                        training = trainingMode ||
                            reinforceTraining
                    )

                val action =
                    dirs.indexOfFirst {
                        it == selected.d
                    }.coerceAtLeast(0)

                                
                ai =
                    Snapshot(
                        strategy = "V2 HUNGER",
                        reason =
                            "饥饿压力提高食物收益，但仍受安全屏蔽",
                        danger = max(
                            danger,
                            3
                        ),
                        region = regionNow,
                        spaceRatio =
                            regionNow.toFloat() /
                                max(
                                    1,
                                    snake.size
                                ),
                        tailReachable =
                            selected.tailOk,
                        foodReachable = true,
                        foodDistance =
                            selected.foodDist,
                        hunger = hunger,
                        chosen = selected.d,
                        candidates =
                            candidates.map {
                                if (it.d == selected.d) {
                                    it.copy(
                                        qValue =
                                            0f
                                    )
                                } else {
                                    it
                                }
                            },
                        depth = 1,
                        nodes = legal.size,
                        hungerFactor =
                            hungerFactorValue(),
                        regionWeight = wRegion,
                        strategyId = 12,
                        qValue =
                            0f,
                        nVisits =
                            qVisit(
                                state,
                                action
                            ),
                        forceEatActive = true,
                        forceEatSafe = true,
                        safeFollowMode = false
                    )

                return selected.d
            }
        }

        /*
         * 第四层：V2 Q-learning 正式决策。
         *
         * 先做安全屏蔽，再让 Q 值在安全动作中选择。
         */
        val shielded =
            legal.filter {
                val ratio =
                    it.region.toFloat() /
                        max(
                            1,
                            snake.size
                        )

                it.tailOk ||
                    ratio >= 1.0f ||
                    (
                        snake.size < 15 &&
                            ratio >= 0.75f
                        )
            }

        val pool =
            if (shielded.isNotEmpty()) {
                shielded
            } else {
                legal
            }

        // =========================================================
        // 规则决策（V2已删除）
        // =========================================================
        var best = pool.first()
        var bestValue = -Float.MAX_VALUE

        for (candidate in pool) {
            val action = dirs.indexOfFirst { it == candidate.d }
            if (action < 0) continue

            val q = 0f
            val rule = candidate.score

            // 混合分数：Q表分数 * 权重 + 神经网络分数 * 权重 * 放大系数 + 规则分数微调
            // 死局预判：如果食物周围空间不够，大幅降低吃食物的优先级
        val de = checkFoodDeadEnd()
        deadEndPredicted = de.first
        foodSpaceRatio = de.second
        var deadEndPenalty = 0f
        if (de.first) deadEndPenalty = -5f

        // 按需启用前瞻模拟：蛇长>20才启用，越长模拟越多步
        val rSteps = when {
            snake.size > 60 -> 5
            snake.size > 25 -> 3
            else -> 0
        }
        rolloutActive = rSteps > 0
        rolloutSteps = rSteps
        val rolloutScore = if (rSteps > 0) rolloutN(candidate.d, rSteps) else 0f
        val mixed = 1.0f * q + 0.0f * nn * 5f + rule * 0.001f + deadEndPenalty + rolloutScore * 0.5f
            if (mixed > bestValue) {
                bestValue = mixed
                best = candidate.copy(qValue = q)
            }
        }

        val action =
            dirs.indexOfFirst {
                it == best.d
            }.coerceAtLeast(0)

                
        ai =
            Snapshot(
                strategy = "混合进化 (Q表+NN)",
                reason = "规则过滤后，Q表与NN选出最优动作",
                danger = danger,
                region = regionNow,
                spaceRatio =
                    regionNow.toFloat() /
                        max(
                            1,
                            snake.size
                        ),
                tailReachable =
                    tailReachable(snake),
                foodReachable =
                    foodDistNow >= 0,
                foodDistance = foodDistNow,
                hunger = hunger,
                chosen = best.d,
                candidates =
                    candidates.map {
                        if (it.d == best.d) {
                            it.copy(
                                qValue =
                                    0f
                            )
                        } else {
                            it
                        }
                    },
                depth = 1,
                nodes = pool.size,
                hungerFactor =
                    hungerFactorValue(),
                regionWeight = wRegion,
                strategyId = 20,
                qValue =
                    0f,
                nVisits =
                    qVisit(
                        state,
                        action
                    ),
                forceEatActive = false,
                forceEatSafe = false,
                safeFollowMode = false
            )

        return best.d
    }

    private fun hungerFactorValue(): Float =
        when {
            hunger >= 60 -> 4f
            hunger >= 30 -> 2.5f
            hunger >= 15 -> 1.6f
            else -> 1f
        }

    /*
     * =========================
     * SAFE FOOD / TAIL
     * =========================
     */

    private fun followTailStep(
        legal: List<Candidate>
    ): P? {
        if (snake.size < 2) {
            return null
        }

        val path =
            shortestPath(
                snake.first(),
                snake.last(),
                snake,
                allowTail = true
            ) ?: return null

        if (path.isEmpty()) {
            return null
        }

        val step = path.first()

        if (
            legal.none {
                it.d == step
            }
        ) {
            return null
        }

        val sim =
            simulate(
                snake.first(),
                step
            )

        if (sim.body.isEmpty()) {
            return null
        }

        if (!tailReachable(sim.body)) {
            return null
        }

        val r =
            freeRegion(sim.body)

        if (
            r < 3 &&
            snake.size < total - 5
        ) {
            return null
        }

        return step
    }

    private fun findSafeFoodStep(): P? {
        val path =
            shortestPath(
                snake.first(),
                food,
                snake,
                allowTail = true
            ) ?: return null

        if (path.isEmpty()) {
            return null
        }

        val simBody =
            ArrayDeque(snake)

        var ate = false

        for (step in path) {
            val nh =
                P(
                    simBody.first().x + step.x,
                    simBody.first().y + step.y
                )

            if (!inside(nh)) {
                return null
            }

            val willEat =
                nh == food

            if (
                simBody.contains(nh) &&
                !(nh == simBody.last() && !willEat)
            ) {
                return null
            }

            simBody.addFirst(nh)

            if (!willEat) {
                simBody.removeLast()
            } else {
                ate = true
            }
        }

        if (!ate) {
            return null
        }

        if (!tailReachable(simBody)) {
            return null
        }

        val len =
            simBody.size

        val freeLeft =
            total - len

        if (len > 180 && freeLeft < 4) {
            return null
        }

        if (len > 150 && freeLeft < 6) {
            return null
        }

        if (len > 120 && freeLeft < 10) {
            return null
        }

        if (len > 90 && freeLeft < 14) {
            return null
        }

        if (len > 60 && freeLeft < 20) {
            return null
        }

        if (
            len <= 60 &&
            freeLeft >= 20
        ) {
            val r =
                freeRegion(simBody)

            if (
                r <
                max(
                    4,
                    freeLeft / 3
                )
            ) {
                return null
            }
        }

        return path.first()
    }

    /*
     * =========================
     * SURVIVAL HEURISTIC
     * =========================
     */

    private fun bestSurvivalStep(
        legal: List<Candidate>
    ): Candidate {
        var best =
            legal.first()

        var bestScore =
            -1e30f

        val len =
            snake.size

        val tailPos =
            snake.last()

        val bodySet =
            snake.toHashSet()

        val tailW =
            (
                wTailGood /
                    wTailGood0
                ).coerceIn(
                    0.8f,
                    1.2f
                )

        val spaceW =
            (
                wSpace /
                    wSpace0
                ).coerceIn(
                    0.8f,
                    1.2f
                )

        val foodW =
            (
                wFoodNear /
                    wFoodNear0
                ).coerceIn(
                    0.8f,
                    1.2f
                )

        for (cand in legal) {
            val sim =
                simulate(
                    snake.first(),
                    cand.d
                )

            if (sim.body.isEmpty()) {
                continue
            }

            val nh =
                sim.body.first()

            val r =
                freeRegion(sim.body)

            val t =
                tailReachable(sim.body)

            val mob =
                countSafeMoves(sim.body)

            val freeLeft =
                total -
                    sim.body.size

            var sc = 0f

            if (t) {
                sc +=
                    50000f *
                        tailW
            } else {
                sc -= 200000f

                if (sc > bestScore) {
                    bestScore = sc
                    best = cand
                }

                continue
            }

            sc +=
                r *
                    250f *
                    spaceW

            if (freeLeft > 0) {
                sc +=
                    (
                        r.toFloat() /
                            freeLeft
                        ) *
                        15000f *
                        spaceW
            }

            sc +=
                mob * 500f

            var bodyAdj = 0

            for (d in dirs) {
                val p =
                    P(
                        nh.x + d.x,
                        nh.y + d.y
                    )

                if (
                    bodySet.contains(p) ||
                    sim.body.contains(p)
                ) {
                    bodyAdj++
                }
            }

            sc +=
                bodyAdj * 600f

            val dToTail =
                distance(
                    nh,
                    tailPos,
                    sim.body,
                    true
                )

            if (dToTail >= 0) {
                sc +=
                    8000f /
                        (dToTail + 1)

                if (dToTail > 6) {
                    sc -=
                        (
                            dToTail - 6
                            ) * 150f
                }
            }

            val fd =
                distance(
                    nh,
                    food,
                    sim.body,
                    true
                )

            if (fd >= 0) {
                sc +=
                    (
                        500f * foodW
                        ) /
                        (fd + 1)
            }

            if (len >= 100) {
                sc += r * 300f
            }

            val nx =
                sim.body.first().x

            val ny =
                sim.body.first().y

            val edge =
                min(
                    min(
                        nx,
                        cols - 1 - nx
                    ),
                    min(
                        ny,
                        rows - 1 - ny
                    )
                )

            sc -=
                max(
                    0,
                    3 - edge
                ) * 800f

            val hx0 =
                snake.first().x

            val hy0 =
                snake.first().y

            val atEdgeNow =
                hx0 == 0 ||
                    hx0 == cols - 1 ||
                    hy0 == 0 ||
                    hy0 == rows - 1

            if (
                !atEdgeNow &&
                edge == 0 &&
                snake.size > 20
            ) {
                sc -= 6000f
            }

            if (
                nx == 0 ||
                nx == cols - 1 ||
                ny == 0 ||
                ny == rows - 1
            ) {
                sc -= 500f
            }

            if (sim.ate) {
                sc += 5000f
            }

            if (sc > bestScore) {
                bestScore = sc
                best = cand
            }
        }

        return best
    }

    /*
     * =========================
     * EVALUATION
     * =========================
     */

    private fun evaluate(d: P): Candidate {
        if (!legalDirection(d)) {
            return Candidate(
                d,
                -1e9f,
                "撞墙/身体",
                false
            )
        }

        val sim =
            simulate(
                snake.first(),
                d
            )

        val region =
            freeRegion(sim.body)

        val tail =
            tailReachable(sim.body)

        val foodDist =
            distance(
                sim.body.first(),
                food,
                sim.body,
                true
            )

        val ate =
            sim.ate

        val mobility =
            countSafeMoves(sim.body)

        val hungerFactor =
            hungerFactorValue()

        val lenBoost =
            if (
                snake.size >=
                safeFollowLength
            ) {
                (
                    snake.size.toFloat() /
                        safeFollowLength
                    ).coerceIn(
                        1f,
                        3f
                    )
            } else {
                1f
            }

        val regionScoreVal =
            region *
                wRegion *
                lenBoost

        val mobilityScoreVal =
            mobility *
                wMobility

        val tailScoreVal =
            if (tail) {
                wTailGood *
                    lenBoost
            } else {
                wTailBad *
                    lenBoost
            }

        var foodScoreVal =
            if (foodDist >= 0) {
                hungerFactor *
                    aggression *
                    (
                        wFoodNear /
                            (foodDist + 1)
                        )
            } else {
                -450f *
                    hungerFactor
            }

        if (ate) {
            foodScoreVal +=
                wFoodAte *
                    aggression
        }

        var eatPenalty = 0f

        if (ate) {
            val afterSize =
                sim.body.size

            val needSpace =
                (
                    afterSize *
                        safetyMargin
                    ).toInt() + 2

            if (
                !tail ||
                region < needSpace
            ) {
                eatPenalty =
                    -2500f -
                        snake.size * 35f
            } else {
                val after =
                    ArrayDeque(sim.body)

                val dx =
                    after.last().x -
                        after.first().x

                val dy =
                    after.last().y -
                        after.first().y

                val follow =
                    when {
                        abs(dx) >= abs(dy) &&
                            dx != 0 ->
                            P(
                                if (dx > 0) 1 else -1,
                                0
                            )

                        dy != 0 ->
                            P(
                                0,
                                if (dy > 0) 1 else -1
                            )

                        else ->
                            null
                    }

                if (
                    follow != null &&
                    canSim(
                        after,
                        follow
                    )
                ) {
                    val next =
                        simulateOn(
                            after,
                            follow
                        )

                    val r2 =
                        freeRegion(
                            next.body
                        )

                    val t2 =
                        tailReachable(
                            next.body
                        )

                    if (
                        !t2 ||
                        r2 <
                        (
                            afterSize *
                                0.85f
                            ).toInt()
                    ) {
                        eatPenalty =
                            -1500f -
                                snake.size * 25f
                    }
                }
            }
        }

        val edge =
            min(
                min(
                    sim.body.first().x,
                    cols - 1 -
                        sim.body.first().x
                ),
                min(
                    sim.body.first().y,
                    rows - 1 -
                        sim.body.first().y
                )
            )

        val edgeScoreVal =
            -max(
                0,
                2 - edge
            ) * wEdge

        val spacePenalty =
            max(
                0f,
                snake.size *
                    safetyMargin -
                    region.toFloat()
            )

        val spaceScoreVal =
            -spacePenalty *
                wSpace

        val totalScore =
            regionScoreVal +
                mobilityScoreVal +
                tailScoreVal +
                foodScoreVal +
                edgeScoreVal +
                spaceScoreVal +
                eatPenalty

        val reason =
            when {
                ate &&
                    eatPenalty < 0 ->
                    "吃完会困死，避开"

                ate ->
                    "马上吃到食物"

                tail ->
                    "保持尾巴可达"

                else ->
                    "扩大可用空间"
            }

        return Candidate(
            d = d,
            score = totalScore,
            reason = reason,
            legal = true,
            regionScore =
                regionScoreVal,
            mobilityScore =
                mobilityScoreVal,
            tailScore =
                tailScoreVal,
            foodScore =
                foodScoreVal,
            edgeScore =
                edgeScoreVal,
            spaceScore =
                spaceScoreVal,
            region = region,
            mobility = mobility,
            tailOk = tail,
            foodDist = foodDist,
            ate = ate
        )
    }

    /*
     * =========================
     * OLD ADAPTIVE WEIGHTS
     * =========================
     */

    private fun clampW(
        v: Float,
        lo: Float,
        hi: Float
    ): Float =
        v.coerceIn(lo, hi)

    private fun rewardEatStep() {
        wFoodAte =
            clampW(
                wFoodAte * 1.003f,
                wFoodAte0 * 0.85f,
                wFoodAte0 * 1.15f
            )

        wTailGood =
            clampW(
                wTailGood * 1.002f,
                wTailGood0 * 0.85f,
                wTailGood0 * 1.15f
            )

        wFoodNear =
            clampW(
                wFoodNear * 1.001f,
                wFoodNear0 * 0.85f,
                wFoodNear0 * 1.15f
            )
    }

    private fun adjustWeights(
        cause: String
    ) {
        val beforeEdge = wEdge
        val beforeTail = wTailGood
        val beforeSpace = wSpace
        val beforeFood = wFoodNear
        val beforeAgg = aggression
        val beforeSafety = safetyMargin

        when (cause) {
            "WALL" -> {
                wEdge =
                    clampW(
                        wEdge * 1.03f,
                        wEdge0 * 0.9f,
                        wEdge0 * 1.1f
                    )

                aggression =
                    clampW(
                        aggression * 0.99f,
                        0.95f,
                        1.35f
                    )
            }

            "SELF" -> {
                wTailGood =
                    clampW(
                        wTailGood * 1.03f,
                        wTailGood0 * 0.9f,
                        wTailGood0 * 1.1f
                    )

                wTailBad =
                    clampW(
                        wTailBad * 1.02f,
                        wTailBad0 * 1.1f,
                        wTailBad0 * 0.9f
                    )

                safetyMargin =
                    clampW(
                        safetyMargin * 1.01f,
                        1.0f,
                        1.20f
                    )
            }

            "TRAP" -> {
                wSpace =
                    clampW(
                        wSpace * 1.04f,
                        wSpace0 * 0.9f,
                        wSpace0 * 1.1f
                    )

                wRegion =
                    clampW(
                        wRegion * 1.02f,
                        wRegion0 * 0.9f,
                        wRegion0 * 1.1f
                    )

                safetyMargin =
                    clampW(
                        safetyMargin * 1.01f,
                        1.0f,
                        1.20f
                    )

                aggression =
                    clampW(
                        aggression * 1.005f,
                        0.95f,
                        1.35f
                    )

                wFoodAte =
                    clampW(
                        wFoodAte * 1.02f,
                        wFoodAte0 * 0.9f,
                        wFoodAte0 * 1.1f
                    )
            }

            "HUNGER" -> {
                wFoodNear =
                    clampW(
                        wFoodNear * 1.04f,
                        wFoodNear0 * 0.9f,
                        wFoodNear0 * 1.1f
                    )

                wFoodAte =
                    clampW(
                        wFoodAte * 1.03f,
                        wFoodAte0 * 0.9f,
                        wFoodAte0 * 1.1f
                    )

                aggression =
                    clampW(
                        aggression * 1.02f,
                        0.95f,
                        1.35f
                    )

                wSpace =
                    clampW(
                        wSpace * 0.98f,
                        wSpace0 * 0.9f,
                        wSpace0 * 1.1f
                    )

                safetyMargin =
                    clampW(
                        safetyMargin * 0.99f,
                        1.0f,
                        1.20f
                    )
            }
        }

        wRegion =
            wRegion * 0.95f +
                wRegion0 * 0.05f

        wMobility =
            wMobility * 0.95f +
                wMobility0 * 0.05f

        wEdge =
            wEdge * 0.95f +
                wEdge0 * 0.05f

        wSpace =
            wSpace * 0.95f +
                wSpace0 * 0.05f

        wFoodNear =
            wFoodNear * 0.95f +
                wFoodNear0 * 0.05f

        wTailGood =
            wTailGood * 0.95f +
                wTailGood0 * 0.05f

        wFoodAte =
            wFoodAte * 0.95f +
                wFoodAte0 * 0.05f

        lastLearnAction =
            when (cause) {
                "WALL" ->
                    "边界${"%.0f→%.0f".format(
                        beforeEdge,
                        wEdge
                    )} 攻${"%.2f→%.2f".format(
                        beforeAgg,
                        aggression
                    )}"

                "SELF" ->
                    "尾+${"%.0f→%.0f".format(
                        beforeTail,
                        wTailGood
                    )} 安全${"%.2f→%.2f".format(
                        beforeSafety,
                        safetyMargin
                    )}"

                "TRAP" ->
                    "空间${"%.0f→%.0f".format(
                        beforeSpace,
                        wSpace
                    )} 安全${"%.2f→%.2f".format(
                        beforeSafety,
                        safetyMargin
                    )}"

                "HUNGER" ->
                    "食近${"%.0f→%.0f".format(
                        beforeFood,
                        wFoodNear
                    )} 攻${"%.2f→%.2f".format(
                        beforeAgg,
                        aggression
                    )}"

                else ->
                    "微调"
            }
    }

    /*
     * =========================
     * PERSISTENCE
     *
     * Training state (Population + Q table) is now persisted
     * to internal storage to allow resuming after app restart.
     * =========================
     */

    private fun saveTrainingState() {
        try {
            val file = context.getFileStreamPath("snake_training.dat")
            val genCopy: Int
            synchronized(sharedLock) {
                genCopy = generation
            }
            DataOutputStream(BufferedOutputStream(FileOutputStream(file))).use { out ->
                out.writeInt(genCopy)
            }
        } catch (e: Exception) {
            e.printStackTrace()
        }
    }

    private fun loadTrainingState() {
        try {
            val file = context.getFileStreamPath("snake_training.dat")
            if (!file.exists()) return
            DataInputStream(BufferedInputStream(FileInputStream(file))).use { input ->
                generation = input.readInt()
            }
        } catch (e: Exception) {
            e.printStackTrace()
        }
    }

    private fun saveLearning() {
        synchronized(sharedLock) {
            prefs.edit()
                .putFloat(
                    "learn_aggression",
                    aggression
                )
                .putFloat(
                    "learn_safety",
                    safetyMargin
                )
                .putFloat(
                    "learn_shortcut",
                    shortcutBonus
                )
                .putFloat(
                    "w_region",
                    wRegion
                )
                .putFloat(
                    "w_mobility",
                    wMobility
                )
                .putFloat(
                    "w_tail_good",
                    wTailGood
                )
                .putFloat(
                    "w_tail_bad",
                    wTailBad
                )
                .putFloat(
                    "w_food_near",
                    wFoodNear
                )
                .putFloat(
                    "w_food_ate",
                    wFoodAte
                )
                .putFloat(
                    "w_edge",
                    wEdge
                )
                .putFloat(
                    "w_space",
                    wSpace
                )
                .putString(
                    "last_learn_action",
                    lastLearnAction
                )
                .putInt(
                    "stat_wall",
                    deathWall
                )
                .putInt(
                    "stat_self",
                    deathSelf
                )
                .putInt(
                    "stat_trap",
                    deathTrap
                )
                .putInt(
                    "stat_total",
                    totalGames
                )
                .putInt(
                    "money",
                    money
                )
                .putInt(
                    "high_score",
                    highScore
                )
                .apply()
        }
    }

    private fun die(
        cause: String
    ) {
        gameOver = true
        deathCause = cause

        when (cause) {
            "WALL" ->
                deathWall++

            "SELF" ->
                deathSelf++

            "HUNGER" ->
                deathTrap++

            else ->
                deathTrap++
        }

        adjustWeights(cause)

        totalGames++
        heartbeat()

        recentScores.addLast(score)

        while (recentScores.size > 50) {
            recentScores.removeFirst()
        }

        if (score > bestRecentScore) {
            bestRecentScore = score
        }

        aggression =
            when (cause) {
                "WALL" ->
                    max(
                        0.9f,
                        aggression * 0.99f
                    )

                "SELF" ->
                    max(
                        0.9f,
                        aggression * 0.995f
                    )

                "HUNGER" ->
                    min(
                        1.4f,
                        aggression * 1.03f
                    )

                else ->
                    max(
                        0.9f,
                        aggression * 0.99f
                    )
            }

        if (cause == "TRAP") {
            safetyMargin =
                min(
                    1.20f,
                    safetyMargin * 1.01f
                )
        }

        if (cause == "HUNGER") {
            safetyMargin =
                max(
                    1.0f,
                    safetyMargin * 0.99f
                )
        }

        safetyMargin =
            safetyMargin * 0.95f +
                1.08f * 0.05f

        aggression =
            aggression * 0.95f +
                1.15f * 0.05f

        safetyMargin =
            safetyMargin.coerceIn(
                1.0f,
                1.20f
            )

        aggression =
            aggression.coerceIn(
                0.95f,
                1.35f
            )

        lastDeathInfo =
            "死因=$cause 长度=${snake.size} 分=$score " +
                "空间=${ai.region} 需求=${(
                    snake.size *
                        safetyMargin
                    ).toInt()}"

        saveLearning()

        if (trainingMode) {
            reset()
            return
        }

        flash = 1f
        vibrateDeath()

        restartCountdown = 0L

        invalidate()
    }

    /*
     * =========================
     * SIMULATION / PATH
     * =========================
     */

    private fun simulate(
        head: P,
        d: P
    ): Sim =
        simulateOn(
            ArrayDeque(snake),
            d
        )

    private fun simulateOn(
        src: ArrayDeque<P>,
        d: P
    ): Sim {
        val b =
            ArrayDeque(src)

        if (b.isEmpty()) {
            return Sim(
                b,
                false
            )
        }

        val nh =
            P(
                b.first().x + d.x,
                b.first().y + d.y
            )

        if (!inside(nh)) {
            return Sim(
                b,
                false
            )
        }

        val ate =
            nh == food

        if (
            b.contains(nh) &&
            !(nh == b.last() && !ate)
        ) {
            return Sim(
                b,
                false
            )
        }

        b.addFirst(nh)

        if (!ate) {
            b.removeLast()
        }

        return Sim(
            b,
            ate
        )
    }

    // N步前瞻模拟：给定方向，模拟走n步，返回评分
    private fun rolloutN(startDir: P, maxSteps: Int): Float {
        var body = ArrayDeque(snake)
        var dir = startDir
        var score = 0f
        val dirs = listOf(P(0,-1), P(0,1), P(-1,0), P(1,0))
        for (step in 0 until maxSteps) {
            // 找这个方向上最安全的下一步
            var bestNext: P? = null
            var bestSpace = -1
            for (d in dirs) {
                val nh = P(body.first().x + d.x, body.first().y + d.y)
                if (!inside(nh)) continue
                val isTail = nh == body.last()
                if (body.contains(nh) && !isTail) continue
                // 数周围空间
                var space = 0
                for (sd in dirs) {
                    val sx = nh.x + sd.x
                    val sy = nh.y + sd.y
                    if (sx in 0 until cols && sy in 0 until rows) {
                        if (!body.any { it.x == sx && it.y == sy }) space++
                    }
                }
                if (space > bestSpace) { bestSpace = space; bestNext = d }
            }
            if (bestNext == null) return -50f + step * -10f // 死了
            val sim = simulateOn(body, bestNext)
            body = sim.body
            score += 5f // 每活一步+5
            if (sim.ate) score += 15f // 吃到食物额外+15
            dir = bestNext
        }
        return score
    }

    private fun simulateForBody(
        src: ArrayDeque<P>,
        d: P,
        target: P
    ): Sim {
        val b =
            ArrayDeque(src)

        if (b.isEmpty()) {
            return Sim(
                b,
                false
            )
        }

        val nh =
            P(
                b.first().x + d.x,
                b.first().y + d.y
            )

        if (!inside(nh)) {
            return Sim(
                b,
                false
            )
        }

        val ate =
            nh == target

        if (
            b.contains(nh) &&
            !(nh == b.last() && !ate)
        ) {
            return Sim(
                b,
                false
            )
        }

        b.addFirst(nh)

        if (!ate) {
            b.removeLast()
        }

        return Sim(
            b,
            ate
        )
    }

    private fun canSim(
        body: ArrayDeque<P>,
        d: P
    ): Boolean {
        if (body.isEmpty()) {
            return false
        }

        val h =
            body.first()

        val nh =
            P(
                h.x + d.x,
                h.y + d.y
            )

        if (!inside(nh)) {
            return false
        }

        val ate =
            nh == food

        return !body.contains(nh) ||
            (
                nh == body.last() &&
                    !ate
                )
    }

    private fun legalDirection(
        d: P
    ): Boolean =
        d != P(0, 0) &&
            !isReverse(d, dir) &&
            canSim(snake, d)

    private fun isReverse(
        a: P,
        b: P
    ): Boolean =
        a.x == -b.x &&
            a.y == -b.y

    private fun directionOfFirst(
        body: ArrayDeque<P>
    ): P {
        if (body.size < 2) {
            return dir
        }

        return P(
            body.elementAt(0).x -
                body.elementAt(1).x,
            body.elementAt(0).y -
                body.elementAt(1).y
        )
    }

    private fun inside(
        p: P
    ): Boolean =
        p.x in 0 until cols &&
            p.y in 0 until rows

    private fun shortestPath(
        start: P,
        target: P,
        body: Collection<P>,
        allowTail: Boolean
    ): List<P>? {
        if (start == target) {
            return emptyList()
        }

        if (!inside(start) ||
            !inside(target)
        ) {
            return null
        }

        val visited =
            tlVisited.get()

        val queue =
            tlQueue.get()

        val parent =
            IntArray(total) {
                -1
            }

        val parentDir =
            arrayOfNulls<P>(total)

        java.util.Arrays.fill(
            visited,
            0,
            total,
            false
        )

        for (p in body) {
            if (!inside(p)) continue

            visited[
                p.y * cols + p.x
            ] = true
        }

        if (
            allowTail &&
            body.isNotEmpty()
        ) {
            val last =
                body.last()

            if (inside(last)) {
                visited[
                    last.y * cols +
                        last.x
                ] = false
            }
        }

        val startIndex =
            start.y * cols +
                start.x

        val targetIndex =
            target.y * cols +
                target.x

        visited[startIndex] = true

        var head = 0
        var tail = 0

        queue[tail++] =
            startIndex

        var found = false

        while (head < tail) {
            val curr =
                queue[head++]

            if (curr == targetIndex) {
                found = true
                break
            }

            val cx =
                curr % cols

            val cy =
                curr / cols

            val candidates =
                arrayOf(
                    P(0, -1) to
                        if (cy > 0)
                            curr - cols
                        else -1,

                    P(0, 1) to
                        if (cy < rows - 1)
                            curr + cols
                        else -1,

                    P(-1, 0) to
                        if (cx > 0)
                            curr - 1
                        else -1,

                    P(1, 0) to
                        if (cx < cols - 1)
                            curr + 1
                        else -1
                )

            for ((d, ni) in candidates) {
                if (ni < 0 ||
                    ni >= total
                ) continue

                if (visited[ni]) continue

                visited[ni] = true

                parent[ni] = curr
                parentDir[ni] = d

                if (tail < total) {
                    queue[tail++] =
                        ni
                }
            }
        }

        if (!found) {
            return null
        }

        val steps =
            ArrayList<P>()

        var cur =
            targetIndex

        while (
            cur != startIndex
        ) {
            val d =
                parentDir[cur]
                    ?: return null

            steps.add(d)

            cur =
                parent[cur]

            if (cur < 0) {
                return null
            }
        }

        steps.reverse()

        return steps
    }

    /*
     * =========================
     * FLOOD / DISTANCE
     * =========================
     */

    private fun freeRegion(
        body: ArrayDeque<P>
    ): Int {
        if (body.isEmpty()) {
            return 0
        }

        val visited =
            tlVisited.get()

        val queue =
            tlQueue.get()

        java.util.Arrays.fill(
            visited,
            0,
            total,
            false
        )

        for (p in body) {
            if (!inside(p)) continue

            visited[
                p.y * cols + p.x
            ] = true
        }

        val start =
            body.first()

        if (!inside(start)) {
            return 0
        }

        val startIndex =
            start.y * cols +
                start.x

        visited[startIndex] = true

        var head = 0
        var tail = 0

        queue[tail++] =
            startIndex

        var count = 0

        while (head < tail) {
            val curr =
                queue[head++]

            val cx =
                curr % cols

            val cy =
                curr / cols

            count++

            if (cx > 0) {
                val ni =
                    curr - 1

                if (!visited[ni]) {
                    visited[ni] = true

                    if (tail < total) {
                        queue[tail++] =
                            ni
                    }
                }
            }

            if (cx < cols - 1) {
                val ni =
                    curr + 1

                if (!visited[ni]) {
                    visited[ni] = true

                    if (tail < total) {
                        queue[tail++] =
                            ni
                    }
                }
            }

            if (cy > 0) {
                val ni =
                    curr - cols

                if (!visited[ni]) {
                    visited[ni] = true

                    if (tail < total) {
                        queue[tail++] =
                            ni
                    }
                }
            }

            if (cy < rows - 1) {
                val ni =
                    curr + cols

                if (!visited[ni]) {
                    visited[ni] = true

                    if (tail < total) {
                        queue[tail++] =
                            ni
                    }
                }
            }
        }

        return count
    }

    private fun distance(
        start: P,
        target: P,
        body: Collection<P>,
        allowTail: Boolean
    ): Int {
        if (!inside(start) ||
            !inside(target)
        ) {
            return -1
        }

        if (start == target) {
            return 0
        }

        val visited =
            tlVisited.get()

        val queue =
            tlQueue.get()

        java.util.Arrays.fill(
            visited,
            0,
            total,
            false
        )

        for (p in body) {
            if (!inside(p)) continue

            visited[
                p.y * cols + p.x
            ] = true
        }

        if (
            allowTail &&
            body.isNotEmpty()
        ) {
            val last =
                body.last()

            if (inside(last)) {
                visited[
                    last.y * cols +
                        last.x
                ] = false
            }
        }

        val startIndex =
            start.y * cols +
                start.x

        visited[startIndex] = true

        var head = 0
        var tail = 0

        queue[tail++] =
            startIndex

        var dist = 0

        while (head < tail) {
            val layerSize =
                tail - head

            repeat(layerSize) {
                if (head >= tail) {
                    return@repeat
                }

                val curr =
                    queue[head++]

                val cx =
                    curr % cols

                val cy =
                    curr / cols

                if (
                    cx == target.x &&
                    cy == target.y
                ) {
                    return dist
                }

                if (cx > 0) {
                    val ni =
                        curr - 1

                    if (!visited[ni]) {
                        visited[ni] = true

                        if (tail < total) {
                            queue[tail++] =
                                ni
                        }
                    }
                }

                if (cx < cols - 1) {
                    val ni =
                        curr + 1

                    if (!visited[ni]) {
                        visited[ni] = true

                        if (tail < total) {
                            queue[tail++] =
                                ni
                        }
                    }
                }

                if (cy > 0) {
                    val ni =
                        curr - cols

                    if (!visited[ni]) {
                        visited[ni] = true

                        if (tail < total) {
                            queue[tail++] =
                                ni
                        }
                    }
                }

                if (cy < rows - 1) {
                    val ni =
                        curr + cols

                    if (!visited[ni]) {
                        visited[ni] = true

                        if (tail < total) {
                            queue[tail++] =
                                ni
                        }
                    }
                }
            }

            dist++
        }

        return -1
    }

    private fun countSafeMoves(
        body: ArrayDeque<P>
    ): Int =
        countSafeMovesFor(
            body,
            directionOfFirst(body),
            food
        )

    private fun countSafeMovesFor(
        body: ArrayDeque<P>,
        heading: P,
        target: P
    ): Int {
        if (body.isEmpty()) {
            return 0
        }

        val h =
            body.first()

        return dirs.count { d ->
            if (isReverse(d, heading)) {
                return@count false
            }

            val nh =
                P(
                    h.x + d.x,
                    h.y + d.y
                )

            if (!inside(nh)) {
                return@count false
            }

            val ate =
                nh == target

            !body.contains(nh) ||
                (
                    nh == body.last() &&
                        !ate
                    )
        }
    }

    private fun tailReachable(
        body: ArrayDeque<P>
    ): Boolean =
        if (body.isEmpty()) {
            false
        } else {
            distance(
                body.first(),
                body.last(),
                body,
                true
            ) >= 0
        }

    // 死局预判：从食物位置BFS算自由空间，如果空间不够蛇身长就是死局
    private fun checkFoodDeadEnd(): Pair<Boolean, Float> {
        if (snake.isEmpty()) return Pair(false, 10f)
        val visited = Array(cols) { BooleanArray(rows) }
        val queue = ArrayDeque<P>()
        queue.addLast(food)
        visited[food.x][food.y] = true
        var space = 0
        while (!queue.isEmpty()) {
            val cur = queue.removeFirst()
            space++
            val dirs = listOf(P(0,-1), P(0,1), P(-1,0), P(1,0))
            for (d in dirs) {
                val nx = cur.x + d.x
                val ny = cur.y + d.y
                if (nx in 0 until cols && ny in 0 until rows && !visited[nx][ny]) {
                    val isBody = snake.any { it.x == nx && it.y == ny }
                    if (!isBody) {
                        visited[nx][ny] = true
                        queue.addLast(P(nx, ny))
                    }
                }
            }
        }
        val ratio = space.toFloat() / snake.size
        val deadEnd = ratio < 1.2f
        return Pair(deadEnd, ratio)
    }

    private fun calculateDanger(): Int {
        val region =
            freeRegion(snake)

        val ratio =
            region.toFloat() /
                max(
                    1,
                    snake.size
                )

        val mobility =
            countSafeMoves(snake)

        return when {
            mobility <= 0 -> 5
            ratio < 1.5f -> 5
            ratio < 2.2f -> 4
            ratio < 3.5f -> 3
            ratio < 5f -> 2
            else -> 1
        }
    }

    private fun placeFood() {
        val free =
            ArrayList<P>()

        for (x in 0 until cols) {
            for (y in 0 until rows) {
                val p =
                    P(x, y)

                if (!snake.contains(p)) {
                    free.add(p)
                }
            }
        }

        if (free.isNotEmpty()) {
            food =
                free[
                    Random.nextInt(
                        free.size
                    )
                ]
        }
    }

    /*
     * =========================
     * EFFECTS
     * =========================
     */

    private fun spawnFoodEffect(
        p: P
    ) {
        repeat(14) {
            particles.add(
                Particle(
                    p.x.toFloat(),
                    p.y.toFloat(),
                    Random.nextFloat() - 0.5f,
                    Random.nextFloat() - 0.5f,
                    1f,
                    Color.YELLOW
                )
            )
        }

        floats.add(
            FloatText(
                p.x.toFloat(),
                p.y.toFloat(),
                1f,
                "+10"
            )
        )
    }

    private fun updateEffects(
        dt: Float
    ) {
        flash =
            max(
                0f,
                flash -
                    dt * 0.035f
            )

        particles.forEach {
            it.x +=
                it.vx * dt

            it.y +=
                it.vy * dt

            it.life -=
                dt * 0.035f
        }

        particles.removeAll {
            it.life <= 0f
        }

        floats.forEach {
            it.y -=
                dt * 0.04f

            it.life -=
                dt * 0.025f
        }

        floats.removeAll {
            it.life <= 0f
        }
    }

    /*
     * =========================
     * DRAWING
     * =========================
     */

    override fun onSizeChanged(
        w: Int,
        h: Int,
        oldw: Int,
        oldh: Int
    ) {
        val hudReserve =
            760f + 24f

        val availTop =
            12f

        val availBottom =
            (
                h - hudReserve
                ).coerceAtLeast(
                    availTop +
                        h * 0.30f
                )

        val availH =
            availBottom -
                availTop

        cell =
            min(
                w.toFloat() / cols,
                availH / rows
            )

        ox =
            (
                w -
                    cols * cell
                ) / 2f

        val baseOy =
            availTop +
                (
                    availH -
                        rows * cell
                    ) / 2f

        val moveDown =
            cell * 2.5f

        val maxOy =
            availBottom -
                rows * cell

        oy =
            (
                baseOy +
                    moveDown
                ).coerceAtMost(
                    maxOy
                )
    }

    override fun onDraw(
        c: Canvas
    ) {
        super.onDraw(c)

        if (reinforceTraining || trainingMode) {
            c.drawColor(
                Color.BLACK
            )
            // 训练模式：全屏HUD，不画棋盘

            text.textAlign =
                Paint.Align.LEFT

            drawDebug(c)

            return
        }

        c.drawColor(
            bgColor
        )

        gridPaint.color =
            gridColor

        gridPaint.style =
            Paint.Style.STROKE

        gridPaint.strokeWidth =
            1f

        for (i in 0..cols) {
            c.drawLine(
                ox + i * cell,
                oy,
                ox + i * cell,
                oy + rows * cell,
                gridPaint
            )
        }

        for (i in 0..rows) {
            c.drawLine(
                ox,
                oy + i * cell,
                ox + cols * cell,
                oy + i * cell,
                gridPaint
            )
        }

        drawFood(c)
        drawSnake(c)
        drawParticles(c)
        drawDebug(c)

        if (gameOver) {
            drawGameOver(c)
        }
    }

    private fun drawFood(
        c: Canvas
    ) {
        val cx =
            ox +
                (food.x + 0.5f) *
                cell

        val cy =
            oy +
                (food.y + 0.5f) *
                cell

        foodPaint.color =
            Color.argb(
                90,
                255,
                80,
                80
            )

        c.drawCircle(
            cx,
            cy,
            cell * 0.38f,
            foodPaint
        )

        foodPaint.color =
            Color.RED

        c.drawCircle(
            cx,
            cy,
            cell * 0.22f,
            foodPaint
        )

        foodPaint.color =
            Color.WHITE

        c.drawCircle(
            cx,
            cy,
            cell * 0.07f,
            foodPaint
        )
    }

    private fun drawSnake(
        c: Canvas
    ) {
        if (snake.isEmpty()) {
            return
        }

        snakePaint.strokeWidth =
            max(
                8f,
                cell * 0.62f
            )

        val list =
            snake.toList()

        for (i in 0 until list.size - 1) {
            val a =
                list[i]

            val b =
                list[i + 1]

            snakePaint.color =
                if (rainbowSkin) {
                    hsv[
                        (i * 23 +
                            score) %
                            360
                    ]
                } else {
                    bodyColor
                }

            c.drawLine(
                ox +
                    (a.x + 0.5f) *
                    cell,
                oy +
                    (a.y + 0.5f) *
                    cell,
                ox +
                    (b.x + 0.5f) *
                    cell,
                oy +
                    (b.y + 0.5f) *
                    cell,
                snakePaint
            )
        }

        val h =
            snake.first()

        headPaint.color =
            headColor

        c.drawCircle(
            ox +
                (h.x + 0.5f) *
                cell,
            oy +
                (h.y + 0.5f) *
                cell,
            cell * 0.36f,
            headPaint
        )

        val ex =
            when {
                dir.x > 0 -> 0.12f
                dir.x < 0 -> -0.12f
                else -> 0f
            }

        val ey =
            when {
                dir.y > 0 -> 0.12f
                dir.y < 0 -> -0.12f
                else -> 0f
            }

        paint.color =
            Color.WHITE

        c.drawCircle(
            ox +
                (h.x + 0.5f) *
                cell +
                cell *
                (0.13f + ex),
            oy +
                (h.y + 0.5f) *
                cell +
                cell *
                (0.13f + ey),
            cell * 0.075f,
            paint
        )

        c.drawCircle(
            ox +
                (h.x + 0.5f) *
                cell -
                cell *
                (0.13f - ex),
            oy +
                (h.y + 0.5f) *
                cell -
                cell *
                (0.13f - ey),
            cell * 0.075f,
            paint
        )
    }

    private fun drawParticles(
        c: Canvas
    ) {
        particles.forEach {
            paint.color =
                Color.argb(
                    (
                        it.life * 255
                        ).toInt()
                        .coerceIn(
                            0,
                            255
                        ),
                    Color.red(
                        it.color
                    ),
                    Color.green(
                        it.color
                    ),
                    Color.blue(
                        it.color
                    )
                )

            c.drawCircle(
                ox +
                    (it.x + 0.5f) *
                    cell,
                oy +
                    (it.y + 0.5f) *
                    cell,
                max(
                    2f,
                    cell * 0.05f
                ),
                paint
            )
        }

        text.textAlign =
            Paint.Align.CENTER

        text.textSize =
            cell * 0.3f

        floats.forEach {
            text.color =
                Color.argb(
                    (
                        it.life * 255
                        ).toInt()
                        .coerceIn(
                            0,
                            255
                        ),
                    255,
                    215,
                    0
                )

            c.drawText(
                it.text,
                ox +
                    (it.x + 0.5f) *
                    cell,
                oy +
                    (it.y + 0.3f) *
                    cell,
                text
            )
        }
    }

    private fun drawDangerGauge(
        c: Canvas,
        cx: Float,
        cy: Float,
        r: Float,
        danger: Int
    ) {
        val arcPaint =
            Paint(
                Paint.ANTI_ALIAS_FLAG
            )

        arcPaint.style =
            Paint.Style.STROKE

        arcPaint.strokeWidth =
            13f

        arcPaint.strokeCap =
            Paint.Cap.ROUND

        val oval =
            RectF(
                cx - r,
                cy - r,
                cx + r,
                cy + r
            )

        arcPaint.color =
            Color.rgb(
                50,
                50,
                50
            )

        c.drawArc(
            oval,
            -90f,
            360f,
            false,
            arcPaint
        )

        arcPaint.color =
            when (danger) {
                1 -> Color.GREEN
                2 ->
                    Color.rgb(
                        150,
                        255,
                        80
                    )

                3 -> Color.YELLOW

                4 ->
                    Color.rgb(
                        255,
                        150,
                        0
                    )

                else ->
                    Color.RED
            }

        c.drawArc(
            oval,
            -90f,
            360f *
                (
                    danger.coerceIn(
                        1,
                        5
                    ) / 5f
                    ),
            false,
            arcPaint
        )
    }

    private val prevWeights = FloatArray(8) { 1f }

    private fun drawWeightBars(
        c: Canvas,
        left: Float,
        top: Float,
        w: Float,
        h: Float
    ) {
        val names =
            listOf(
                "区域",
                "机动",
                "尾+",
                "尾-",
                "食近",
                "食吃",
                "边界",
                "空间"
            )

        val values =
            floatArrayOf(
                wRegion / wRegion0,
                wMobility / wMobility0,
                wTailGood / wTailGood0,
                wTailBad / wTailBad0,
                wFoodNear / wFoodNear0,
                wFoodAte / wFoodAte0,
                wEdge / wEdge0,
                wSpace / wSpace0
            )

        val barW =
            w / names.size

        val maxRatio =
            2.0f

        names.forEachIndexed {
                i,
                name ->
            val x =
                left +
                    i * barW

            val ratio =
                values[i].coerceIn(
                    0f,
                    maxRatio
                )

            val barH =
                h *
                    (
                        ratio /
                            maxRatio
                        )

            barPaint.style =
                Paint.Style.FILL

            barPaint.color =
                Color.rgb(
                    40,
                    40,
                    40
                )

            c.drawRect(
                x + 3f,
                top,
                x + barW - 8f,
                top + h,
                barPaint
            )

            barPaint.color =
                Color.rgb(
                    100,
                    100,
                    100
                )

            val baseY =
                top +
                    h -
                    h *
                    (
                        1f /
                            maxRatio
                        )

            c.drawLine(
                x + 3f,
                baseY,
                x + barW - 8f,
                baseY,
                barPaint
            )

            // 涨跌检测：和上一帧比较
            val prevRatio = prevWeights.getOrElse(i) { 1f }
            val delta = ratio - prevRatio
            prevWeights[i] = ratio

            barPaint.color =
                when {
                    delta > 0.05f ->
                        Color.rgb(46, 204, 113)  // 涨了=红
                    delta < -0.05f ->
                        Color.rgb(46, 204, 113)  // 跌了=绿
                    ratio > 1.3f ->
                        Color.rgb(46, 204, 113)
                    ratio > 1.1f ->
                        Color.rgb(241, 196, 15)
                    ratio < 0.8f ->
                        Color.rgb(52, 152, 219)
                    else ->
                        Color.rgb(46, 204, 113
                        )
                }

            c.drawRect(
                x + 3f,
                top + h - barH,
                x + barW - 8f,
                top + h,
                barPaint
            )

            text.textAlign =
                Paint.Align.CENTER

            text.textSize =
                12f

            text.color =
                Color.LTGRAY

            c.drawText(
                name,
                x +
                    (
                        barW - 5f
                        ) / 2f,
                top + h + 15f,
                text
            )

            text.color =
                Color.WHITE

            c.drawText(
                "${(values[i] * 100f).toInt()}%",
                x +
                    (
                        barW - 5f
                        ) / 2f,
                top + h + 30f,
                text
            )
        }

        text.textAlign =
            Paint.Align.LEFT
    }

    private fun drawLearningCurve(
        c: Canvas,
        left: Float,
        top: Float,
        w: Float,
        h: Float
    ) {
        barPaint.style =
            Paint.Style.FILL

        barPaint.color =
            Color.rgb(
                25,
                25,
                25
            )

        c.drawRect(
            left,
            top,
            left + w,
            top + h,
            barPaint
        )

        if (recentScores.size < 2) {
            text.textAlign =
                Paint.Align.CENTER

            text.textSize =
                13f

            text.color =
                Color.GRAY

            c.drawText(
                "数据不足",
                left + w / 2f,
                top + h / 2f,
                text
            )

            text.textAlign =
                Paint.Align.LEFT

            return
        }

        val scores =
            recentScores.toList()

        val maxScore =
            scores.max()
                .coerceAtLeast(1)

        val stepX =
            w /
                (
                    scores.size - 1
                ).coerceAtLeast(1)

        val areaPath =
            Path()

        areaPath.moveTo(
            left,
            top + h
        )

        scores.forEachIndexed {
                i,
                s ->
            areaPath.lineTo(
                left +
                    i * stepX,
                top +
                    h -
                    h *
                    (
                        s.toFloat() /
                            maxScore
                        )
            )
        }

        areaPath.lineTo(
            left + w,
            top + h
        )

        areaPath.close()

        barPaint.color =
            Color.argb(
                60,
                120,
                255,
                180
            )

        c.drawPath(
            areaPath,
            barPaint
        )

        val linePath =
            Path()

        scores.forEachIndexed {
                i,
                s ->
            val x =
                left +
                    i * stepX

            val y =
                top +
                    h -
                    h *
                    (
                        s.toFloat() /
                            maxScore
                        )

            if (i == 0) {
                linePath.moveTo(
                    x,
                    y
                )
            } else {
                linePath.lineTo(
                    x,
                    y
                )
            }
        }

        val curvePaint =
            Paint(
                Paint.ANTI_ALIAS_FLAG
            )

        curvePaint.style =
            Paint.Style.STROKE

        curvePaint.strokeWidth =
            3f

        curvePaint.color =
            Color.rgb(
                120,
                255,
                180
            )

        c.drawPath(
            linePath,
            curvePaint
        )

        text.textSize =
            12f

        text.color =
            Color.LTGRAY

        c.drawText(
            "max $maxScore",
            left + 5f,
            top + 14f,
            text
        )
    }

    private fun drawDeathPie(
        c: Canvas,
        cx: Float,
        cy: Float,
        r: Float
    ) {
        val totalD =
            deathWall +
                deathSelf +
                deathTrap

        barPaint.style =
            Paint.Style.FILL

        if (totalD == 0) {
            barPaint.color =
                Color.rgb(
                    60,
                    60,
                    60
                )

            c.drawCircle(
                cx,
                cy,
                r,
                barPaint
            )

            return
        }

        val oval =
            RectF(
                cx - r,
                cy - r,
                cx + r,
                cy + r
            )

        var start =
            -90f

        val sweepW =
            360f *
                deathWall /
                totalD

        if (sweepW > 0f) {
            barPaint.color =
                Color.rgb(
                    255,
                    100,
                    100
                )

            c.drawArc(
                oval,
                start,
                sweepW,
                true,
                barPaint
            )

            start += sweepW
        }

        val sweepS =
            360f *
                deathSelf /
                totalD

        if (sweepS > 0f) {
            barPaint.color =
                Color.rgb(
                    100,
                    150,
                    255
                )

            c.drawArc(
                oval,
                start,
                sweepS,
                true,
                barPaint
            )

            start += sweepS
        }

        val sweepT =
            360f *
                deathTrap /
                totalD

        if (sweepT > 0f) {
            barPaint.color =
                Color.rgb(
                    255,
                    200,
                    100
                )

            c.drawArc(
                oval,
                start,
                sweepT,
                true,
                barPaint
            )
        }
    }

    private fun drawQHeatmap(
        c: Canvas,
        left: Float,
        top: Float,
        w: Float,
        h: Float
    ) {
        val grid = 10
        val cellW = w / grid
        val cellH = h / grid

        barPaint.style = Paint.Style.FILL
        barPaint.color = Color.rgb(35, 35, 35)
        c.drawRect(left, top, left + w, top + h, barPaint)

        val sampleList = visitedStates.take(100)
        var maxAbs = 0.001f
        for (s in sampleList) {
            for (a in 0 until 4) {
                val qv = 0f
                if (abs(qv) > maxAbs) maxAbs = abs(qv)
            }
        }

        for (i in 0 until 100) {
            val px = left + (i % grid) * cellW
            val py = top + (i / grid) * cellH

            if (i >= sampleList.size) {
                barPaint.color = Color.rgb(30, 30, 35)
            } else {
                val s = sampleList[i]
                var bestQ = -Float.MAX_VALUE
                for (a in 0 until 4) {
                    val qv = 0f
                    if (qv > bestQ) bestQ = qv
                }
                val t = (bestQ / maxAbs).coerceIn(-1f, 1f)
                barPaint.color = if (t >= 0f) {
                    Color.rgb(
                        (60 * (1f - t)).toInt(),
                        (60 + 195 * t).toInt(),
                        60
                    )
                } else {
                    val nt = -t
                    Color.rgb(
                        (60 + 195 * nt).toInt(),
                        (60 * (1f - nt)).toInt(),
                        (60 * (1f - nt)).toInt()
                    )
                }
            }
            c.drawRect(px, py, px + cellW - 1f, py + cellH - 1f, barPaint)
        }
    }

    private fun drawDebug(
        c: Canvas
    ) {
        if (
            aiMode == 0 &&
            !reinforceTraining
        ) {
            return
        }

        val w =
            min(
                width * 0.97f,
                720f
            )

        val h = 760f

        val left =
            (width - w) / 2f

        val top =
            max(
                12f,
                height - h - 12f
            )

        panel.color =
            Color.argb(
                232,
                0,
                0,
                0
            )

        c.drawRoundRect(
            left,
            top,
            left + w,
            top + h,
            22f,
            22f,
            panel
        )

        border.color =
            Color.argb(
                60,
                46,
                204,
                113
            )

        border.style =
            Paint.Style.STROKE

        border.strokeWidth =
            1.5f

        c.drawRoundRect(
            left,
            top,
            left + w,
            top + h,
            22f,
            22f,
            border
        )

        text.textAlign =
            Paint.Align.LEFT

        text.isFakeBoldText =
            true

        text.textSize =
            26f

        text.color =
            Color.WHITE

        c.drawText(
            if (reinforceTraining)
                "混合进化中 · 世代 $generation"
            else
                ai.strategy,
            left + 16f,
            top + 36f,
            text
        )

        text.isFakeBoldText =
            false

        text.textSize =
            14f

        text.color =
            Color.YELLOW

        c.drawText(
            if (reinforceTraining) {
                "规则过滤 + Q表 + 神经网络 自我迭代"
            } else {
                ai.reason
            },
            left + 16f,
            top + 58f,
            text
        )

        val gaugeCX =
            left + 58f

        val gaugeCY =
            top + 116f

        if (reinforceTraining) {
            // 训练模式：圆环显示进化进度
            val progRatio = currentAgentIndex.toFloat() / POPULATION_SIZE
            val arcPaint = Paint(Paint.ANTI_ALIAS_FLAG)
            arcPaint.style = Paint.Style.STROKE
            arcPaint.strokeWidth = 13f
            arcPaint.strokeCap = Paint.Cap.ROUND
            val oval = RectF(gaugeCX - 42f, gaugeCY - 42f, gaugeCX + 42f, gaugeCY + 42f)
            arcPaint.color = Color.rgb(50, 50, 50)
            c.drawArc(oval, -90f, 360f, false, arcPaint)
            arcPaint.color = Color.rgb(46, 204, 113)
            c.drawArc(oval, -90f, 360f * progRatio, false, arcPaint)

            text.textAlign = Paint.Align.CENTER
            text.isFakeBoldText = true
            text.textSize = 22f
            text.color = Color.WHITE
            c.drawText("$generation", gaugeCX, gaugeCY + 8f, text)
            text.isFakeBoldText = false
            text.textSize = 11f
            text.color = Color.LTGRAY
            c.drawText("世代", gaugeCX, gaugeCY + 28f, text)
        } else {
            drawDangerGauge(
                c,
                gaugeCX,
                gaugeCY,
                42f,
                ai.danger
            )
            text.textAlign = Paint.Align.CENTER
            text.isFakeBoldText = true
            text.textSize = 26f
            text.color = Color.WHITE
            c.drawText("${ai.danger}", gaugeCX, gaugeCY + 9f, text)
            text.isFakeBoldText = false
            text.textSize = 12f
            text.color = Color.LTGRAY
            c.drawText("危险", gaugeCX, gaugeCY + 28f, text)
        }

        text.textAlign =
            Paint.Align.LEFT

        text.textSize =
            16f

        text.color =
            Color.WHITE

        c.drawText(
            "局数 $totalGames",
            left + 118f,
            top + 86f,
            text
        )

        val avg =
            if (recentScores.isEmpty()) {
                0f
            } else {
                recentScores
                    .average()
                    .toFloat()
            }

        c.drawText(
            "近50均分 ${
                "%.0f".format(avg)
            }   最佳 $bestRecentScore",
            left + 118f,
            top + 110f,
            text
        )

        val threadInfo =
            if (reinforceTraining) {
                "${trainThreads.size} 线程"
            } else {
                "单局"
            }

        c.drawText(
            "模式 $threadInfo   主蛇长 ${snake.size}   Q覆盖${visitedStates.size}",
            left + 118f,
            top + 134f,
            text
        )

        // 训练数据条（Q覆盖/回放/ε/Q-NN权重）
        if (reinforceTraining) {
            barPaint.style = Paint.Style.FILL
            var meterY = top + 155f
            val meterW = w - 32f

            // V3 Agent进度
            text.textSize = 9f
            text.color = Color.rgb(200, 180, 255)
            c.drawText("Agent ${completedAgents}/$POPULATION_SIZE", left + 16f, meterY + 8f, text)
            barPaint.color = Color.rgb(30, 30, 40)
            c.drawRoundRect(left + 16f, meterY + 12f, left + 16f + meterW, meterY + 19f, 3f, 3f, barPaint)
            barPaint.color = Color.rgb(200, 150, 255)
            val agR = (completedAgents.toFloat() / POPULATION_SIZE).coerceIn(0f, 1f)
            c.drawRoundRect(left + 16f, meterY + 12f, left + 16f + meterW * agR, meterY + 19f, 3f, 3f, barPaint)
            meterY += 24f

            // V3 Fallback
            text.color = Color.rgb(100, 220, 255)
            c.drawText("V3 Fallback $v3FallbackCount", left + 16f, meterY + 8f, text)
            barPaint.color = Color.rgb(30, 30, 40)
            c.drawRoundRect(left + 16f, meterY + 12f, left + 16f + meterW, meterY + 19f, 3f, 3f, barPaint)
            barPaint.color = Color.rgb(100, 200, 255)
            val fbR = (v3FallbackCount.toFloat() / (v3FallbackCount + v3ExceptionCount + 1)).coerceIn(0f, 1f)
            c.drawRoundRect(left + 16f, meterY + 12f, left + 16f + meterW * fbR, meterY + 19f, 3f, 3f, barPaint)
            meterY += 24f

            // V3 Exception
            text.color = Color.rgb(241, 196, 15)
            c.drawText("Exception $v3ExceptionCount", left + 16f, meterY + 8f, text)
            barPaint.color = Color.rgb(30, 30, 40)
            c.drawRoundRect(left + 16f, meterY + 12f, left + 16f + meterW, meterY + 19f, 3f, 3f, barPaint)
            barPaint.color = Color.rgb(231, 76, 60)
            val exR = (v3ExceptionCount.toFloat() / (v3FallbackCount + v3ExceptionCount + 1)).coerceIn(0f, 1f)
            c.drawRoundRect(left + 16f, meterY + 12f, left + 16f + meterW * exR, meterY + 19f, 3f, 3f, barPaint)
            meterY += 24f

            // Q/NN权重条
            text.color = Color.rgb(200, 200, 200)
            c.drawText("V3 Gen $generation", left + 16f, meterY + 8f, text)
            barPaint.color = Color.rgb(30, 30, 40)
            c.drawRoundRect(left + 16f, meterY + 12f, left + 16f + meterW, meterY + 19f, 3f, 3f, barPaint)
            barPaint.color = Color.rgb(231, 76, 60)
            c.drawRoundRect(left + 16f, meterY + 12f, left + 16f + meterW * 1.0f, meterY + 19f, 3f, 3f, barPaint)
            barPaint.color = Color.rgb(46, 204, 113)
            c.drawRoundRect(left + 16f + meterW * 1.0f, meterY + 12f, left + 16f + meterW, meterY + 19f, 3f, 3f, barPaint)
        }

        val wbY =
            top + 250f

        text.isFakeBoldText =
            true

        text.textSize =
            14f

        text.color =
            Color.rgb(
                255,
                200,
                100
            )

        c.drawText(
            "【权重柱状图】",
            left + 16f,
            wbY,
            text
        )

        text.isFakeBoldText =
            false

        drawWeightBars(
            c,
            left + 16f,
            wbY + 8f,
            w - 32f,
            66f
        )

        val learnY =
            top + 290f

        text.isFakeBoldText =
            true

        text.textSize =
            14f

        text.color =
            Color.rgb(
                255,
                150,
                255
            )

        c.drawText(
            "【V2学习】",
            left + 16f,
            learnY,
            text
        )

        text.isFakeBoldText =
            false

        text.color =
            Color.WHITE

        c.drawText(
            "训练中",
            left + 118f,
            learnY,
            text
        )

        val barStartX =
            left + 118f

        val barEndX =
            left + w - 16f

        val barW =
            barEndX - barStartX

        var barY =
            top + 318f

        if (!reinforceTraining) {
            text.isFakeBoldText =
                true

            text.textSize =
                14f

            text.color =
                Color.rgb(
                    255,
                    200,
                    100
                )

            c.drawText(
                "【四方向安全 / Q】",
                left + 16f,
                barY,
                text
            )

            text.isFakeBoldText =
                false

            barY += 10f

            val dirNames =
                listOf(
                    "UP",
                    "DN",
                    "LF",
                    "RT"
                )

            ai.candidates
                .forEachIndexed {
                    idx,
                    cand ->
                    text.textSize =
                        18f

                    text.color =
                        if (!cand.legal) {
                            Color.GRAY
                        } else if (
                            cand.d ==
                            ai.chosen
                        ) {
                            Color.CYAN
                        } else {
                            Color.WHITE
                        }

                    c.drawText(
                        dirNames[idx],
                        left + 16f,
                        barY + 19f,
                        text
                    )

                    if (!cand.legal) {
                        text.textSize =
                            14f

                        text.color =
                            Color.GRAY

                        c.drawText(
                            "非法",
                            barStartX,
                            barY + 19f,
                            text
                        )
                    } else {
                        val regionRatio =
                            if (snake.isNotEmpty()) {
                                cand.region.toFloat() /
                                    snake.size
                            } else {
                                0f
                            }

                        val safeScore =
                            when {
                                cand.tailOk &&
                                    regionRatio >= 1.5f ->
                                    1.0f

                                cand.tailOk &&
                                    regionRatio >= 1.0f ->
                                    0.75f

                                regionRatio >= 1.0f ->
                                    0.5f

                                regionRatio >= 0.6f ->
                                    0.3f

                                else ->
                                    0.15f
                            }

                        barPaint.color =
                            Color.rgb(
                                40,
                                40,
                                40
                            )

                        barPaint.style =
                            Paint.Style.FILL

                        c.drawRoundRect(
                            barStartX,
                            barY,
                            barEndX,
                            barY + 24f,
                            4f,
                            4f,
                            barPaint
                        )

                        val barColor =
                            when {
                                safeScore >= 0.9f ->
                                    Color.rgb(
                                        46,
                                        204,
                                        113
                                    )

                                safeScore >= 0.7f ->
                                    Color.rgb(
                                        241,
                                        196,
                                        15
                                    )

                                safeScore >= 0.5f ->
                                    Color.rgb(
                                        230,
                                        126,
                                        34
                                    )

                                else ->
                                    Color.rgb(
                                        231,
                                        76,
                                        60
                                    )
                            }

                        barPaint.color =
                            barColor

                        c.drawRoundRect(
                            barStartX,
                            barY,
                            barStartX +
                                barW *
                                safeScore,
                            barY + 24f,
                            4f,
                            4f,
                            barPaint
                        )

                        text.textSize =
                            13f

                        text.color =
                            Color.WHITE

                        c.drawText(
                            "空间${cand.region} 尾${
                                if (cand.tailOk) "Y"
                                else "N"
                            } 食${
                                if (cand.foodDist < 0)
                                    "∞"
                                else
                                    cand.foodDist
                            } Q${
                                "%.2f".format(
                                    cand.qValue
                                )
                            }",
                            barStartX + 8f,
                            barY + 18f,
                            text
                        )
                    }

                    barY += 28f
                }
        } else {
            barY =
                top + 318f
        }

        val chartY =
            barY + 20f

        val chartH =
            72f

        val curveX =
            left + 16f

        val curveW =
            (w - 32f) * 0.55f

        text.isFakeBoldText =
            true

        text.textSize =
            14f

        text.color =
            Color.rgb(
                120,
                255,
                180
            )

        c.drawText(
            "【历史分数】",
            curveX,
            chartY,
            text
        )

        text.isFakeBoldText =
            false

        drawLearningCurve(
            c,
            curveX,
            chartY + 8f,
            curveW,
            chartH
        )

        val pieCX =
            left + w - 130f

        val pieCY =
            chartY +
                chartH / 2f +
                14f

        val pieR =
            34f

        text.isFakeBoldText =
            true

        text.textSize =
            14f

        text.color =
            Color.rgb(
                255,
                150,
                150
            )

        c.drawText(
            "【死亡统计】",
            pieCX - 52f,
            chartY,
            text
        )

        text.isFakeBoldText =
            false

        drawDeathPie(
            c,
            pieCX,
            pieCY,
            pieR
        )

        text.textSize =
            13f

        text.color =
            Color.rgb(
                255,
                100,
                100
            )

        c.drawText(
            "W $deathWall",
            pieCX + 42f,
            pieCY - 16f,
            text
        )

        text.color =
            Color.rgb(
                100,
                150,
                255
            )

        c.drawText(
            "S $deathSelf",
            pieCX + 42f,
            pieCY + 4f,
            text
        )

        text.color =
            Color.rgb(
                255,
                200,
                100
            )

        c.drawText(
            "T $deathTrap",
            pieCX + 42f,
            pieCY + 24f,
            text
        )

        val heatY =
            chartY +
                chartH +
                30f

        text.textAlign =
            Paint.Align.LEFT

        text.isFakeBoldText =
            true

        text.textSize =
            14f

        text.color =
            Color.rgb(
                200,
                180,
                255
            )

        c.drawText(
            "【V2 Q表热度】",
            left + 16f,
            heatY,
            text
        )

        text.isFakeBoldText =
            false

        drawQHeatmap(
            c,
            left + 16f,
            heatY + 8f,
            w - 32f,
            66f
        )

        val infoY =
            heatY +
                8f +
                66f +
                22f

        var visited =
            0

        var sumQ =
            0f

        var cntQ =
            0

        val sampleStep =
            max(
                1,
                V2_STATE_COUNT /
                    400
            )

        val avgQ = 0f
            } else {
                0f
            }

        text.textSize =
            14f

        text.color =
            Color.WHITE

        text.textAlign =
            Paint.Align.LEFT

        if (reinforceTraining) {
            c.drawText(
                "世代 $generation   当前个体 $currentAgentIndex/$POPULATION_SIZE   Q覆盖${visitedStates.size}",
                left + 16f,
                infoY,
                text
            )
            c.drawText(
                "本代最佳 ${"%.0f".format(0f)}   历史最佳 ${"%.0f".format(0f)}",
                left + 16f,
                infoY + 18f,
                text
            )
            c.drawText(
                "Q表权重 ${"%.2f".format(1.0f)}   神经网络权重 ${"%.2f".format(0.0f)}",
                left + 16f,
                infoY + 36f,
                text
            )
            c.drawText(
                "回放${replayBuffer.size}/${REPLAY_CAPACITY}   ε${"%.2f".format(v2Epsilon)}   步${v2LearningSteps}",
                left + 16f,
                infoY + 54f,
                text
            )
            val learnStatus = when {
                generation < 3 -> "🧬 初始化种群，随机试错中..."
                v2Epsilon > 0.15f -> "🔍 探索阶段：尝试新策略"
                v2Epsilon < 0.05f && 0.0f > 0.5f -> "🧠 收敛阶段：神经网络主导"
                0f > 0f * 0.95f && 0f > 0 -> "🚀 突破中！分数上升"
                0f < 0f * 0.3f && 0f > 1000 -> "⚡ 瓶颈期，等待变异突破"
                else -> "📊 正常进化中..."
            }
            text.textSize = 13f
            text.isFakeBoldText = true
            text.color = Color.rgb(100, 220, 255)
            c.drawText(learnStatus, left + 16f, infoY + 74f, text)

            // 死局预判指示器
            if (deadEndPredicted) {
                text.color = Color.rgb(255, 80, 80)
                c.drawText("⚠️ 死局预判！食物周围空间仅 ${"%.1f".format(foodSpaceRatio)}x 蛇长", left + 16f, infoY + 94f, text)
            } else {
                text.color = Color.rgb(80, 200, 120)
                c.drawText("✅ 食物空间 ${"%.1f".format(foodSpaceRatio)}x 蛇长", left + 16f, infoY + 94f, text)
            }
            text.color = if (rolloutActive) Color.rgb(180, 180, 255) else Color.rgb(100, 100, 120)
            c.drawText(if (rolloutActive) "🔮 前瞻模拟${rolloutSteps}步（蛇长${snake.size}）" else "🔮 前瞻模拟：蛇短不启用", left + 16f, infoY + 112f, text)
            text.isFakeBoldText = false
            text.color = Color.WHITE
            text.textSize = 14f
        } else {
            c.drawText(
                "局数 $totalGames   近50均分 ${
                    "%.0f".format(avg)
                }   最佳 $bestRecentScore",
                left + 16f,
                infoY,
                text
            )

            c.drawText(
                "V2覆盖 ${
                    visited
                }   平均Q ${
                    "%.2f".format(avgQ)
                }   学习步 ${
                    v2LearningSteps
                }",
                left + 16f,
                infoY + 18f,
                text
            )

            c.drawText(
                "ε ${
                    "%.3f".format(
                        v2Epsilon
                    )
                }   攻击x${
                    "%.2f".format(
                        aggression
                    )
                }   安全x${
                    "%.2f".format(
                        safetyMargin
                    )
                }",
                left + 16f,
                infoY + 36f,
                text
            )
        }

        if (
            gameOver &&
            !reinforceTraining
        ) {
            text.color =
                Color.RED

            text.isFakeBoldText =
                true

            text.textSize =
                16f

            c.drawText(
                "死亡原因：$deathCause",
                left + 16f,
                infoY + 62f,
                text
            )

            text.isFakeBoldText =
                false
        }

        val btnW =
            160f

        val btnH =
            42f

        val btnLeft =
            left +
                w -
                btnW -
                16f

        val btnTop =
            infoY + 48f

        reinforceButtonRect.set(
            btnLeft,
            btnTop,
            btnLeft + btnW,
            btnTop + btnH
        )

        val btnColor =
            if (reinforceTraining) {
                Color.rgb(
                    231,
                    76,
                    60
                )
            } else {
                Color.rgb(
                    46,
                    204,
                    113
                )
            }

        panel.color =
            btnColor

        c.drawRoundRect(
            reinforceButtonRect,
            12f,
            12f,
            panel
        )

        text.textAlign =
            Paint.Align.CENTER

        text.isFakeBoldText =
            true

        text.textSize =
            18f

        text.color =
            Color.WHITE

        c.drawText(
            if (reinforceTraining)
                "停止进化"
            else
                "神经进化",
            reinforceButtonRect.centerX(),
            reinforceButtonRect.centerY() + 7f,
            text
        )

        text.isFakeBoldText =
            false

        text.textAlign =
            Paint.Align.LEFT
    }

    private fun drawGameOver(
        c: Canvas
    ) {
        paint.color =
            Color.argb(
                150,
                0,
                0,
                0
            )

        c.drawRect(
            0f,
            0f,
            width.toFloat(),
            height.toFloat(),
            paint
        )

        text.textAlign =
            Paint.Align.CENTER

        text.isFakeBoldText =
            true

        text.textSize =
            30f

        text.color =
            Color.WHITE

        c.drawText(
            "GAME OVER",
            width / 2f,
            height / 2f - 45,
            text
        )

        text.textSize =
            15f

        text.isFakeBoldText =
            false

        c.drawText(
            "分数 $score   最高 $highScore   长度 ${snake.size}",
            width / 2f,
            height / 2f - 15,
            text
        )

        text.color =
            Color.YELLOW

        c.drawText(
            "点击屏幕重新开始",
            width / 2f,
            height / 2f + 20,
            text
        )

        text.color =
            Color.LTGRAY

        text.textSize =
            11f

        c.drawText(
            lastDeathInfo,
            width / 2f,
            height / 2f + 48,
            text
        )
    }

    /*
     * =========================
     * TOUCH
     * =========================
     */

    private var touchStartX = 0f
    private var touchStartY = 0f

    override fun onTouchEvent(
        e: MotionEvent
    ): Boolean {
        when (e.action) {
            MotionEvent.ACTION_DOWN -> {
                touchStartX = e.x
                touchStartY = e.y
                return true
            }

            MotionEvent.ACTION_UP,
            MotionEvent.ACTION_CANCEL -> {
                if (
                    reinforceButtonRect
                        .contains(
                            e.x,
                            e.y
                        )
                ) {
                    val now =
                        System.currentTimeMillis()

                    if (
                        now -
                            lastReinforceTap >
                        400L
                    ) {
                        lastReinforceTap =
                            now

                        setReinforceTraining(
                            !reinforceTraining
                        )
                    }

                    return true
                }

                if (reinforceTraining) {
                    return true
                }

                if (gameOver) {
                    reset()
                    return true
                }

                if (aiMode != 0) {
                    return true
                }

                if (snake.isEmpty()) {
                    return true
                }

                val dx =
                    e.x -
                        touchStartX

                val dy =
                    e.y -
                        touchStartY

                val useSwipe =
                    abs(dx) > 24f ||
                        abs(dy) > 24f

                val d =
                    if (useSwipe) {
                        if (
                            abs(dx) >
                            abs(dy)
                        ) {
                            P(
                                if (dx > 0) 1
                                else -1,
                                0
                            )
                        } else {
                            P(
                                0,
                                if (dy > 0) 1
                                else -1
                            )
                        }
                    } else {
                        val hx =
                            ox +
                                (
                                    snake.first().x +
                                        0.5f
                                    ) * cell

                        val hy =
                            oy +
                                (
                                    snake.first().y +
                                        0.5f
                                    ) * cell

                        val rdx =
                            e.x - hx

                        val rdy =
                            e.y - hy

                        if (
                            abs(rdx) >
                            abs(rdy)
                        ) {
                            P(
                                if (rdx > 0) 1
                                else -1,
                                0
                            )
                        } else {
                            P(
                                0,
                                if (rdy > 0) 1
                                else -1
                            )
                        }
                    }

                if (!isReverse(d, dir)) {
                    queue.clear()
                    queue.add(d)
                }

                return true
            }

            else ->
                return true
        }
    }

    override fun onDetachedFromWindow() {
        stopParallelTraining()
        super.onDetachedFromWindow()
        bgm?.stop()
        try { toneGen?.release() } catch (_: Throwable) {}
        try { aiPool.shutdownNow() } catch (_: Throwable) {}
        saveTrainingState()
    }

    /*
     * ============================================================
     * TRAINING GAME
     * ============================================================
     */

    private inner class TrainGame(
        seed: Long,
        private val runId: Long,
        val v3: AIEngineV3
    ) {
        val rng =
            Random(seed)

        var v3Active = false
        var gFoodEaten = 0
        private var gPrevHashes = LongArray(0)

        val gSnake =
            ArrayDeque<P>()

        var gDir =
            P(1, 0)

        var gFood =
            P(7, 7)

        var gScore =
            0

        var gHunger =
            0

        var gLastFreeRegion = 0f

        var gCombo =
            0

        var gSteps =
            0

        var gOver =
            false

        var lastDeathCause =
            "UNKNOWN"

        val vis =
            BooleanArray(total)

        val que =
            IntArray(total + 4)

        val par =
            IntArray(total)

        val parDir =
            arrayOfNulls<P>(total)

        private var prevState =
            -1

        private var prevAction =
            -1

        private var currentAgentId = 0

        fun playOneGame(agentId: Int): V3AgentResult {
            currentAgentId = agentId
            gSnake.clear()

            gSnake.add(P(7, 7))
            gSnake.add(P(6, 7))
            gSnake.add(P(5, 7))

            gDir = P(1, 0)

            gScore = 0
            gFoodEaten = 0
            gHunger = 0
            gCombo = 0
            gSteps = 0
            gOver = false

            prevState = -1
            prevAction = -1
            lastDeathCause = "UNKNOWN"
            gPrevHashes = LongArray(0)
            gLastFreeRegion = gFreeRegion(gSnake).toFloat()

            v3.resetEpisode()
            v3.setTraining(true)
            v3.setGeneration(generation)

            gPlaceFood()

            var iter = 0

            while (
                !gOver &&
                isTrainingRunActive(runId) &&
                !Thread.currentThread().isInterrupted &&
                iter < 30000
            ) {
                gStep()
                iter++
            }

            if (isTrainingRunActive(runId) && !gOver) {
                lastDeathCause = "TIMEOUT"
                gOver = true
                gDie(lastDeathCause)
            } else if (gOver && isTrainingRunActive(runId)) {
                gDie(lastDeathCause)
            }

            val reason = when (lastDeathCause) {
                "WALL" -> V3DeathReason.HIT_WALL
                "SELF" -> V3DeathReason.HIT_SELF
                "TRAP" -> V3DeathReason.TRAPPED
                "HUNGER" -> V3DeathReason.HUNGER
                "TIMEOUT" -> V3DeathReason.LOOP
                else -> V3DeathReason.UNKNOWN
            }

            val fit = V3EvolutionManager.fitness(
                score = gScore, food = gFoodEaten,
                survivalSteps = gSteps, length = gSnake.size, deathReason = reason
            )

            return V3AgentResult(agent = v3, fitness = fit, score = gScore, food = gFoodEaten, survivalSteps = gSteps, deathReason = reason)
        }

        fun gPlaceFood() {
            val free =
                ArrayList<P>(
                    total
                )

            for (x in 0 until cols) {
                for (y in 0 until rows) {
                    val p =
                        P(x, y)

                    if (!gSnake.contains(p)) {
                        free.add(p)
                    }
                }
            }

            if (free.isNotEmpty()) {
                gFood =
                    free[
                        rng.nextInt(
                            free.size
                        )
                    ]
            }
        }

        fun gStep() {
            val state =
                gBuildState()

            val mv =
                gChooseMove(
                    state
                )

            val action =
                dirs.indexOfFirst {
                    it == mv
                }.coerceAtLeast(0)

            val prevScore = gScore

            if (
                !gIsReverse(
                    mv,
                    gDir
                )
            ) {
                gDir = mv
            }

            val nh =
                P(
                    gSnake.first().x +
                        gDir.x,
                    gSnake.first().y +
                        gDir.y
                )

            fun v3Feedback(died: Boolean) {
                try {
                    val bodyArr = IntArray(gSnake.size)
                    for (i in gSnake.indices) {
                        val p = gSnake.elementAt(i)
                        bodyArr[i] = p.y * cols + p.x
                    }
                    val dirV3 = when {
                        gDir.x == 1 -> V3Action.RIGHT
                        gDir.x == -1 -> V3Action.LEFT
                        gDir.y == -1 -> V3Action.UP
                        else -> V3Action.DOWN
                    }
                    val next = V3State(
                        width = cols, height = rows,
                        body = bodyArr,
                        food = gFood.y * cols + gFood.x,
                        direction = dirV3,
                        score = gScore, steps = gSteps,
                        stepsSinceFood = gHunger,
                        hunger = gHunger.toFloat(),
                        gameOver = gOver,
                        recentHashes = (gPrevHashes + (bodyArr.contentHashCode().toLong() * 31 + gFood.y * cols + gFood.x)).takeLast(16).toLongArray()
                    )
                    gPrevHashes = next.recentHashes
                    v3.feedback(nextState = next, ateFood = gScore > prevScore, died = died)
                } catch (e: InterruptedException) {
                    throw e
                } catch (e: Throwable) {
                    v3ExceptionCount++
                    Log.e("SnakeV3", "V3 feedback error", e)
                }
            }

            if (!gInside(nh)) {
                gTerminal(
                    state,
                    action,
                    DEATH_WALL
                )

                lastDeathCause =
                    "WALL"

                gOver = true
                v3Feedback(true)
                return
            }

            val ate =
                nh == gFood

            val tail =
                gSnake.last()

            if (
                gSnake.contains(nh) &&
                !(nh == tail && !ate)
            ) {
                val testSnake =
                    ArrayDeque(
                        gSnake
                    )

                testSnake.addFirst(nh)

                if (!ate) {
                    testSnake.removeLast()
                }

                val reg =
                    gFreeRegion(
                        testSnake
                    )

                val cause =
                    if (
                        reg <
                        max(
                            2,
                            (
                                gSnake.size *
                                    safetyMargin
                                ).toInt()
                        )
                    ) {
                        "TRAP"
                    } else {
                        "SELF"
                    }

                gTerminal(
                    state,
                    action,
                    if (cause == "TRAP") {
                        DEATH_TRAP
                    } else {
                        DEATH_SELF
                    }
                )

                lastDeathCause =
                    cause

                gOver = true
                v3Feedback(true)
                return
            }

            gSnake.addFirst(nh)

            var reward =
                REWARD_STEP

            if (ate) {
                gFoodEaten++
                gScore +=
                    10 +
                        min(
                            gCombo,
                            30
                        ) * 3 +
                        gSnake.size

                gCombo++

                gHunger = 0

                gPlaceFood()

                reward +=
                    REWARD_FOOD +
                        gCombo * 0.06f
            } else {
                gSnake.removeLast()

                gHunger++

                gCombo =
                    max(
                        0,
                        gCombo - 1
                    )

                // 空间奖励改变化量
                val gCurFree = gFreeRegion(gSnake).toFloat()
                val gSpaceDelta = gCurFree - gLastFreeRegion
                gLastFreeRegion = gCurFree
                reward += gSpaceDelta * REWARD_SPACE_DELTA

                if (
                    gTailReachable(
                        gSnake
                    )
                ) {
                    reward +=
                        REWARD_TAIL
                }

                if (
                    gCalculateDanger() >= 4
                ) {
                    reward +=
                        REWARD_DANGER
                }

                // hunger惩罚与主游戏统一：平方递增
                reward += -(gHunger * gHunger * 0.001f).coerceAtMost(0.15f)
            }

            gSteps++

            if (
                gHunger >=
                hungerKillLimit
            ) {
                gTerminal(
                    state,
                    action,
                    DEATH_HUNGER
                )

                lastDeathCause =
                    "HUNGER"

                gOver = true
                v3Feedback(true)
                return
            }

            val nextState =
                gBuildState()

            val nextMask =
                gLegalMask()

            v3Feedback(false)

            prevState = nextState
            prevAction = action
        }

        private fun gTerminal(
            state: Int,
            action: Int,
            reward: Float
        ) {
            prevState = -1
            prevAction = -1
        }

        fun gChooseMove(
            state: Int
        ): P {
            v3Active = false
            // V3 决策路径
            try {
                val bodyArr = IntArray(gSnake.size)
                for (i in gSnake.indices) {
                    val p = gSnake.elementAt(i)
                    bodyArr[i] = p.y * cols + p.x
                }
                val dirV3 = when {
                    gDir.x == 1 -> V3Action.RIGHT
                    gDir.x == -1 -> V3Action.LEFT
                    gDir.y == -1 -> V3Action.UP
                    else -> V3Action.DOWN
                }
                val v3state = V3State(
                    width = cols, height = rows,
                    body = bodyArr,
                    food = gFood.y * cols + gFood.x,
                    direction = dirV3,
                    score = gScore,
                    steps = gSteps,
                    stepsSinceFood = gHunger,
                    hunger = gHunger.toFloat(),
                    gameOver = gOver
                )
                v3.setTraining(true)
                val a = v3.act(v3state)
                v3Active = true
                return when(a) {
                    V3Action.UP -> P(0, -1)
                    V3Action.RIGHT -> P(1, 0)
                    V3Action.DOWN -> P(0, 1)
                    V3Action.LEFT -> P(-1, 0)
                }
            } catch (_: Throwable) {
                v3Active = false
                v3ExceptionCount++
                Log.e("SnakeV3", "V3 chooseMove error")
            }

            val cands =
                dirs.map {
                    gEvaluate(it)
                }

            val legal =
                cands.filter {
                    it.legal
                }

            if (legal.isEmpty()) return gDir

            // V3失败：纯安全fallback，不进旧V2学习
            v3FallbackCount++
            return legal.maxByOrNull { it.region }?.d ?: gDir

            if (
                gSnake.size < 15
            ) {
                val path =
                    gShortestPath(
                        gSnake.first(),
                        gFood,
                        gSnake,
                        true
                    )

                if (
                    path != null &&
                    path.isNotEmpty()
                ) {
                    val simBody =
                        ArrayDeque(
                            gSnake
                        )

                    var ate = false
                    var valid = true

                    for (step in path) {
                        val nh =
                            P(
                                simBody.first().x +
                                    step.x,
                                simBody.first().y +
                                    step.y
                            )

                        if (!gInside(nh)) {
                            valid = false
                            break
                        }

                        val willEat =
                            nh == gFood

                        if (
                            simBody.contains(nh) &&
                            !(
                                nh ==
                                    simBody.last() &&
                                    !willEat
                                )
                        ) {
                            valid = false
                            break
                        }

                        simBody.addFirst(nh)

                        if (!willEat) {
                            simBody.removeLast()
                        } else {
                            ate = true
                        }
                    }

                    if (
                        valid &&
                        ate &&
                        gTailReachable(
                            simBody
                        )
                    ) {
                        return path.first()
                    }
                }
            }

            val safeFood =
                gFindSafeFoodStep()

            if (safeFood != null) {
                return safeFood
            }

            val tailStep =
                gFollowTailStep(
                    legal
                )

            if (
                tailStep != null &&
                gHunger <
                    gHungerForceEat()
            ) {
                return tailStep
            }

            val threshold =
                gHungerForceEat()

            if (
                gHunger >= threshold
            ) {
                val safe =
                    legal.filter {
                        it.tailOk &&
                            it.foodDist >= 0
                    }

                if (safe.isNotEmpty()) {
                    return gSelectAction(
                        state,
                        safe
                    ).d
                }
            }

            val shielded =
                legal.filter {
                    val ratio =
                        it.region.toFloat() /
                            max(
                                1,
                                gSnake.size
                            )

                    it.tailOk ||
                        ratio >= 1.0f ||
                        (
                            gSnake.size < 15 &&
                                ratio >= 0.75f
                            )
                }

            val pool =
                if (shielded.isNotEmpty()) {
                    shielded
                } else {
                    legal
                }

            return gSelectAction(
                state,
                pool
            ).d
        }

        private fun gSelectAction(
            state: Int,
            legal: List<Candidate>
        ): Candidate {
            return legal.maxByOrNull { it.region } ?: legal.first()
        }
        private fun gBuildState(): Int {
            val h =
                gSnake.first()

            return buildState(
                gSnake,
                gDir,
                gFood,
                gHunger
            )
        }

        private fun gLegalMask(): Int {
            return legalActionMask(
                gSnake,
                gDir,
                gFood
            )
        }

        fun gHungerForceEat(): Int =
            when {
                gSnake.size < 20 -> 50
                gSnake.size < 35 -> 70
                gSnake.size < 55 -> 100
                gSnake.size < 80 -> 140
                else -> 200
            }

        fun gFollowTailStep(
            legal: List<Candidate>
        ): P? {
            if (gSnake.size < 2) {
                return null
            }

            val path =
                gShortestPath(
                    gSnake.first(),
                    gSnake.last(),
                    gSnake,
                    true
                ) ?: return null

            if (path.isEmpty()) {
                return null
            }

            val step =
                path.first()

            if (
                legal.none {
                    it.d == step
                }
            ) {
                return null
            }

            val sim =
                gSimulate(step)

            if (sim.body.isEmpty()) {
                return null
            }

            if (
                !gTailReachable(
                    sim.body
                )
            ) {
                return null
            }

            return step
        }

        fun gFindSafeFoodStep(): P? {
            val path =
                gShortestPath(
                    gSnake.first(),
                    gFood,
                    gSnake,
                    true
                ) ?: return null

            if (path.isEmpty()) {
                return null
            }

            val simBody =
                ArrayDeque(
                    gSnake
                )

            var ate = false

            for (step in path) {
                val nh =
                    P(
                        simBody.first().x +
                            step.x,
                        simBody.first().y +
                            step.y
                    )

                if (!gInside(nh)) {
                    return null
                }

                val willEat =
                    nh == gFood

                if (
                    simBody.contains(nh) &&
                    !(nh == simBody.last() && !willEat)
                ) {
                    return null
                }

                simBody.addFirst(nh)

                if (!willEat) {
                    simBody.removeLast()
                } else {
                    ate = true
                }
            }

            if (!ate) {
                return null
            }

            if (
                !gTailReachable(
                    simBody
                )
            ) {
                return null
            }

            val len =
                simBody.size

            val freeLeft =
                total - len

            if (
                len > 180 &&
                freeLeft < 4
            ) {
                return null
            }

            if (
                len > 150 &&
                freeLeft < 6
            ) {
                return null
            }

            if (
                len > 120 &&
                freeLeft < 10
            ) {
                return null
            }

            if (
                len > 90 &&
                freeLeft < 14
            ) {
                return null
            }

            if (
                len > 60 &&
                freeLeft < 20
            ) {
                return null
            }

            return path.first()
        }

        fun gBestSurvival(
            legal: List<Candidate>
        ): Candidate {
            var best =
                legal.first()

            var bestScore =
                -1e30f

            for (cand in legal) {
                val sim =
                    gSimulate(
                        cand.d
                    )

                if (sim.body.isEmpty()) {
                    continue
                }

                val r =
                    gFreeRegion(
                        sim.body
                    )

                val t =
                    gTailReachable(
                        sim.body
                    )

                val mob =
                    gCountSafeMoves(
                        sim.body
                    )

                var sc = 0f

                if (t) {
                    sc += 50000f
                } else {
                    sc -= 200000f
                    continue
                }

                sc +=
                    r * 250f

                sc +=
                    mob * 500f

                val fd =
                    gDistance(
                        sim.body.first(),
                        gFood,
                        sim.body,
                        true
                    )

                if (fd >= 0) {
                    sc +=
                        500f /
                            (fd + 1)
                }

                if (sim.ate) {
                    sc += 5000f
                }

                if (
                    sc >
                    bestScore
                ) {
                    bestScore = sc
                    best = cand
                }
            }

            return best
        }

        fun gEvaluate(
            d: P
        ): Candidate {
            if (
                !gLegalDirection(d)
            ) {
                return Candidate(
                    d,
                    -1e9f,
                    "非法",
                    false
                )
            }

            val sim =
                gSimulate(d)

            if (sim.body.isEmpty()) {
                return Candidate(
                    d,
                    -1e9f,
                    "非法",
                    false
                )
            }

            val region =
                gFreeRegion(
                    sim.body
                )

            val tail =
                gTailReachable(
                    sim.body
                )

            val foodDist =
                gDistance(
                    sim.body.first(),
                    gFood,
                    sim.body,
                    true
                )

            val ate =
                sim.ate

            val mobility =
                gCountSafeMoves(
                    sim.body
                )

            val hungerFactor =
                when {
                    gHunger >= 60 -> 4f
                    gHunger >= 30 -> 2.5f
                    gHunger >= 15 -> 1.6f
                    else -> 1f
                }

            val regionScore =
                region * wRegion

            val mobilityScore =
                mobility *
                    wMobility

            val tailScore =
                if (tail) {
                    wTailGood
                } else {
                    wTailBad
                }

            var foodScore =
                if (foodDist >= 0) {
                    hungerFactor *
                        aggression *
                        (
                            wFoodNear /
                                (
                                    foodDist + 1
                                    )
                            )
                } else {
                    -450f *
                        hungerFactor
                }

            if (ate) {
                foodScore +=
                    wFoodAte *
                        aggression
            }

            var eatPenalty = 0f

            if (ate) {
                val afterSize =
                    sim.body.size

                val needSpace =
                    (
                        afterSize *
                            safetyMargin
                        ).toInt() + 2

                if (
                    !tail ||
                    region < needSpace
                ) {
                    eatPenalty =
                        -2500f -
                            gSnake.size *
                            35f
                }
            }

            val edge =
                min(
                    min(
                        sim.body.first().x,
                        cols - 1 -
                            sim.body.first().x
                    ),
                    min(
                        sim.body.first().y,
                        rows - 1 -
                            sim.body.first().y
                    )
                )

            val edgeScore =
                -max(
                    0,
                    2 - edge
                ) * wEdge

            val spacePenalty =
                max(
                    0f,
                    gSnake.size *
                        safetyMargin -
                        region.toFloat()
                )

            val spaceScore =
                -spacePenalty *
                    wSpace

            val totalScore =
                regionScore +
                    mobilityScore +
                    tailScore +
                    foodScore +
                    edgeScore +
                    spaceScore +
                    eatPenalty

            return Candidate(
                d,
                totalScore,
                "",
                true,
                regionScore = regionScore,
                mobilityScore = mobilityScore,
                tailScore = tailScore,
                foodScore = foodScore,
                edgeScore = edgeScore,
                spaceScore = spaceScore,
                region = region,
                mobility = mobility,
                tailOk = tail,
                foodDist = foodDist,
                ate = ate
            )
        }

        fun gSimulate(
            d: P
        ): Sim =
            gSimulateOn(
                ArrayDeque(gSnake),
                d
            )

        fun gSimulateOn(
            src: ArrayDeque<P>,
            d: P
        ): Sim {
            val b =
                ArrayDeque(src)

            if (b.isEmpty()) {
                return Sim(
                    b,
                    false
                )
            }

            val nh =
                P(
                    b.first().x + d.x,
                    b.first().y + d.y
                )

            if (!gInside(nh)) {
                return Sim(
                    b,
                    false
                )
            }

            val ate =
                nh == gFood

            if (
                b.contains(nh) &&
                !(nh == b.last() && !ate)
            ) {
                return Sim(
                    b,
                    false
                )
            }

            b.addFirst(nh)

            if (!ate) {
                b.removeLast()
            }

            return Sim(
                b,
                ate
            )
        }

        fun gLegalDirection(
            d: P
        ): Boolean {
            if (d == P(0, 0)) {
                return false
            }

            if (
                gIsReverse(
                    d,
                    gDir
                )
            ) {
                return false
            }

            if (gSnake.isEmpty()) {
                return false
            }

            val nh =
                P(
                    gSnake.first().x + d.x,
                    gSnake.first().y + d.y
                )

            if (!gInside(nh)) {
                return false
            }

            val ate =
                nh == gFood

            return !gSnake.contains(nh) ||
                (
                    nh == gSnake.last() &&
                        !ate
                    )
        }

        fun gIsReverse(
            a: P,
            b: P
        ): Boolean =
            a.x == -b.x &&
                a.y == -b.y

        fun gInside(
            p: P
        ): Boolean =
            p.x in 0 until cols &&
                p.y in 0 until rows

        fun gFreeRegion(
            body: ArrayDeque<P>
        ): Int {
            if (body.isEmpty()) {
                return 0
            }

            java.util.Arrays.fill(
                vis,
                0,
                total,
                false
            )

            for (p in body) {
                if (!gInside(p)) continue

                vis[
                    p.y * cols +
                        p.x
                ] = true
            }

            val start =
                body.first()

            if (!gInside(start)) {
                return 0
            }

            val si =
                start.y * cols +
                    start.x

            vis[si] = true

            var head = 0
            var tail = 0

            que[tail++] =
                si

            var count = 0

            while (head < tail) {
                val curr =
                    que[head++]

                val cx =
                    curr % cols

                val cy =
                    curr / cols

                count++

                if (cx > 0) {
                    val ni =
                        curr - 1

                    if (!vis[ni]) {
                        vis[ni] = true

                        if (tail < total) {
                            que[tail++] =
                                ni
                        }
                    }
                }

                if (cx < cols - 1) {
                    val ni =
                        curr + 1

                    if (!vis[ni]) {
                        vis[ni] = true

                        if (tail < total) {
                            que[tail++] =
                                ni
                        }
                    }
                }

                if (cy > 0) {
                    val ni =
                        curr - cols

                    if (!vis[ni]) {
                        vis[ni] = true

                        if (tail < total) {
                            que[tail++] =
                                ni
                        }
                    }
                }

                if (cy < rows - 1) {
                    val ni =
                        curr + cols

                    if (!vis[ni]) {
                        vis[ni] = true

                        if (tail < total) {
                            que[tail++] =
                                ni
                        }
                    }
                }
            }

            return count
        }

        fun gDistance(
            start: P,
            target: P,
            body: Collection<P>,
            allowTail: Boolean
        ): Int {
            if (
                !gInside(start) ||
                !gInside(target)
            ) {
                return -1
            }

            if (start == target) {
                return 0
            }

            java.util.Arrays.fill(
                vis,
                0,
                total,
                false
            )

            for (p in body) {
                if (!gInside(p)) continue

                vis[
                    p.y * cols +
                        p.x
                ] = true
            }

            if (
                allowTail &&
                body.isNotEmpty()
            ) {
                val last =
                    body.last()

                if (gInside(last)) {
                    vis[
                        last.y * cols +
                            last.x
                    ] = false
                }
            }

            val si =
                start.y * cols +
                    start.x

            vis[si] = true

            var head = 0
            var tail = 0

            que[tail++] =
                si

            var dist = 0

            while (head < tail) {
                val layer =
                    tail - head

                repeat(layer) {
                    if (head >= tail) {
                        return@repeat
                    }

                    val curr =
                        que[head++]

                    val cx =
                        curr % cols

                    val cy =
                        curr / cols

                    if (
                        cx == target.x &&
                        cy == target.y
                    ) {
                        return dist
                    }

                    if (cx > 0) {
                        val ni =
                            curr - 1

                        if (!vis[ni]) {
                            vis[ni] = true

                            if (tail < total) {
                                que[tail++] =
                                    ni
                            }
                        }
                    }

                    if (cx < cols - 1) {
                        val ni =
                            curr + 1

                        if (!vis[ni]) {
                            vis[ni] = true

                            if (tail < total) {
                                que[tail++] =
                                    ni
                            }
                        }
                    }

                    if (cy > 0) {
                        val ni =
                            curr - cols

                        if (!vis[ni]) {
                            vis[ni] = true

                            if (tail < total) {
                                que[tail++] =
                                    ni
                            }
                        }
                    }

                    if (cy < rows - 1) {
                        val ni =
                            curr + cols

                        if (!vis[ni]) {
                            vis[ni] = true

                            if (tail < total) {
                                que[tail++] =
                                    ni
                            }
                        }
                    }
                }

                dist++
            }

            return -1
        }

        fun gCountSafeMoves(
            body: ArrayDeque<P>
        ): Int {
            if (body.isEmpty()) {
                return 0
            }

            val h =
                body.first()

            val prevDir =
                if (body.size < 2) {
                    gDir
                } else {
                    P(
                        body.elementAt(0).x -
                            body.elementAt(1).x,
                        body.elementAt(0).y -
                            body.elementAt(1).y
                    )
                }

            return dirs.count { d ->
                val nh =
                    P(
                        h.x + d.x,
                        h.y + d.y
                    )

                gInside(nh) &&
                    (
                        !body.contains(nh) ||
                            (
                                nh ==
                                    body.last() &&
                                    nh != gFood
                                )
                        ) &&
                    !gIsReverse(
                        d,
                        prevDir
                    )
            }
        }

        fun gTailReachable(
            body: ArrayDeque<P>
        ): Boolean =
            if (body.isEmpty()) {
                false
            } else {
                gDistance(
                    body.first(),
                    body.last(),
                    body,
                    true
                ) >= 0
            }

        fun gShortestPath(
            start: P,
            target: P,
            body: Collection<P>,
            allowTail: Boolean
        ): List<P>? {
            if (start == target) {
                return emptyList()
            }

            if (
                !gInside(start) ||
                !gInside(target)
            ) {
                return null
            }

            java.util.Arrays.fill(
                vis,
                0,
                total,
                false
            )

            for (p in body) {
                if (!gInside(p)) continue

                val idx =
                    p.y * cols +
                        p.x

                vis[idx] = true
            }

            if (
                allowTail &&
                body.isNotEmpty()
            ) {
                val last =
                    body.last()

                if (gInside(last)) {
                    val li =
                        last.y * cols +
                            last.x

                    vis[li] = false
                }
            }

            val si =
                start.y * cols +
                    start.x

            val ti =
                target.y * cols +
                    target.x

            vis[si] = true

            java.util.Arrays.fill(
                par,
                0,
                total,
                -1
            )

            for (i in 0 until total) {
                parDir[i] = null
            }

            var head = 0
            var tail = 0

            que[tail++] =
                si

            var found = false

            while (head < tail) {
                val curr =
                    que[head++]

                if (curr == ti) {
                    found = true
                    break
                }

                val cx =
                    curr % cols

                val cy =
                    curr / cols

                if (cy > 0) {
                    val ni =
                        curr - cols

                    if (!vis[ni]) {
                        vis[ni] = true
                        par[ni] = curr
                        parDir[ni] =
                            P(0, -1)

                        if (tail < total) {
                            que[tail++] =
                                ni
                        }
                    }
                }

                if (cy < rows - 1) {
                    val ni =
                        curr + cols

                    if (!vis[ni]) {
                        vis[ni] = true
                        par[ni] = curr
                        parDir[ni] =
                            P(0, 1)

                        if (tail < total) {
                            que[tail++] =
                                ni
                        }
                    }
                }

                if (cx > 0) {
                    val ni =
                        curr - 1

                    if (!vis[ni]) {
                        vis[ni] = true
                        par[ni] = curr
                        parDir[ni] =
                            P(-1, 0)

                        if (tail < total) {
                            que[tail++] =
                                ni
                        }
                    }
                }

                if (cx < cols - 1) {
                    val ni =
                        curr + 1

                    if (!vis[ni]) {
                        vis[ni] = true
                        par[ni] = curr
                        parDir[ni] =
                            P(1, 0)

                        if (tail < total) {
                            que[tail++] =
                                ni
                        }
                    }
                }
            }

            if (!found) {
                return null
            }

            val steps =
                ArrayList<P>()

            var cur =
                ti

            while (cur != si) {
                val d =
                    parDir[cur]
                        ?: return null

                steps.add(d)

                cur =
                    par[cur]

                if (cur < 0) {
                    return null
                }
            }

            steps.reverse()

            return steps
        }

        fun gCalculateDanger(): Int {
            val region =
                gFreeRegion(
                    gSnake
                )

            val ratio =
                region.toFloat() /
                    max(
                        1,
                        gSnake.size
                    )

            val mobility =
                gCountSafeMoves(
                    gSnake
                )

            return when {
                mobility <= 0 -> 5
                ratio < 1.5f -> 5
                ratio < 2.2f -> 4
                ratio < 3.5f -> 3
                ratio < 5f -> 2
                else -> 1
            }
        }

        fun gDie(
            cause: String
        ) {
            synchronized(sharedLock) {
                when (cause) {
                    "WALL" ->
                        deathWall++

                    "SELF" ->
                        deathSelf++

                    else ->
                        deathTrap++
                }

                totalGames++

                recentScores.addLast(
                    gScore
                )

                while (
                    recentScores.size > 50
                ) {
                    recentScores.removeFirst()
                }

                if (
                    gScore >
                    bestRecentScore
                ) {
                    bestRecentScore =
                        gScore
                }

                // 记录当前个体的成绩
                currentScores[currentAgentId % POPULATION_SIZE] = max(currentScores[currentAgentId % POPULATION_SIZE], gScore.toFloat())

                adjustWeights(
                    cause
                )

                safetyMargin =
                    safetyMargin * 0.95f +
                        1.08f * 0.05f

                aggression =
                    aggression * 0.95f +
                        1.15f * 0.05f

                safetyMargin =
                    safetyMargin.coerceIn(
                        1.0f,
                        1.20f
                    )

                aggression =
                    aggression.coerceIn(
                        0.95f,
                        1.35f
                    )

                v2Episodes++

                if (
                    totalGames % 200 == 0
                ) {
                    saveLearning()
                }
            }
        }
    }

    /*
     * =========================
     * BGM
     * =========================
     */

    private class BgmPlayer {

        private var audioTrack:
            AudioTrack? = null

        @Volatile
        private var playing =
            false

        private var thread:
            Thread? = null

        fun start() {
            if (playing) {
                return
            }

            playing = true

            thread =
                Thread {
                    try {
                        val sr =
                            22050

                        val pcm =
                            generateMelody(sr)

                        val track =
                            AudioTrack.Builder()
                                .setAudioAttributes(
                                    AudioAttributes.Builder()
                                        .setUsage(
                                            AudioAttributes.USAGE_GAME
                                        )
                                        .setContentType(
                                            AudioAttributes.CONTENT_TYPE_MUSIC
                                        )
                                        .build()
                                )
                                .setAudioFormat(
                                    AudioFormat.Builder()
                                        .setEncoding(
                                            AudioFormat.ENCODING_PCM_16BIT
                                        )
                                        .setSampleRate(sr)
                                        .setChannelMask(
                                            AudioFormat.CHANNEL_OUT_MONO
                                        )
                                        .build()
                                )
                                .setBufferSizeInBytes(
                                    pcm.size * 2
                                )
                                .setTransferMode(
                                    AudioTrack.MODE_STATIC
                                )
                                .build()

                        track.write(
                            pcm,
                            0,
                            pcm.size
                        )

                        if (
                            Build.VERSION.SDK_INT >= 23
                        ) {
                            track.setLoopPoints(
                                0,
                                pcm.size,
                                -1
                            )
                        }

                        audioTrack =
                            track

                        if (playing) {
                            track.play()
                        }
                    } catch (_: Throwable) {
                    }
                }.also {
                    it.start()
                }
        }

        fun stop() {
            playing = false

            try {
                audioTrack?.pause()
            } catch (_: Throwable) {
            }

            try {
                audioTrack?.flush()
            } catch (_: Throwable) {
            }

            try {
                audioTrack?.release()
            } catch (_: Throwable) {
            }

            audioTrack = null
            thread = null
        }

        private fun generateMelody(
            sampleRate: Int
        ): ShortArray {
            val N = 0f

            val E5 = 659.25f
            val G5 = 783.99f
            val C6 = 1046.50f
            val D5 = 587.33f
            val F5 = 698.46f
            val A5 = 880.00f
            val C5 = 523.25f
            val E4 = 329.63f
            val G4 = 392.00f
            val B4 = 493.88f
            val A4 = 440.00f

            val notes =
                listOf(
                    E5 to 180,
                    G5 to 180,
                    C6 to 180,
                    G5 to 180,
                    E5 to 180,
                    G5 to 180,
                    C6 to 260,
                    N to 100,

                    D5 to 180,
                    F5 to 180,
                    A5 to 180,
                    F5 to 180,
                    D5 to 180,
                    F5 to 180,
                    A5 to 260,
                    N to 100,

                    E5 to 180,
                    G5 to 180,
                    C6 to 180,
                    G5 to 180,
                    E5 to 180,
                    G5 to 180,
                    C6 to 180,
                    E4 to 180,

                    F5 to 180,
                    A5 to 180,
                    C6 to 180,
                    A5 to 180,
                    G5 to 260,
                    D5 to 260,
                    C5 to 420,
                    N to 260,

                    C5 to 180,
                    E5 to 180,
                    G5 to 180,
                    E5 to 180,
                    A4 to 180,
                    C5 to 180,
                    E5 to 180,
                    C5 to 180,

                    G4 to 180,
                    B4 to 180,
                    D5 to 180,
                    G5 to 180,
                    E5 to 220,
                    D5 to 220,
                    C5 to 420,
                    N to 260,

                    E5 to 180,
                    D5 to 180,
                    C5 to 180,
                    D5 to 180,
                    E5 to 260,
                    G5 to 260,
                    C6 to 400,
                    N to 200
                )

            val out =
                ArrayList<Short>()

            for ((freq, durMs) in notes) {
                val n =
                    durMs *
                        sampleRate /
                        1000

                if (
                    freq == N ||
                    freq <= 0f
                ) {
                    repeat(n) {
                        out.add(0)
                    }
                } else {
                    val period =
                        (
                            sampleRate /
                                freq
                            ).toInt()
                            .coerceAtLeast(1)

                    for (i in 0 until n) {
                        val phase =
                            (
                                i % period
                                ) /
                                period.toFloat()

                        val t =
                            i.toFloat() /
                                n

                        val env =
                            when {
                                t < 0.05f ->
                                    t / 0.05f

                                t > 0.70f ->
                                    (
                                        1f - t
                                        ) / 0.30f

                                else ->
                                    1f
                            }.coerceIn(
                                0f,
                                1f
                            )

                        val v =
                            (
                                if (
                                    phase < 0.5f
                                ) {
                                    1f
                                } else {
                                    -1f
                                }
                                ) *
                                env *
                                0.06f

                        out.add(
                            (
                                v *
                                    Short.MAX_VALUE
                                ).toInt()
                                .coerceIn(
                                    Short.MIN_VALUE.toInt(),
                                    Short.MAX_VALUE.toInt()
                                )
                                .toShort()
                        )
                    }
                }
            }

            return out.toShortArray()
        }
    }
}


/*
 * ============================================================
 *                         AI V3
 * ============================================================
 *
 * 核心：
 *
 *   State
 *      ↓
 *   Goal
 *      ↓
 *   Q + Brain + Environment
 *      ↓
 *   Counterfactual
 *      ↓
 *   Action
 *      ↓
 *   Game Result
 *      ↓
 *   Reward
 *      ↓
 *   Death Analysis
 *      ↓
 *   Failure Memory
 *      ↓
 *   Self Adjustment
 *      ↓
 *   Genetic Evolution
 *
 * AI 不直接修改 SnakeView 的游戏世界。
 *
 * SnakeView：
 *   负责游戏
 *
 * AI V3：
 *   只负责观察、学习、判断和返回动作。
 *
 * ============================================================
 */


/* ============================================================
 * 1. ACTION
 * ============================================================
 */

enum class V3Action {
    UP,
    RIGHT,
    DOWN,
    LEFT
}


/* ============================================================
 * 2. CURRENT GOAL
 * ============================================================
 */

enum class V3Goal {

    GET_FOOD,

    PRESERVE_SPACE,

    REACH_TAIL,

    ESCAPE_DANGER,

    BREAK_LOOP,

    SURVIVE
}


/* ============================================================
 * 3. DEATH REASON
 * ============================================================
 */

enum class V3DeathReason {

    HIT_WALL,

    HIT_SELF,

    TRAPPED,

    DEAD_END,

    LOOP,

    SPACE_COLLAPSE,

    TAIL_CUTOFF,

    HUNGER,

    UNKNOWN
}


/* ============================================================
 * 4. STATE
 * ============================================================
 *
 * body:
 *   head first
 *   tail last
 *
 * cell = y * width + x
 *
 */

data class V3State(

    val width: Int,

    val height: Int,

    val body: IntArray,

    val food: Int,

    val direction: V3Action,

    val score: Int = 0,

    val steps: Int = 0,

    val stepsSinceFood: Int = 0,

    val hunger: Float = 0f,

    val gameOver: Boolean = false,

    val recentHashes: LongArray = longArrayOf()
) {

    val cells: Int
        get() = width * height

    val head: Int
        get() = if (body.isNotEmpty()) body[0] else 0

    val tail: Int
        get() = if (body.isNotEmpty()) body[body.size - 1] else head

    fun copyDeep(): V3State {
        return copy(
            body = body.clone(),
            recentHashes = recentHashes.clone()
        )
    }
}


/* ============================================================
 * 5. ENCODED STATE
 * ============================================================
 */

data class V3EncodedState(

    val values: FloatArray,

    val hash: Long
)


/* ============================================================
 * 6. ACTION EVALUATION
 * ============================================================
 */

data class V3ActionEvaluation(

    val action: V3Action,

    val qValue: Float,

    val brainValue: Float,

    val foodValue: Float,

    val spaceValue: Float,

    val tailValue: Float,

    val dangerValue: Float,

    val loopValue: Float,

    val counterfactualValue: Float,

    val memoryPenalty: Float,

    val finalValue: Float,

    val immediateDeath: Boolean
)


/* ============================================================
 * 7. DECISION TRACE
 * ============================================================
 */

data class V3Decision(

    val action: V3Action,

    val goal: V3Goal,

    val evaluations: List<V3ActionEvaluation>,

    val explored: Boolean
)


/* ============================================================
 * 8. EXPERIENCE
 * ============================================================
 */

data class V3Experience(

    val state: V3EncodedState,

    val action: V3Action,

    val reward: Float,

    val nextState: V3EncodedState?,

    val done: Boolean,

    val deathReason: V3DeathReason? = null,

    val priority: Float = 1f,

    val nextLegalMask: BooleanArray? = null
)


/* ============================================================
 * 9. DEATH REPORT
 * ============================================================
 */

data class V3DeathReport(

    val reason: V3DeathReason,

    val action: V3Action?,

    val stateHash: Long,

    val avoidable: Boolean,

    val bestAlternative: V3Action?,

    val regret: Float,

    val freeSpace: Int,

    val safeActions: Int,

    val tailReachable: Boolean,

    val foodDistance: Int,

    val repeatedFailure: Int
)


/* ============================================================
 * 10. LESSON
 * ============================================================
 */

data class V3Lesson(

    val contextHash: Long,

    val badAction: V3Action,

    val reason: V3DeathReason,

    var penalty: Float,

    var confidence: Float,

    var occurrences: Int = 1,

    var alternative: V3Action? = null
)


/* ============================================================
 * 11. STRATEGY GENOME
 * ============================================================
 *
 * 每个 AI 都有自己的“行为性格”。
 *
 */

data class V3StrategyGenome(

    var foodPriority: Float = 1.00f,

    var spacePriority: Float = 1.25f,

    var tailPriority: Float = 0.90f,

    var dangerAversion: Float = 1.40f,

    var loopAversion: Float = 0.80f,

    var hungerUrgency: Float = 0.80f,

    var explorationBias: Float = 1.00f,

    var 1.0f: Float = 0.70f,

    var brainWeight: Float = 0.30f,

    var mutationRate: Float = 0.08f,

    var mutationSigma: Float = 0.12f,

    var lookaheadDepth: Int = 2
) {

    fun deepCopy(): V3StrategyGenome {

        return copy()
    }


    fun normalize() {

        foodPriority =
            foodPriority.coerceIn(0.1f, 3f)

        spacePriority =
            spacePriority.coerceIn(0.1f, 3f)

        tailPriority =
            tailPriority.coerceIn(0.1f, 3f)

        dangerAversion =
            dangerAversion.coerceIn(0.1f, 3f)

        loopAversion =
            loopAversion.coerceIn(0.1f, 3f)

        hungerUrgency =
            hungerUrgency.coerceIn(0.1f, 3f)

        explorationBias =
            explorationBias.coerceIn(0.2f, 2f)

        1.0f =
            1.0f.coerceIn(0.05f, 0.95f)

        brainWeight =
            1f - 1.0f

        mutationRate =
            mutationRate.coerceIn(0.005f, 0.35f)

        mutationSigma =
            mutationSigma.coerceIn(0.01f, 0.5f)

        lookaheadDepth =
            lookaheadDepth.coerceIn(1, 3)
    }


    /*
     * AI 根据自己的死亡原因调整策略。
     */
    fun selfAdjust(

        reason: V3DeathReason,

        repeated: Boolean,

        avoidable: Boolean

    ) {

        val amount =
            if (repeated) 0.08f
            else 0.035f

        when (reason) {

            V3DeathReason.HIT_WALL,
            V3DeathReason.HIT_SELF -> {

                dangerAversion += amount
            }

            V3DeathReason.TRAPPED,
            V3DeathReason.DEAD_END,
            V3DeathReason.SPACE_COLLAPSE -> {

                spacePriority += amount
            }

            V3DeathReason.TAIL_CUTOFF -> {

                tailPriority += amount
            }

            V3DeathReason.LOOP -> {

                loopAversion += amount
            }

            V3DeathReason.HUNGER -> {

                hungerUrgency += amount
            }

            V3DeathReason.UNKNOWN -> {

                dangerAversion += amount * 0.25f
            }
        }


        if (avoidable) {

            explorationBias -= 0.01f
        }


        normalize()
    }


    /*
     * 两个优秀 Agent 的策略交叉。
     */
    fun crossover(
        other: V3StrategyGenome
    ): V3StrategyGenome {

        fun pick(
            a: Float,
            b: Float
        ): Float {

            return if (Random.nextBoolean()) a else b
        }

        return V3StrategyGenome(

            foodPriority =
                pick(foodPriority, other.foodPriority),

            spacePriority =
                pick(spacePriority, other.spacePriority),

            tailPriority =
                pick(tailPriority, other.tailPriority),

            dangerAversion =
                pick(dangerAversion, other.dangerAversion),

            loopAversion =
                pick(loopAversion, other.loopAversion),

            hungerUrgency =
                pick(hungerUrgency, other.hungerUrgency),

            explorationBias =
                pick(explorationBias, other.explorationBias),

            1.0f =
                pick(1.0f, other.1.0f),

            brainWeight = 0f,

            mutationRate =
                pick(mutationRate, other.mutationRate),

            mutationSigma =
                pick(mutationSigma, other.mutationSigma),

            lookaheadDepth =
                max(
                    lookaheadDepth,
                    other.lookaheadDepth
                )
        ).also {

            it.normalize()
        }
    }


    /*
     * 基因突变。
     */
    fun mutate(
        scale: Float = 1f
    ) {

        fun noise(): Float {

            return (
                    Random.nextFloat() * 2f - 1f
                    ) *
                    mutationSigma *
                    scale
        }


        if (Random.nextFloat() < mutationRate)
            foodPriority += noise()

        if (Random.nextFloat() < mutationRate)
            spacePriority += noise()

        if (Random.nextFloat() < mutationRate)
            tailPriority += noise()

        if (Random.nextFloat() < mutationRate)
            dangerAversion += noise()

        if (Random.nextFloat() < mutationRate)
            loopAversion += noise()

        if (Random.nextFloat() < mutationRate)
            hungerUrgency += noise()

        if (Random.nextFloat() < mutationRate)
            explorationBias += noise()

        if (Random.nextFloat() < mutationRate)
            1.0f += noise() * 0.25f


        normalize()
    }
}


/* ============================================================
 * 12. BOARD TOOLS
 * ============================================================
 */

object V3Board {


    private fun point(
        state: V3State,
        cell: Int
    ): Pair<Int, Int> {

        return Pair(
            cell % state.width,
            cell / state.width
        )
    }


    fun step(
        state: V3State,
        cell: Int,
        action: V3Action
    ): Int {

        val p = point(state, cell)

        val x = p.first

        val y = p.second


        val nx: Int

        val ny: Int


        when (action) {

            V3Action.UP -> {

                nx = x
                ny = y - 1
            }

            V3Action.RIGHT -> {

                nx = x + 1
                ny = y
            }

            V3Action.DOWN -> {

                nx = x
                ny = y + 1
            }

            V3Action.LEFT -> {

                nx = x - 1
                ny = y
            }
        }


        if (
            nx < 0 ||
            nx >= state.width ||
            ny < 0 ||
            ny >= state.height
        ) {

            return -1
        }


        return ny * state.width + nx
    }


    fun opposite(
        action: V3Action
    ): V3Action {

        return when (action) {

            V3Action.UP ->
                V3Action.DOWN

            V3Action.RIGHT ->
                V3Action.LEFT

            V3Action.DOWN ->
                V3Action.UP

            V3Action.LEFT ->
                V3Action.RIGHT
        }
    }


    fun left(
        action: V3Action
    ): V3Action {

        return when (action) {

            V3Action.UP ->
                V3Action.LEFT

            V3Action.LEFT ->
                V3Action.DOWN

            V3Action.DOWN ->
                V3Action.RIGHT

            V3Action.RIGHT ->
                V3Action.UP
        }
    }


    fun right(
        action: V3Action
    ): V3Action {

        return when (action) {

            V3Action.UP ->
                V3Action.RIGHT

            V3Action.RIGHT ->
                V3Action.DOWN

            V3Action.DOWN ->
                V3Action.LEFT

            V3Action.LEFT ->
                V3Action.UP
        }
    }


    fun occupied(
        state: V3State
    ): BooleanArray {

        val result =
            BooleanArray(state.cells)


        for (cell in state.body) {

            if (cell in result.indices) {

                result[cell] = true
            }
        }


        return result
    }


    /*
     * 判断动作是不是立即死亡。
     */
    fun immediateDeath(
        state: V3State,
        action: V3Action
    ): Boolean {

        if (
            action == opposite(state.direction) &&
            state.body.size > 1
        ) {

            return true
        }


        val next =
            step(
                state,
                state.head,
                action
            )


        if (next < 0) {

            return true
        }


        val occupied =
            occupied(state)


        if (!occupied[next]) {

            return false
        }


        /*
         * 尾巴本步通常会移动。
         */
        if (next == state.tail) {

            return false
        }


        return true
    }


    fun legalActions(
        state: V3State
    ): List<V3Action> {

        return V3Action.values()
            .filter {
                !immediateDeath(
                    state,
                    it
                )
            }
    }


    /*
     * 抽象模拟。
     *
     * 注意：
     * 不修改真实 SnakeView。
     */
    fun simulate(
        state: V3State,
        action: V3Action
    ): V3State? {

        if (
            immediateDeath(
                state,
                action
            )
        ) {

            return null
        }


        val next =
            step(
                state,
                state.head,
                action
            )


        if (next < 0) {

            return null
        }


        val ate =
            next == state.food


        val newSize =
            if (ate)
                state.body.size + 1
            else
                state.body.size


        val newBody =
            IntArray(newSize)


        newBody[0] = next


        for (i in 1 until newSize) {

            newBody[i] =
                state.body[i - 1]
        }


        val newState = state.copy(
            body = newBody,
            direction = action,
            food = if (ate) -1 else state.food,
            steps = state.steps + 1,
            stepsSinceFood = if (ate) 0 else state.stepsSinceFood + 1,
            hunger = if (ate) 0f else min(1f, state.hunger + 0.002f)
        )

        val newHash = newBody.contentHashCode().toLong() * 31 + newState.food + newState.direction.ordinal
        val newHashes = (state.recentHashes + newHash).takeLast(16).toLongArray()

        return newState.copy(recentHashes = newHashes)
    }


    /*
     * BFS 计算自由空间。
     */
    fun freeSpace(
        state: V3State
    ): Int {

        val blocked =
            occupied(state)

        val seen =
            BooleanArray(state.cells)

        val queue =
            ArrayDeque<Int>()


        queue.add(state.head)

        seen[state.head] = true


        var count = 0


        while (queue.isNotEmpty()) {

            val cell =
                queue.removeFirst()

            count++


            val x =
                cell % state.width

            val y =
                cell / state.width


            val neighbours =
                intArrayOf(

                    if (y > 0)
                        cell - state.width
                    else -1,

                    if (x + 1 < state.width)
                        cell + 1
                    else -1,

                    if (y + 1 < state.height)
                        cell + state.width
                    else -1,

                    if (x > 0)
                        cell - 1
                    else -1
                )


            for (next in neighbours) {

                if (
                    next >= 0 &&
                    !seen[next] &&
                    (
                            !blocked[next] ||
                            next == state.tail
                            )
                ) {

                    seen[next] = true

                    queue.add(next)
                }
            }
        }


        return count
    }


    /*
     * 判断蛇头能不能找到尾巴。
     */
    fun tailReachable(
        state: V3State
    ): Pair<Boolean, Int> {

        val blocked =
            occupied(state)

        blocked[state.head] = false
        blocked[state.tail] = false


        val distance =
            IntArray(state.cells) {
                -1
            }


        val queue =
            ArrayDeque<Int>()


        queue.add(state.head)

        distance[state.head] = 0


        while (queue.isNotEmpty()) {

            val cell =
                queue.removeFirst()


            if (cell == state.tail) {

                return Pair(
                    true,
                    distance[cell]
                )
            }


            val x =
                cell % state.width

            val y =
                cell / state.width


            val neighbours =
                intArrayOf(

                    if (y > 0)
                        cell - state.width
                    else -1,

                    if (x + 1 < state.width)
                        cell + 1
                    else -1,

                    if (y + 1 < state.height)
                        cell + state.width
                    else -1,

                    if (x > 0)
                        cell - 1
                    else -1
                )


            for (next in neighbours) {

                if (
                    next >= 0 &&
                    distance[next] < 0 &&
                    !blocked[next]
                ) {

                    distance[next] =
                        distance[cell] + 1

                    queue.add(next)
                }
            }
        }


        return Pair(
            false,
            Int.MAX_VALUE
        )
    }
}


/* ============================================================
 * 13. STATE ENCODER
 * ============================================================
 */

class V3StateEncoder {


    companion object {

        /*
         * 固定输入维度。
         */
        const val INPUTS = 64
    }


    fun encode(
        state: V3State
    ): V3EncodedState {

        val values =
            FloatArray(INPUTS)


        var index = 0


        fun put(
            value: Float
        ) {

            if (
                index < values.size
            ) {

                values[index++] =
                    value.coerceIn(
                        -1f,
                        1f
                    )
            }
        }


        val hx =
            state.head % state.width

        val hy =
            state.head / state.width


        val fx =
            if (state.food >= 0)
                state.food % state.width
            else
                hx


        val fy =
            if (state.food >= 0)
                state.food / state.width
            else
                hy


        val scale =
            max(
                1,
                state.width + state.height
            ).toFloat()


        /*
         * 食物相对位置。
         */
        put(
            (fx - hx) / scale
        )

        put(
            (fy - hy) / scale
        )

        put(
            abs(fx - hx) /
                    max(
                        1f,
                        state.width.toFloat()
                    )
        )

        put(
            abs(fy - hy) /
                    max(
                        1f,
                        state.height.toFloat()
                    )
        )


        /*
         * 当前方向 one-hot。
         */
        for (action in V3Action.values()) {

            put(
                if (
                    action == state.direction
                )
                    1f
                else
                    0f
            )
        }


        /*
         * 四方向扫描。
         */
        val occupied =
            V3Board.occupied(state)


        for (action in V3Action.values()) {

            var cell =
                state.head

            var distance = 0

            var bodySeen = false

            var foodSeen = false


            repeat(
                max(
                    state.width,
                    state.height
                )
            ) {

                cell =
                    V3Board.step(
                        state,
                        cell,
                        action
                    )


                if (cell < 0) {

                    return@repeat
                }


                distance++


                if (occupied[cell]) {

                    bodySeen = true

                    return@repeat
                }


                if (
                    cell == state.food
                ) {

                    foodSeen = true
                }
            }


            put(
                distance / scale
            )

            put(
                if (bodySeen)
                    1f
                else
                    0f
            )

            put(
                if (foodSeen)
                    1f
                else
                    0f
            )
        }


        /*
         * 当前四方向危险。
         */
        put(
            if (
                V3Board.immediateDeath(
                    state,
                    state.direction
                )
            )
                1f
            else
                0f
        )


        put(
            if (
                V3Board.immediateDeath(
                    state,
                    V3Board.left(
                        state.direction
                    )
                )
            )
                1f
            else
                0f
        )


        put(
            if (
                V3Board.immediateDeath(
                    state,
                    V3Board.right(
                        state.direction
                    )
                )
            )
                1f
            else
                0f
        )


        put(
            if (
                V3Board.immediateDeath(
                    state,
                    V3Board.opposite(
                        state.direction
                    )
                )
            )
                1f
            else
                0f
        )


        /*
         * 空间。
         */
        val free =
            V3Board.freeSpace(state)


        put(
            free.toFloat() /
                    max(
                        1,
                        state.cells
                    )
        )


        /*
         * 安全动作数量。
         */
        put(
            V3Board.legalActions(state)
                .size
                .toFloat() /
                    3f
        )


        /*
         * 尾巴。
         */
        val tail =
            V3Board.tailReachable(state)


        put(
            if (tail.first)
                1f
            else
                0f
        )


        put(
            if (
                tail.second == Int.MAX_VALUE
            )
                1f
            else
                min(
                    1f,
                    tail.second / scale
                )
        )


        /*
         * Hunger。
         */
        put(state.hunger)


        /*
         * Snake 长度。
         */
        put(
            state.body.size.toFloat() /
                    max(
                        1,
                        state.cells
                    )
        )


        /*
         * 时间。
         */
        put(
            min(
                1f,
                state.steps / 5000f
            )
        )


        /*
         * Loop risk。
         */
        put(
            loopRisk(state)
        )


        /*
         * Food 是否存在。
         */
        put(
            if (state.food >= 0)
                1f
            else
                0f
        )


        /*
         * Score。
         */
        put(
            min(
                1f,
                state.score / 1000f
            )
        )


        /*
         * Steps since food。
         */
        put(
            min(
                1f,
                state.stepsSinceFood / 1000f
            )
        )


        /*
         * Body density。
         */
        put(
            state.body.size.toFloat() /
                    max(
                        1,
                        state.cells
                    )
        )


        /*
         * 再加入八方向局部感知。
         */
        val directions =
            arrayOf(

                V3Action.UP,

                V3Action.RIGHT,

                V3Action.DOWN,

                V3Action.LEFT,

                V3Board.left(V3Action.UP),

                V3Board.right(V3Action.UP),

                V3Board.left(V3Action.DOWN),

                V3Board.right(V3Action.DOWN)
            )


        for (action in directions) {

            var cell =
                state.head

            var distance = 0

            var hitBody = 0

            var hitFood = 0


            repeat(4) {

                cell =
                    V3Board.step(
                        state,
                        cell,
                        action
                    )


                if (cell < 0) {

                    return@repeat
                }


                distance++


                if (
                    occupied[cell]
                ) {

                    hitBody = 1

                    return@repeat
                }


                if (
                    cell == state.food
                ) {

                    hitFood = 1
                }
            }


            put(
                distance / 4f
            )

            put(
                hitBody.toFloat()
            )

            put(
                hitFood.toFloat()
            )
        }


        /*
         * 没填满的全部补 0。
         */
        while (
            index < values.size
        ) {

            values[index++] = 0f
        }


        /*
         * 状态 Hash。
         */
        var hash =
            -3750763034362895579L


        for (value in values) {

            hash =
                (
                        hash xor
                                value.toBits().toLong()
                        ) *
                        1099511628211L
        }


        for (cell in state.body) {

            hash =
                (
                        hash xor
                                cell.toLong()
                        ) *
                        1099511628211L
        }


        hash =
            (
                    hash xor
                            state.food.toLong()
                    ) *
                    1099511628211L


        hash =
            (
                    hash xor
                            state.direction.ordinal.toLong()
                    ) *
                    1099511628211L


        return V3EncodedState(
            values,
            hash
        )
    }


    private fun loopRisk(
        state: V3State
    ): Float {

        if (
            state.recentHashes.size < 6
        ) {

            return 0f
        }


        val last =
            state.recentHashes
                .takeLast(6)


        val unique =
            last.toSet().size


        return (
                1f -
                        unique / 6f
                )
            .coerceIn(
                0f,
                1f
            )
    }
}


/* ============================================================
 * 14. DOUBLE-Q LEARNER
 * ============================================================
 */

class V3QLearner(

    private val gamma: Float = 0.97f,

    private val learningRate: Float = 0.003f,

    private val maxStates: Int = 100000

) {


    private val online =
        LinkedHashMap<Long, FloatArray>()


    private val target =
        HashMap<Long, FloatArray>()


    var learningSteps: Long = 0
        private set


    var meanTdError: Float = 0f
        private set


    @Synchronized
    private fun valuesInternal(
        table: MutableMap<Long, FloatArray>,
        hash: Long
    ): FloatArray {

        var q =
            table[hash]


        if (q == null) {

            if (
                table === online &&
                online.size >= maxStates
            ) {

                val iterator =
                    online.entries.iterator()


                if (
                    iterator.hasNext()
                ) {

                    iterator.next()

                    iterator.remove()
                }
            }


            q = FloatArray(4)

            table[hash] = q
        }


        return q
    }


    @Synchronized
    fun values(
        hash: Long
    ): FloatArray {

        return valuesInternal(
            online,
            hash
        ).clone()
    }


    /*
     * Double-Q style：

     * Online 决定下一动作。
     *
     * Target 估计下一动作。
     */
    @Synchronized
    fun learn(
        experience: V3Experience
    ) {

        val q =
            valuesInternal(
                online,
                experience.state.hash
            )


        val action =
            experience.action.ordinal


        val targetValue: Float


        if (
            experience.done ||
            experience.nextState == null
        ) {

            targetValue =
                experience.reward

        } else {

            val nextOnline =
                valuesInternal(
                    online,
                    experience.nextState.hash
                )

            val legalMask = experience.nextLegalMask

            var foundLegal = false
            var bestValue = Float.NEGATIVE_INFINITY
            var bestAction = 0

            for (i in nextOnline.indices) {
                if (legalMask != null && (i >= legalMask.size || !legalMask[i])) continue
                if (!foundLegal || nextOnline[i] > bestValue) {
                    bestValue = nextOnline[i]
                    foundLegal = true
                    bestAction = i
                }
            }

            val nextValue = if (foundLegal) {
                valuesInternal(target, experience.nextState.hash)[bestAction]
            } else 0f

            targetValue = experience.reward + gamma * nextValue
        }


        val clipped =
            targetValue.coerceIn(
                -20f,
                20f
            )


        val td =
            clipped - q[action]


        q[action] =
            (
                    q[action] +
                            learningRate *
                            td
                    )
                .coerceIn(
                    -20f,
                    20f
                )


        learningSteps++


        meanTdError =
            meanTdError * 0.995f +
                    abs(td) * 0.005f
    }


    @Synchronized
    fun syncTarget() {

        target.clear()


        for (
            entry in online
        ) {

            target[
                entry.key
            ] =
                entry.value.clone()
        }
    }


    @Synchronized
    fun clear() {

        online.clear()

        target.clear()

        learningSteps = 0

        meanTdError = 0f
    }
}


/* ============================================================
 * 15. TINY BRAIN
 * ============================================================
 *
 * 一个不依赖 TensorFlow / PyTorch 的轻量神经网络。
 *
 * 64
 *  ↓
 * 64
 *  ↓
 * 32
 *  ↓
 * 4
 *
 */

class V3TinyBrain(

    private val inputSize: Int =
        V3StateEncoder.INPUTS,

    private val hidden1Size: Int = 64,

    private val hidden2Size: Int = 32,

    private val outputSize: Int = 4,

    private var learningRate: Float = 0.001f

) {


    private val w1 =
        Array(hidden1Size) {

            FloatArray(inputSize) {

                Random.nextFloat() *
                        0.08f -
                        0.04f
            }
        }


    private val b1 =
        FloatArray(hidden1Size)


    private val w2 =
        Array(hidden2Size) {

            FloatArray(hidden1Size) {

                Random.nextFloat() *
                        0.08f -
                        0.04f
            }
        }


    private val b2 =
        FloatArray(hidden2Size)


    private val w3 =
        Array(outputSize) {

            FloatArray(hidden2Size) {

                Random.nextFloat() *
                        0.08f -
                        0.04f
            }
        }


    private val b3 =
        FloatArray(outputSize)


    fun forward(
        input: FloatArray
    ): FloatArray {

        val h1 =
            FloatArray(hidden1Size)


        for (i in 0 until hidden1Size) {

            var value =
                b1[i]


            for (
                j in input.indices
            ) {

                value +=
                    w1[i][j] *
                            input[j]
            }


            h1[i] =
                tanh(value)
                    .toFloat()
        }


        val h2 =
            FloatArray(hidden2Size)


        for (i in 0 until hidden2Size) {

            var value =
                b2[i]


            for (
                j in 0 until hidden1Size
            ) {

                value +=
                    w2[i][j] *
                            h1[j]
            }


            h2[i] =
                tanh(value)
                    .toFloat()
        }


        return FloatArray(
            outputSize
        ) { action ->

            var value =
                b3[action]


            for (
                j in 0 until hidden2Size
            ) {

                value +=
                    w3[action][j] *
                            h2[j]
            }


            value.coerceIn(
                -20f,
                20f
            )
        }
    }


    /*
     * 对指定 action 做一次梯度更新。
     */
    fun train(
        input: FloatArray,
        action: Int,
        target: Float
    ) {

        val h1 =
            FloatArray(hidden1Size)


        for (i in 0 until hidden1Size) {

            var value =
                b1[i]


            for (
                j in input.indices
            ) {

                value +=
                    w1[i][j] *
                            input[j]
            }


            h1[i] =
                tanh(value)
                    .toFloat()
        }


        val h2 =
            FloatArray(hidden2Size)


        for (i in 0 until hidden2Size) {

            var value =
                b2[i]


            for (
                j in 0 until hidden1Size
            ) {

                value +=
                    w2[i][j] *
                            h1[j]
            }


            h2[i] =
                tanh(value)
                    .toFloat()
        }


        var output =
            b3[action]


        for (
            j in 0 until hidden2Size
        ) {

            output +=
                w3[action][j] *
                        h2[j]
        }


        val error =
            (
                    target -
                            output
                    )
                .coerceIn(
                    -2f,
                    2f
                )


        val gradH2 =
            FloatArray(hidden2Size)


        for (
            j in 0 until hidden2Size
        ) {

            gradH2[j] =
                error *
                        w3[action][j] *
                        (
                                1f -
                                        h2[j] *
                                        h2[j]
                                )


            w3[action][j] +=
                learningRate *
                        error *
                        h2[j]
        }


        b3[action] +=
            learningRate *
                    error


        val gradH1 =
            FloatArray(hidden1Size)


        for (
            i in 0 until hidden1Size
        ) {

            var gradient =
                0f


            for (
                j in 0 until hidden2Size
            ) {

                gradient +=
                    gradH2[j] *
                            w2[j][i]


                w2[j][i] +=
                    learningRate *
                            gradH2[j] *
                            h1[i]
            }


            gradH1[i] =
                gradient *
                        (
                                1f -
                                        h1[i] *
                                        h1[i]
                                )


            for (
                j in input.indices
            ) {

                w1[i][j] +=
                    learningRate *
                            gradH1[i] *
                            input[j]
            }


            b1[i] +=
                learningRate *
                        gradH1[i]
        }
    }


    fun deepCopy(): V3TinyBrain {

        val result =
            V3TinyBrain(
                inputSize,
                hidden1Size,
                hidden2Size,
                outputSize,
                learningRate
            )


        for (i in 0 until hidden1Size) {

            result.b1[i] =
                b1[i]

            for (
                j in 0 until inputSize
            ) {

                result.w1[i][j] =
                    w1[i][j]
            }
        }


        for (i in 0 until hidden2Size) {

            result.b2[i] =
                b2[i]

            for (
                j in 0 until hidden1Size
            ) {

                result.w2[i][j] =
                    w2[i][j]
            }
        }


        for (i in 0 until outputSize) {

            result.b3[i] =
                b3[i]

            for (
                j in 0 until hidden2Size
            ) {

                result.w3[i][j] =
                    w3[i][j]
            }
        }


        return result
    }


    /*
     * 将另一个 Brain 完整复制到当前 Brain。
     */
    fun copyFrom(
        other: V3TinyBrain
    ) {

        for (i in 0 until hidden1Size) {

            b1[i] =
                other.b1[i]

            for (
                j in 0 until inputSize
            ) {

                w1[i][j] =
                    other.w1[i][j]
            }
        }


        for (i in 0 until hidden2Size) {

            b2[i] =
                other.b2[i]

            for (
                j in 0 until hidden1Size
            ) {

                w2[i][j] =
                    other.w2[i][j]
            }
        }


        for (i in 0 until outputSize) {

            b3[i] =
                other.b3[i]

            for (
                j in 0 until hidden2Size
            ) {

                w3[i][j] =
                    other.w3[i][j]
            }
        }
    }


    /*
     * Brain 遗传突变。
     */
    fun mutate(
        sigma: Float
    ) {

        fun noise(): Float {

            return (
                    Random.nextFloat() *
                            2f -
                            1f
                    ) *
                    sigma
        }


        for (
            i in 0 until hidden1Size
        ) {

            for (
                j in 0 until inputSize
            ) {

                w1[i][j] +=
                    noise()
            }


            b1[i] +=
                noise()
        }


        for (
            i in 0 until hidden2Size
        ) {

            for (
                j in 0 until hidden1Size
            ) {

                w2[i][j] +=
                    noise()
            }


            b2[i] +=
                noise()
        }


        for (
            i in 0 until outputSize
        ) {

            for (
                j in 0 until hidden2Size
            ) {

                w3[i][j] +=
                    noise()
            }


            b3[i] +=
                noise()
        }
    }
}


/* ============================================================
 * 16. REPLAY BUFFER
 * ============================================================
 */

class V3ReplayBuffer(

    private val capacity: Int = 20000

) {


    private val data =
        ArrayList<V3Experience>()


    @Synchronized
    fun add(
        experience: V3Experience
    ) {

        if (
            data.size >= capacity
        ) {

            data.removeAt(0)
        }


        data.add(
            experience
        )
    }


    @Synchronized
    fun sample(
        count: Int
    ): List<V3Experience> {

        if (
            data.isEmpty()
        ) {

            return emptyList()
        }


        return List(
            min(
                count,
                data.size
            )
        ) {

            /*
             * 当前版本先使用稳定的
             * weighted sampling。
             */
            val total =
                data.sumOf {
                    max(
                        0.01,
                        it.priority.toDouble()
                    )
                }


            var r =
                Random.nextDouble() *
                        total


            var selected =
                data.last()


            for (item in data) {

                r -=
                    max(
                        0.01,
                        item.priority.toDouble()
                    )


                if (r <= 0.0) {

                    selected = item

                    break
                }
            }


            selected
        }
    }


    @Synchronized
    fun size(): Int {

        return data.size
    }


    @Synchronized
    fun clear() {

        data.clear()
    }
}


/* ============================================================
 * 17. FAILURE MEMORY
 * ============================================================
 */

class V3FailureMemory(

    private val capacity: Int = 50000

) {


    private val memory =
        LinkedHashMap<Long, V3Lesson>()


    @Synchronized
    fun remember(

        contextHash: Long,

        action: V3Action,

        reason: V3DeathReason,

        penalty: Float,

        alternative: V3Action?

    ): V3Lesson {

        val old =
            memory[contextHash]


        if (old == null) {

            val lesson =
                V3Lesson(

                    contextHash =
                        contextHash,

                    badAction =
                        action,

                    reason =
                        reason,

                    penalty =
                        penalty.coerceIn(
                            0f,
                            10f
                        ),

                    confidence =
                        0.8f,

                    occurrences =
                        1,

                    alternative =
                        alternative
                )


            if (
                memory.size >=
                capacity
            ) {

                val iterator =
                    memory.entries.iterator()


                if (
                    iterator.hasNext()
                ) {

                    iterator.next()

                    iterator.remove()
                }
            }


            memory[
                contextHash
            ] =
                lesson


            return lesson
        }


        old.occurrences++


        old.penalty =
            (
                    old.penalty *
                            0.8f +
                            penalty *
                            0.2f
                    )
                .coerceIn(
                    0f,
                    10f
                )


        old.confidence =
            (
                    old.confidence +
                            0.03f
                    )
                .coerceIn(
                    0f,
                    1f
                )


        if (
            alternative != null
        ) {

            old.alternative =
                alternative
        }


        return old
    }


    @Synchronized
    fun actionPenalty(
        contextHash: Long,
        action: V3Action
    ): Float {

        val lesson =
            memory[
                contextHash
            ]
                ?: return 0f


        if (
            lesson.badAction !=
            action
        ) {

            return 0f
        }


        return lesson.penalty *
                lesson.confidence
    }


    @Synchronized
    fun occurrences(
        contextHash: Long
    ): Int {

        return memory[
            contextHash
        ]?.occurrences ?: 0
    }


    @Synchronized
    fun size(): Int {

        return memory.size
    }


    @Synchronized
    fun clear() {

        memory.clear()
    }
}


/* ============================================================
 * 18. GOAL SELECTOR
 * ============================================================
 */

class V3GoalSelector {


    fun select(
        state: V3State
    ): V3Goal {

        val legal =
            V3Board.legalActions(
                state
            )


        if (
            legal.isEmpty()
        ) {

            return V3Goal.ESCAPE_DANGER
        }


        /*
         * 检查循环。
         */
        val loop =
            state.recentHashes.size >= 6 &&
                    state.recentHashes
                        .takeLast(6)
                        .toSet()
                        .size <= 2


        if (loop) {

            return V3Goal.BREAK_LOOP
        }


        val spaceRatio =
            V3Board.freeSpace(
                state
            ).toFloat() /
                    max(
                        1,
                        state.cells
                    )


        /*
         * 空间太小。
         */
        if (
            spaceRatio < 0.25f ||
            legal.size == 1
        ) {

            return V3Goal.PRESERVE_SPACE
        }


        /*
         * 饥饿。
         */
        if (
            state.hunger > 0.75f &&
            state.food >= 0
        ) {

            return V3Goal.GET_FOOD
        }


        /*
         * 空间开始紧张，但尾巴可达。
         */
        if (
            spaceRatio < 0.45f &&
            V3Board.tailReachable(
                state
            ).first
        ) {

            return V3Goal.REACH_TAIL
        }


        /*
         * 正常情况下仍然追求食物。
         */
        if (
            state.food >= 0
        ) {

            return V3Goal.GET_FOOD
        }


        return V3Goal.SURVIVE
    }
}


/* ============================================================
 * 19. ACTION EVALUATOR
 * ============================================================
 */

class V3ActionEvaluator(

    private val qLearner: V3QLearner,

    private val brain: V3TinyBrain,

    private val encoder: V3StateEncoder,

    private val memory: V3FailureMemory

) {


    private fun normalize(
        values: FloatArray
    ): FloatArray {

        val maxAbs =
            max(
                1f,
                values.maxOfOrNull {
                    abs(it)
                } ?: 1f
            )


        return FloatArray(
            values.size
        ) {

            (
                    values[it] /
                            maxAbs
                    )
                .coerceIn(
                    -1f,
                    1f
                )
        }
    }


    fun evaluate(
        state: V3State,

        genome: V3StrategyGenome,

        goal: V3Goal

    ): List<V3ActionEvaluation> {


        val encoded =
            encoder.encode(
                state
            )


        val q =
            normalize(
                qLearner.values(
                    encoded.hash
                )
            )


        val brain =
            normalize(
                brain.forward(
                    encoded.values
                )
            )


        val currentSpace =
            V3Board.freeSpace(
                state
            ).toFloat() /
                    max(
                        1,
                        state.cells
                    )


        val currentTail =
            V3Board.tailReachable(
                state
            ).first


        return V3Action.values().map {

            action ->


            val immediateDeath =
                V3Board.immediateDeath(
                    state,
                    action
                )


            val next =
                if (
                    immediateDeath
                )
                    null
                else
                    V3Board.simulate(
                        state,
                        action
                    )


            /*
             * 空间价值。
             */
            val nextSpace =
                next?.let {

                    V3Board.freeSpace(
                        it
                    ).toFloat() /
                            max(
                                1,
                                it.cells
                            )

                } ?: 0f


            val spaceValue =
                (
                        nextSpace -
                                currentSpace
                        )
                    .coerceIn(
                        -1f,
                        1f
                    )


            /*
             * 尾巴价值。
             */
            val nextTail =
                next?.let {

                    V3Board.tailReachable(
                        it
                    ).first

                } ?: false


            val tailValue =
                when {

                    nextTail &&
                            !currentTail ->
                        0.25f

                    nextTail ->
                        0.10f

                    currentTail &&
                            !nextTail ->
                        -0.35f

                    else ->
                        -0.05f
                }


            /*
             * 食物价值。
             */
            val foodValue =
                if (
                    state.food >= 0 &&
                    next != null
                ) {

                    val hx =
                        state.head %
                                state.width

                    val hy =
                        state.head /
                                state.width

                    val fx =
                        state.food %
                                state.width

                    val fy =
                        state.food /
                                state.width

                    val nx =
                        next.head %
                                next.width

                    val ny =
                        next.head /
                                next.width


                    val before =
                        abs(
                            hx - fx
                        ) +
                                abs(
                                    hy - fy
                                )


                    val after =
                        abs(
                            nx - fx
                        ) +
                                abs(
                                    ny - fy
                                )


                    (
                            (
                                    before -
                                            after
                                    ) *
                                    0.12f
                            )
                        .coerceIn(
                            -1f,
                            1f
                        )

                } else {

                    0f
                }


            /*
             * 危险价值。
             */
            val dangerValue =
                when {

                    immediateDeath ->
                        1f

                    next == null ->
                        1f

                    V3Board.legalActions(
                        next
                    ).isEmpty() ->
                        1f

                    V3Board.legalActions(
                        next
                    ).size <= 1 ->
                        0.65f

                    V3Board.legalActions(
                        next
                    ).size == 2 ->
                        0.25f

                    else ->
                        0f
                }


            /*
             * Loop。
             */
            val loopValue =
                if (
                    state.recentHashes.size >= 4 &&
                    state.recentHashes
                        .takeLast(4)
                        .toSet()
                        .size <= 2
                )
                    0.7f
                else
                    0f


            /*
             * Counterfactual。
             *
             * 如果走了这个动作，
             * 下一步还有没有好的选择？
             */
            val counterfactualValue =
                if (
                    next == null
                ) {

                    -1f

                } else {

                    val future =
                        V3Board.legalActions(
                            next
                        )


                    if (
                        future.isEmpty()
                    ) {

                        -1f

                    } else {

                        val bestFuture =
                            future.maxOf {

                                val futureState =
                                    V3Board.simulate(
                                        next,
                                        it
                                    )


                                if (
                                    futureState == null
                                ) {

                                    -1f

                                } else {

                                    V3Board.freeSpace(
                                        futureState
                                    ).toFloat() /
                                            max(
                                                1,
                                                futureState.cells
                                            )
                                }
                            }


                        (
                                bestFuture * 2f -
                                        1f
                                )
                    }
                }


            /*
             * 长期失败记忆。
             */
            val memoryPenalty =
                memory.actionPenalty(
                    encoded.hash,
                    action
                )


            /*
             * 当前目标额外价值。
             */
            val goalBonus =
                when (goal) {

                    V3Goal.GET_FOOD ->
                        foodValue * 0.35f

                    V3Goal.PRESERVE_SPACE ->
                        spaceValue * 0.45f

                    V3Goal.REACH_TAIL ->
                        tailValue * 0.45f

                    V3Goal.ESCAPE_DANGER ->
                        -dangerValue * 0.45f +
                                spaceValue * 0.25f

                    V3Goal.BREAK_LOOP ->
                        -loopValue * 0.45f +
                                spaceValue * 0.15f

                    V3Goal.SURVIVE ->
                        spaceValue * 0.15f -
                                dangerValue * 0.15f
                }


            /*
             * 学习价值。
             */
            val learned =
                q[action.ordinal] *
                        genome.1.0f +

                        brain[action.ordinal] *
                        genome.brainWeight


            /*
             * 最终价值。
             *
             * 注意：
             *
             * 没有：
             *
             * if food -> force food
             *
             * if danger -> force tail
             *
             * 所有东西都统一进入价值函数。
             */
            val finalValue =
                learned +

                        genome.foodPriority *
                        foodValue +

                        genome.spacePriority *
                        spaceValue +

                        genome.tailPriority *
                        tailValue +

                        if (
                            state.hunger > 0.7f
                        )
                            genome.hungerUrgency *
                                    foodValue *
                                    0.3f
                        else
                            0f +

                        goalBonus +

                        counterfactualValue *
                        0.35f -

                        genome.dangerAversion *
                        dangerValue -

                        genome.loopAversion *
                        loopValue -

                        memoryPenalty


            V3ActionEvaluation(

                action = action,

                qValue =
                    q[action.ordinal],

                brainValue =
                    brain[action.ordinal],

                foodValue =
                    foodValue,

                spaceValue =
                    spaceValue,

                tailValue =
                    tailValue,

                dangerValue =
                    dangerValue,

                loopValue =
                    loopValue,

                counterfactualValue =
                    counterfactualValue,

                memoryPenalty =
                    memoryPenalty,

                finalValue =
                    if (
                        immediateDeath
                    )
                        -Float.MAX_VALUE
                    else
                        finalValue,

                immediateDeath =
                    immediateDeath
            )
        }
    }
}


/* ============================================================
 * 20. REWARD ENGINE
 * ============================================================
 */

class V3RewardEngine {


    fun reward(

        before: V3State?,

        after: V3State,

        ateFood: Boolean,

        died: Boolean

    ): Float {


        if (died) {

            return -15f
        }


        if (ateFood) {

            return 10f
        }


        if (before == null) {

            return 0.005f
        }


        var reward =
            0.005f


        /*
         * 食物进度。
         */
        if (
            before.food >= 0 &&
            after.food >= 0
        ) {

            val bx =
                before.head %
                        before.width

            val by =
                before.head /
                        before.width


            val ax =
                after.head %
                        after.width

            val ay =
                after.head /
                        after.width


            val fx =
                before.food %
                        before.width

            val fy =
                before.food /
                        before.width


            val oldDistance =
                abs(
                    bx - fx
                ) +
                        abs(
                            by - fy
                        )


            val newDistance =
                abs(
                    ax - fx
                ) +
                        abs(
                            ay - fy
                        )


            reward +=
                (
                        (
                                oldDistance -
                                        newDistance
                                ) *
                                0.08f
                        )
                    .coerceIn(
                        -0.2f,
                        0.2f
                    )
        }


        /*
         * 空间奖励必须使用 Delta。
         */
        val oldSpace =
            V3Board.freeSpace(
                before
            )


        val newSpace =
            V3Board.freeSpace(
                after
            )


        reward +=
            (
                    (
                            newSpace -
                                    oldSpace
                            ) *
                            0.015f
                    )
                .coerceIn(
                    -0.15f,
                    0.15f
                )


        /*
         * 尾巴可达性。
         */
        val oldTail =
            V3Board.tailReachable(
                before
            ).first


        val newTail =
            V3Board.tailReachable(
                after
            ).first


        if (
            !oldTail &&
            newTail
        ) {

            reward +=
                0.12f
        }


        if (
            oldTail &&
            !newTail
        ) {

            reward -=
                0.12f
        }


        /*
         * 未来选择变少。
         */
        if (
            V3Board.legalActions(
                after
            ).size <= 1
        ) {

            reward -=
                0.08f
        }


        /*
         * Hunger。
         */
        reward -=
            min(
                0.15f,
                after.hunger *
                        after.hunger *
                        0.001f
            )


        return reward.coerceIn(
            -2f,
            10f
        )
    }
}


/* ============================================================
 * 21. DEATH ANALYZER
 * ============================================================
 */

class V3DeathAnalyzer(

    private val encoder: V3StateEncoder

) {


    fun analyze(

        before: V3State,

        action: V3Action,

        chosenValue: Float,

        evaluations:
            List<V3ActionEvaluation>

    ): V3DeathReport {


        val legal =
            V3Board.legalActions(
                before
            )


        val foodDistance =
            if (
                before.food >= 0
            ) {

                val hx =
                    before.head %
                            before.width

                val hy =
                    before.head /
                            before.width


                val fx =
                    before.food %
                            before.width

                val fy =
                    before.food /
                            before.width


                abs(
                    hx - fx
                ) +
                        abs(
                            hy - fy
                        )

            } else {

                0
            }


        /*
         * 先判断最直接的死亡原因。
         */
        val reason =
            when {

                V3Board.step(
                    before,
                    before.head,
                    action
                ) < 0 -> {

                    V3DeathReason.HIT_WALL
                }


                V3Board.immediateDeath(
                    before,
                    action
                ) -> {

                    val next =
                        V3Board.step(
                            before,
                            before.head,
                            action
                        )


                    if (
                        next == before.tail
                    )
                        V3DeathReason.DEAD_END
                    else
                        V3DeathReason.HIT_SELF
                }


                legal.isEmpty() -> {

                    V3DeathReason.TRAPPED
                }


                else -> {

                    val space =
                        V3Board.freeSpace(
                            before
                        )


                    val tail =
                        V3Board.tailReachable(
                            before
                        ).first


                    val loop =
                        before.recentHashes.size >= 6 &&
                                before.recentHashes
                                    .takeLast(6)
                                    .toSet()
                                    .size <= 2


                    when {

                        loop ->
                            V3DeathReason.LOOP

                        space <
                                before.body.size * 2 ->
                            V3DeathReason.SPACE_COLLAPSE

                        !tail &&
                                before.body.size > 8 ->
                            V3DeathReason.TAIL_CUTOFF

                        before.hunger > 0.85f ->
                            V3DeathReason.HUNGER

                        else ->
                            V3DeathReason.UNKNOWN
                    }
                }
            }


        /*
         * Counterfactual：
         *
         * 如果当时选别的动作，
         * 有没有活路？
         */
        val alternatives =
            evaluations
                .filter {
                    !it.immediateDeath &&
                            it.action != action
                }
                .sortedByDescending {
                    it.finalValue
                }


        val best =
            alternatives.firstOrNull()


        val regret =
            if (
                best != null
            ) {

                max(
                    0f,
                    best.finalValue -
                            chosenValue
                )

            } else {

                0f
            }


        return V3DeathReport(

            reason =
                reason,

            action =
                action,

            stateHash =
                encoder.encode(
                    before
                ).hash,

            avoidable =
                best != null,

            bestAlternative =
                best?.action,

            regret =
                regret,

            freeSpace =
                V3Board.freeSpace(
                    before
                ),

            safeActions =
                legal.size,

            tailReachable =
                V3Board.tailReachable(
                    before
                ).first,

            foodDistance =
                foodDistance,

            repeatedFailure =
                0
        )
    }
}


/* ============================================================
 * 22. TRAINING STATS
 * ============================================================
 */

data class V3TrainingStats(

    var generation: Int = 0,

    var agent: Int = 0,

    var score: Int = 0,

    var bestScore: Int = 0,

    var averageScore: Float = 0f,

    var fitness: Float = 0f,

    var epsilon: Float = 1f,

    var replaySize: Int = 0,

    var memorySize: Int = 0,

    var learningSteps: Long = 0,

    var meanTdError: Float = 0f,

    var lessonsLearned: Long = 0,

    var avoidableDeaths: Long = 0,

    var lastDeathReason:
        V3DeathReason? = null,

    var lastGoal:
        V3Goal = V3Goal.SURVIVE
)


/* ============================================================
 * 23. SHARED LEARNING
 * ============================================================
 *
 * 50 Agent 可以共享：
 *
 * Q
 * Replay
 *
 * 每个 Agent 自己拥有：
 *
 * Brain
 * Genome
 * FailureMemory
 *
 */

class V3SharedLearning(

    val qLearner:
        V3QLearner = V3QLearner(),

    val replay:
        V3ReplayBuffer =
            V3ReplayBuffer()

)


/* ============================================================
 * 24. MAIN AI ENGINE
 * ============================================================
 */

class AIEngineV3(

    val shared:
        V3SharedLearning =
            V3SharedLearning()

) {


    /*
     * AI 的核心组件。
     */
    val encoder =
        V3StateEncoder()


    val brain =
        V3TinyBrain()


    val genome =
        V3StrategyGenome()


    val failureMemory =
        V3FailureMemory()


    val stats =
        V3TrainingStats()


    private val rewardEngine =
        V3RewardEngine()


    private val goalSelector =
        V3GoalSelector()


    private val evaluator =
        V3ActionEvaluator(

            shared.qLearner,

            brain,

            encoder,

            failureMemory
        )


    private val deathAnalyzer =
        V3DeathAnalyzer(
            encoder
        )


    /*
     * 当前 episode 的 pending state。
     */
    private var previousState:
        V3State? = null


    private var lastAction:
        V3Action? = null


    private var lastDecision:
        V3Decision? = null


    private var lastChosenValue:
        Float = 0f


    /*
     * 最近决策。
     *
     * 用来做因果责任追踪。
     */
    private val decisionHistory =
        ArrayDeque<Pair<Long, V3Action>>()


    /*
     * 训练模式。
     */
    var trainingEnabled =
        false
        private set


    /*
     * Exploration。
     */
    var epsilon =
        1f
        private set


    /*
     * --------------------------------------------------------
     * RESET
     * --------------------------------------------------------
     */

    fun resetEpisode() {

        previousState =
            null

        lastAction =
            null

        lastDecision =
            null

        lastChosenValue =
            0f

        decisionHistory.clear()
    }


    /*
     * --------------------------------------------------------
     * ACT
     * --------------------------------------------------------
     *
     * SnakeView 调用：
     *
     * val action = ai.act(state)
     *
     */

    fun act(
        state: V3State
    ): V3Action {


        /*
         * 1.
         * 判断当前目标。
         */
        val goal =
            goalSelector.select(
                state
            )


        /*
         * 2.
         * 评价所有动作。
         */
        val evaluations =
            evaluator.evaluate(
                state,
                genome,
                goal
            )


        /*
         * 3.
         * Safety：
         *
         * 只有马上死亡的动作被过滤。
         */
        val safe =
            evaluations.filter {
                !it.immediateDeath
            }


        val candidates =
            if (
                safe.isNotEmpty()
            )
                safe
            else
                evaluations


        /*
         * 4.
         * Exploration。
         *
         * 不是完全随机。
         *
         * 从当前最好的前三个安全动作里探索。
         */
        val explorationProbability =
            (
                    epsilon *
                            genome.explorationBias
                    )
                .coerceIn(
                    0.01f,
                    0.9f
                )


        val explored =
            trainingEnabled &&
                    Random.nextFloat() <
                    explorationProbability


        val selected =
            if (
                explored
            ) {

                val top =
                    candidates
                        .sortedByDescending {
                            it.finalValue
                        }
                        .take(
                            min(
                                3,
                                candidates.size
                            )
                        )


                top.random()

            } else {

                candidates.maxByOrNull {
                    it.finalValue
                }!!
            }


        /*
         * 5.
         * 保存本次决策。
         */
        lastAction =
            selected.action


        lastChosenValue =
            selected.finalValue


        previousState =
            state


        lastDecision =
            V3Decision(

                action =
                    selected.action,

                goal =
                    goal,

                evaluations =
                    evaluations,

                explored =
                    explored
            )


        /*
         * 6.
         * 记录最近行为。
         */
        decisionHistory.addLast(

            Pair(
                encoder.encode(
                    state
                ).hash,

                selected.action
            )
        )


        while (
            decisionHistory.size > 12
        ) {

            decisionHistory.removeFirst()
        }


        stats.lastGoal =
            goal


        return selected.action
    }


    /*
     * --------------------------------------------------------
     * FEEDBACK
     * --------------------------------------------------------
     *
     * 游戏执行动作之后：
     *
     * ai.feedback(
     *     nextState,
     *     ateFood,
     *     gameOver
     * )
     *
     */

    fun feedback(

        nextState: V3State,

        ateFood: Boolean = false,

        died: Boolean =
            nextState.gameOver

    ) {


        val action =
            lastAction
                ?: return


        val before =
            previousState


        /*
         * Reward。
         */
        val reward =
            rewardEngine.reward(

                before,

                nextState,

                ateFood,

                died
            )


        /*
         * State Encoding。
         */
        val beforeEncoded =
            encoder.encode(
                before ?: nextState
            )


        val afterEncoded =
            if (died)
                null
            else
                encoder.encode(
                    nextState
                )


        /*
         * 死亡分析。
         */
        var deathReason:
            V3DeathReason? =
            null


        if (
            died &&
            before != null
        ) {


            val report =
                deathAnalyzer.analyze(

                    before,

                    action,

                    lastChosenValue,

                    lastDecision?.evaluations
                        ?: emptyList()
                )


            deathReason =
                report.reason


            /*
             * 真正学习：
             *
             * 为什么死？
             */
            learnFromDeath(
                report
            )


            /*
             * 因果责任：
             *
             * 最近几步也受到处罚。
             */
            applyCausalCredit(
                report
            )
        }


        /*
         * 经验。
         */
        val experience =
            V3Experience(

                state =
                    beforeEncoded,

                action =
                    action,

                reward =
                    reward,

                nextState =
                    afterEncoded,

                done =
                    died,

                deathReason =
                    deathReason,

                priority =
                    if (died)
                        8f
                    else
                        1f,

                nextLegalMask =
                    if (!died) {
                        BooleanArray(V3Action.values().size).also { mask ->
                            for (a in V3Board.legalActions(nextState)) {
                                mask[a.ordinal] = true
                            }
                        }
                    } else null
            )


        /*
         * Training。
         */
        if (
            trainingEnabled
        ) {


            /*
             * Replay。
             */
            shared.replay.add(
                experience
            )


            /*
             * 当前经验立即学习。
             */
            shared.qLearner.learn(
                experience
            )


            /*
             * Replay 学习。
             */
            val batch =
                shared.replay.sample(
                    8
                )


            for (
                item in batch
            ) {

                shared.qLearner.learn(
                    item
                )
            }


            /*
             * Brain 更新。
             */
            val target =
                reward.coerceIn(
                    -10f,
                    10f
                )


            brain.train(

                beforeEncoded.values,

                action.ordinal,

                target
            )


            stats.learningSteps =
                shared.qLearner.learningSteps


            stats.meanTdError =
                shared.qLearner.meanTdError


            stats.replaySize =
                shared.replay.size()
        }


        /*
         * Exploration 逐渐降低。
         */
        if (
            trainingEnabled
        ) {

            epsilon =
                max(
                    0.03f,
                    epsilon * 0.9995f
                )


            stats.epsilon =
                epsilon
        }


        /*
         * Target Network 定期同步。
         */
        if (
            shared.qLearner.learningSteps > 0 &&
            shared.qLearner.learningSteps %
            2000L == 0L
        ) {

            shared.qLearner.syncTarget()
        }


        stats.lastDeathReason =
            deathReason


        stats.memorySize =
            failureMemory.size()


        /*
         * Episode 结束。
         */
        if (died) {

            previousState =
                null

            lastAction =
                null

        } else {

            previousState =
                nextState
        }
    }


    /*
     * --------------------------------------------------------
     * LEARN FROM DEATH
     * --------------------------------------------------------
     */

    private fun learnFromDeath(

        report:
            V3DeathReport

    ) {


        val action =
            report.action
                ?: return


        /*
         * 判断是不是重复错误。
         */
        val repeated =
            failureMemory.occurrences(
                report.stateHash
            ) > 0


        /*
         * 不同死亡原因，
         * 有不同的长期惩罚。
         */
        val basePenalty =
            when (
                report.reason
            ) {

                V3DeathReason.HIT_WALL,
                V3DeathReason.HIT_SELF ->
                    4f

                V3DeathReason.TRAPPED ->
                    3f

                V3DeathReason.DEAD_END ->
                    2.5f

                V3DeathReason.SPACE_COLLAPSE ->
                    3f

                V3DeathReason.TAIL_CUTOFF ->
                    2.5f

                V3DeathReason.LOOP ->
                    1.5f

                V3DeathReason.HUNGER ->
                    1.5f

                V3DeathReason.UNKNOWN ->
                    0.5f
            }


        /*
         * 如果存在更好的反事实动作，
         * 增加 regret 惩罚。
         */
        val penalty =
            basePenalty +
                    min(
                        2f,
                        report.regret
                    )


        /*
         * 长期记忆。
         */
        failureMemory.remember(

            contextHash =
                report.stateHash,

            action =
                action,

            reason =
                report.reason,

            penalty =
                penalty,

            alternative =
                report.bestAlternative
        )


        /*
         * 策略自调整。
         */
        genome.selfAdjust(

            reason =
                report.reason,

            repeated =
                repeated,

            avoidable =
                report.avoidable
        )


        if (
            report.avoidable
        ) {

            stats.avoidableDeaths++
        }


        stats.lessonsLearned++


        stats.memorySize =
            failureMemory.size()
    }


    /*
     * --------------------------------------------------------
     * CAUSAL CREDIT
     * --------------------------------------------------------
     *
     * 不只处罚最后一步。
     *
     * 越接近死亡：
     *   责任越大。
     *
     */

    private fun applyCausalCredit(

        report:
            V3DeathReport

    ) {


        var weight =
            1f


        /*
         * 当前实现把因果责任
         * 转换为长期记忆。
         *
         * 未来相同上下文出现时，
         * 该动作会得到额外惩罚。
         */
        val history =
            decisionHistory.toList()


        for (
            i in history.indices.reversed()
        ) {


            val record =
                history[i]


            val contextHash =
                record.first


            val action =
                record.second


            failureMemory.remember(

                contextHash =
                    contextHash,

                action =
                    action,

                reason =
                    report.reason,

                penalty =
                    when {

                        weight > 0.7f ->
                            0.8f

                        weight > 0.45f ->
                            0.5f

                        weight > 0.25f ->
                            0.25f

                        else ->
                            0.1f
                    },

                alternative =
                    report.bestAlternative
            )


            weight *=
                0.70f
        }
    }


    /*
     * --------------------------------------------------------
     * EVOLUTION HELPERS
     * --------------------------------------------------------
     */

    fun copyForEvolution():
            AIEngineV3 {


        val child =
            AIEngineV3(
                shared
            )


        /*
         * Genome 深拷贝。
         */
        val g =
            genome.deepCopy()


        child.genome.foodPriority =
            g.foodPriority

        child.genome.spacePriority =
            g.spacePriority

        child.genome.tailPriority =
            g.tailPriority

        child.genome.dangerAversion =
            g.dangerAversion

        child.genome.loopAversion =
            g.loopAversion

        child.genome.hungerUrgency =
            g.hungerUrgency

        child.genome.explorationBias =
            g.explorationBias

        child.genome.1.0f =
            g.1.0f

        child.genome.brainWeight =
            g.brainWeight

        child.genome.mutationRate =
            g.mutationRate

        child.genome.mutationSigma =
            g.mutationSigma

        child.genome.lookaheadDepth =
            g.lookaheadDepth


        /*
         * Brain 深拷贝。
         */
        child.brain.copyFrom(
            brain
        )


        child.trainingEnabled =
            trainingEnabled


        child.epsilon =
            epsilon


        child.resetEpisode()


        return child
    }


    /*
     * 对自身进行基因 + Brain 突变。
     */
    fun mutate(
        strength: Float = 1f
    ) {

        genome.mutate(
            strength
        )


        brain.mutate(
            genome.mutationSigma *
                    strength
        )
    }


    fun setTraining(
        enabled: Boolean
    ) {

        trainingEnabled =
            enabled
    }


    fun setGeneration(
        generation: Int
    ) {

        stats.generation =
            generation
    }


    fun lastDecision():
            V3Decision? {

        return lastDecision
    }


    fun lastDeathReason():
            V3DeathReason? {

        return stats.lastDeathReason
    }
}


/* ============================================================
 * 25. EVOLUTION RESULT
 * ============================================================
 */

data class V3AgentResult(

    val agent: AIEngineV3,

    val fitness: Float,

    val score: Int,

    val food: Int,

    val survivalSteps: Int,

    val deathReason:
        V3DeathReason?

)


/* ============================================================
 * 26. EVOLUTION MANAGER
 * ============================================================
 */

object V3EvolutionManager {


    /*
     * Fitness。
     */
    fun fitness(

        score: Int,

        food: Int,

        survivalSteps: Int,

        length: Int,

        deathReason:
            V3DeathReason?

    ): Float {


        val deathPenalty =
            when (
                deathReason
            ) {

                V3DeathReason.HIT_WALL,
                V3DeathReason.HIT_SELF ->
                    8f

                V3DeathReason.TRAPPED,
                V3DeathReason.SPACE_COLLAPSE ->
                    6f

                V3DeathReason.DEAD_END,
                V3DeathReason.TAIL_CUTOFF ->
                    5f

                V3DeathReason.LOOP ->
                    3f

                V3DeathReason.HUNGER ->
                    2f

                V3DeathReason.UNKNOWN,
                null ->
                    1f
            }


        return score * 1f +

                food * 2f +

                survivalSteps *
                0.01f +

                length *
                0.2f -

                deathPenalty
    }


    /*
     * 一代进化。
     *
     * 例如 50 Agent：
     *
     * 5 Elite
     * 45 新 Agent
     */
    fun evolve(

        population:
            List<V3AgentResult>,

        generation: Int,

        eliteCount: Int = 5

    ): List<AIEngineV3> {


        require(
            population.isNotEmpty()
        )


        /*
         * 内部按照 fitness 选择父代。
         */
        val sorted =
            population.sortedByDescending {
                it.fitness
            }


        val elites =
            sorted
                .take(
                    min(
                        eliteCount,
                        sorted.size
                    )
                )
                .map {
                    it.agent.copyForEvolution()
                }


        val shared =
            elites.firstOrNull()?.shared
                ?: V3SharedLearning()


        val next =
            ArrayList<AIEngineV3>()


        /*
         * Elite 原样继承。
         */
        for (
            elite in elites
        ) {

            elite.setGeneration(
                generation + 1
            )

            elite.setTraining(
                true
            )

            next.add(
                elite
            )
        }


        /*
         * 产生孩子。
         */
        while (
            next.size <
            population.size
        ) {


            val parentA =
                elites.random()


            val parentB =
                elites.random()


            val child =
                AIEngineV3(
                    shared
                )


            /*
             * Genome crossover。
             */
            val genome =
                parentA.genome
                    .crossover(
                        parentB.genome
                    )


            child.genome.foodPriority =
                genome.foodPriority

            child.genome.spacePriority =
                genome.spacePriority

            child.genome.tailPriority =
                genome.tailPriority

            child.genome.dangerAversion =
                genome.dangerAversion

            child.genome.loopAversion =
                genome.loopAversion

            child.genome.hungerUrgency =
                genome.hungerUrgency

            child.genome.explorationBias =
                genome.explorationBias

            child.genome.1.0f =
                genome.1.0f

            child.genome.brainWeight =
                genome.brainWeight

            child.genome.mutationRate =
                genome.mutationRate

            child.genome.mutationSigma =
                genome.mutationSigma

            child.genome.lookaheadDepth =
                genome.lookaheadDepth


            /*
             * Brain crossover：
             *
             * 当前版本随机继承一个父代 Brain，
             * 再进行 mutation。
             */
            val selectedBrain =
                if (
                    Random.nextBoolean()
                )
                    parentA.brain
                else
                    parentB.brain


            child.brain.copyFrom(
                selectedBrain
            )


            /*
             * 20% 的孩子使用更大的突变，
             * 保持种群多样性。
             */
            val mutationScale =
                if (
                    Random.nextFloat() <
                    0.20f
                )
                    1.8f
                else
                    1f


            child.mutate(
                mutationScale
            )


            child.setGeneration(
                generation + 1
            )


            child.setTraining(
                true
            )


            next.add(
                child
            )
        }


        return next
    }
}


/* ============================================================
 * 27. SIMPLE ADAPTER
 * ============================================================
 *
 * 这个 Adapter 是给 SnakeView 嵌套用的。
 *
 * 不要让 AI 修改 SnakeView。
 *
 * SnakeView 只需要：
 *
 * 1. 把自己的游戏状态转换成 V3State
 * 2. 调用 decide()
 * 3. 执行返回动作
 * 4. 把结果再反馈给 AI
 *
 */

class SnakeAIV3Adapter(

    val ai:
        AIEngineV3

) {


    fun decide(
        state: V3State
    ): V3Action {

        return ai.act(
            state
        )
    }


    fun feedback(

        nextState:
            V3State,

        ateFood: Boolean,

        gameOver: Boolean

    ) {

        ai.feedback(

            nextState =
                nextState,

            ateFood =
                ateFood,

            died =
                gameOver
        )
    }


    fun reset() {

        ai.resetEpisode()
    }
}


/* ============================================================
 * 28. END
 * ============================================================
 *
 * AI V3 的核心闭环：
 *
 *   观察
 *     ↓
 *   Goal
 *     ↓
 *   Q
 *     +
 *   Brain
 *     +
 *   Food
 *     +
 *   Space
 *     +
 *   Tail
 *     +
 *   Counterfactual
 *     -
 *   Danger
 *     -
 *   Loop
 *     -
 *   Failure Memory
 *     ↓
 *   Action
 *     ↓
 *   游戏执行
 *     ↓
 *   Reward
 *     ↓
 *   Death Analyzer
 *     ↓
 *   Lesson
 *     ↓
 *   Memory
 *     ↓
 *   Genome Self Adjustment
 *     ↓
 *   Evolution
 *
 * ============================================================
 */

}
