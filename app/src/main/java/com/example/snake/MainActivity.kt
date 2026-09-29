package com.example.snake

import android.app.AlertDialog
import android.content.Context
import android.graphics.Color
import android.os.Bundle
import android.view.Gravity
import android.view.WindowManager
import android.widget.Button
import android.widget.FrameLayout
import android.widget.LinearLayout
import android.widget.TextView
import android.widget.Toast
import androidx.appcompat.app.AppCompatActivity
import java.io.File
import java.text.SimpleDateFormat
import java.util.Date
import java.util.Locale

class MainActivity : AppCompatActivity() {

    companion object {

        private const val CRASH_FILE = "last_crash.txt"

        private fun installCrashHandler(context: Context) {

            val appContext = context.applicationContext

            val oldHandler =
                Thread.getDefaultUncaughtExceptionHandler()

            Thread.setDefaultUncaughtExceptionHandler {
                    thread,
                    throwable ->

                try {

                    val time =
                        SimpleDateFormat(
                            "yyyy-MM-dd HH:mm:ss",
                            Locale.getDefault()
                        ).format(Date())

                    val file =
                        File(
                            appContext.filesDir,
                            CRASH_FILE
                        )

                    val text =
                        buildString {

                            append(
                                "================================\n"
                            )

                            append(
                                "        SNAKE 崩溃诊断日志\n"
                            )

                            append(
                                "================================\n\n"
                            )

                            append("时间:\n")
                            append(time)
                            append("\n\n")

                            append("线程:\n")
                            append(thread.name)
                            append("\n\n")

                            append("异常类型:\n")
                            append(
                                throwable.javaClass.name
                            )
                            append("\n\n")

                            append("异常信息:\n")
                            append(
                                throwable.message ?: "无"
                            )
                            append("\n\n")

                            append(
                                "========== STACK TRACE ==========\n"
                            )

                            append(
                                throwable.stackTraceToString()
                            )

                            var cause =
                                throwable.cause

                            var level = 1

                            while (cause != null) {

                                append(
                                    "\n\n========== CAUSE $level ==========\n"
                                )

                                append(
                                    cause.stackTraceToString()
                                )

                                cause = cause.cause
                                level++
                            }
                        }

                    file.writeText(text)

                } catch (_: Throwable) {
                    // 崩溃记录本身不能导致第二次崩溃
                }

                try {

                    oldHandler?.uncaughtException(
                        thread,
                        throwable
                    )

                } catch (_: Throwable) {
                }
            }
        }

        private fun getCrashFile(
            context: Context
        ): File {

            return File(
                context.applicationContext.filesDir,
                CRASH_FILE
            )
        }

        private fun readCrashLog(
            context: Context
        ): String? {

            return try {

                val file =
                    getCrashFile(context)

                if (file.exists()) {
                    file.readText()
                } else {
                    null
                }

            } catch (_: Throwable) {

                null
            }
        }

        private fun deleteCrashLog(
            context: Context
        ) {

            try {

                getCrashFile(context).delete()

            } catch (_: Throwable) {
            }
        }
    }

    private var gameView: SnakeView? = null

    private var scoreView: TextView? = null

    private var moneyView: TextView? = null

    private var aiBtn: Button? = null

    private var autoBtn: Button? = null

    private var bfsBtn: Button? = null

    private var tailBtn: Button? = null

    private var hamBtn: Button? = null

    private var beamBtn: Button? = null

    private lateinit var prefs:
        android.content.SharedPreferences

    private var forcedStrategy = -1

    private var aiOn = true

    override fun onCreate(
        savedInstanceState: Bundle?
    ) {

        installCrashHandler(
            applicationContext
        )

        super.onCreate(
            savedInstanceState
        )

        val previousCrash =
            readCrashLog(
                applicationContext
            )

        try {

            window.addFlags(
                WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON
            )

            prefs =
                getSharedPreferences(
                    "snake_prefs",
                    Context.MODE_PRIVATE
                )

            forcedStrategy =
                prefs.getInt(
                    "forced_strategy",
                    -1
                )

            aiOn =
                prefs.getBoolean(
                    "ai_on",
                    true
                )

            // ========================================
            // 创建游戏
            // ========================================

            gameView =
                SnakeView(this)

            gameView?.setAIMode(
                if (aiOn) 1 else 0
            )

            gameView?.setForcedStrategy(
                forcedStrategy
            )

            // ========================================
            // 第一行：分数 / 金币 / 商店
            // ========================================

            val row1 =
                LinearLayout(this).apply {

                    orientation =
                        LinearLayout.HORIZONTAL

                    setPadding(
                        12,
                        12,
                        12,
                        4
                    )

                    gravity =
                        Gravity.CENTER_VERTICAL
                }

            scoreView =
                TextView(this).apply {

                    text =
                        "分数: 0"

                    textSize =
                        14f

                    setTextColor(
                        Color.WHITE
                    )
                }

            moneyView =
                TextView(this).apply {

                    text =
                        "金币: ${
                            prefs.getInt(
                                "money",
                                0
                            )
                        }"

                    textSize =
                        14f

                    setTextColor(
                        Color.rgb(
                            241,
                            196,
                            15
                        )
                    )

                    setPadding(
                        14,
                        0,
                        0,
                        0
                    )
                }

            val shop =
                Button(this).apply {

                    text = "🛒"

                    textSize =
                        12f

                    setTextColor(
                        Color.WHITE
                    )

                    setPadding(
                        8,
                        0,
                        8,
                        0
                    )

                    setBackgroundColor(
                        Color.rgb(
                            46,
                            204,
                            113
                        )
                    )

                    setOnClickListener {

                        showShopCategoryDialog()
                    }
                }

            val spacer =
                FrameLayout(this).apply {

                    layoutParams =
                        LinearLayout.LayoutParams(
                            0,
                            1,
                            1f
                        )
                }

            row1.addView(
                scoreView
            )

            row1.addView(
                moneyView
            )

            row1.addView(
                spacer
            )

            row1.addView(
                shop
            )

            // ========================================
            // 第二行：策略 + AI
            // ========================================

            val row2 =
                LinearLayout(this).apply {

                    orientation =
                        LinearLayout.HORIZONTAL

                    setPadding(
                        6,
                        0,
                        6,
                        6
                    )

                    gravity =
                        Gravity.CENTER_VERTICAL
                }

            autoBtn =
                makeStrategyBtn(
                    "自动"
                ) {

                    setForcedStrategy(
                        -1
                    )
                }

            bfsBtn =
                makeStrategyBtn(
                    "BFS"
                ) {

                    setForcedStrategy(
                        0
                    )
                }

            tailBtn =
                makeStrategyBtn(
                    "追尾"
                ) {

                    setForcedStrategy(
                        1
                    )
                }

            hamBtn =
                makeStrategyBtn(
                    "HAM"
                ) {

                    setForcedStrategy(
                        2
                    )
                }

            /*
             * 策略编号：
             *
             * -1 = 自动
             *  0 = BFS
             *  1 = 追尾
             *  2 = HAM
             *  3 = BEAM
             */

            beamBtn =
                makeStrategyBtn(
                    "BEAM"
                ) {

                    setForcedStrategy(
                        3
                    )
                }

            // ========================================
            // AI ON / OFF
            // ========================================

            aiBtn =
                Button(this).apply {

                    textSize =
                        11f

                    setTextColor(
                        Color.WHITE
                    )

                    setPadding(
                        4,
                        0,
                        4,
                        0
                    )

                    layoutParams =
                        LinearLayout.LayoutParams(
                            0,
                            -2,
                            1.25f
                        )

                    updateAiButton()

                    setOnClickListener {

                        aiOn =
                            !aiOn

                        prefs.edit()
                            .putBoolean(
                                "ai_on",
                                aiOn
                            )
                            .apply()

                        gameView?.setAIMode(
                            if (aiOn) 1 else 0
                        )

                        updateAiButton()
                    }
                }

            row2.addView(
                autoBtn
            )

            row2.addView(
                bfsBtn
            )

            row2.addView(
                tailBtn
            )

            row2.addView(
                hamBtn
            )

            row2.addView(
                beamBtn
            )

            row2.addView(
                aiBtn
            )

            // ========================================
            // 顶部区域
            // ========================================

            val top =
                LinearLayout(this).apply {

                    orientation =
                        LinearLayout.VERTICAL

                    addView(
                        row1
                    )

                    addView(
                        row2
                    )
                }

            // ========================================
            // 游戏回调
            // ========================================

            gameView?.onScoreChanged =
                { s ->

                    runOnUiThread {

                        scoreView?.text =
                            "分数: $s"
                    }
                }

            gameView?.onMoneyChanged =
                { m ->

                    runOnUiThread {

                        moneyView?.text =
                            "金币: $m"
                    }
                }

            updateButtons()

            // ========================================
            // 根布局
            // ========================================

            val root =
                FrameLayout(this).apply {

                    setBackgroundColor(
                        Color.BLACK
                    )
                }

            root.addView(
                gameView,
                FrameLayout.LayoutParams(
                    -1,
                    -1
                )
            )

            root.addView(
                top,
                FrameLayout.LayoutParams(
                    -1,
                    -2,
                    Gravity.TOP
                )
            )

            setContentView(
                root
            )

            // ========================================
            // 显示之前的崩溃日志
            // ========================================

            if (
                !previousCrash.isNullOrBlank()
            ) {

                window.decorView.post {

                    showPreviousCrash(
                        previousCrash
                    )
                }
            }

        } catch (e: Throwable) {

            // ========================================
            // Activity 启动失败保护
            // ========================================

            val error =
                TextView(this).apply {

                    setTextColor(
                        Color.RED
                    )

                    textSize =
                        14f

                    setPadding(
                        20,
                        20,
                        20,
                        20
                    )

                    text =
                        buildString {

                            append(
                                "启动失败\n\n"
                            )

                            append(
                                e.javaClass.name
                            )

                            append(
                                "\n\n"
                            )

                            append(
                                e.message
                                    ?: "无错误信息"
                            )

                            append(
                                "\n\n"
                            )

                            append(
                                e.stackTraceToString()
                            )
                        }
                }

            setContentView(
                error
            )
        }
    }

    // ========================================
    // 显示上一次崩溃
    // ========================================

    private fun showPreviousCrash(
        crash: String
    ) {

        val view =
            TextView(this).apply {

                setTextColor(
                    Color.WHITE
                )

                textSize =
                    11f

                setPadding(
                    30,
                    20,
                    30,
                    20
                )

                text =
                    crash
            }

        AlertDialog.Builder(this)
            .setTitle(
                "⚠ 上一次运行发生崩溃"
            )
            .setView(
                view
            )
            .setPositiveButton(
                "知道了"
            ) { _, _ ->

                deleteCrashLog(
                    applicationContext
                )
            }
            .setNeutralButton(
                "保留日志",
                null
            )
            .show()
    }

    // ========================================
    // 创建策略按钮
    // ========================================

    private fun makeStrategyBtn(
        label: String,
        click: () -> Unit
    ): Button {

        return Button(this).apply {

            text =
                label

            textSize =
                11f

            setTextColor(
                Color.WHITE
            )

            setPadding(
                2,
                0,
                2,
                0
            )

            layoutParams =
                LinearLayout.LayoutParams(
                    0,
                    -2,
                    1f
                )

            setOnClickListener {

                click()
            }
        }
    }

    // ========================================
    // 设置策略
    // ========================================

    private fun setForcedStrategy(
        s: Int
    ) {

        forcedStrategy =
            if (
                forcedStrategy == s
            ) {
                -1
            } else {
                s
            }

        prefs.edit()
            .putInt(
                "forced_strategy",
                forcedStrategy
            )
            .apply()

        gameView?.setForcedStrategy(
            forcedStrategy
        )

        updateButtons()

        val name =
            when (forcedStrategy) {

                -1 -> "自动"

                0 -> "BFS"

                1 -> "追尾"

                2 -> "HAM"

                3 -> "BEAM"

                else -> "未知"
            }

        Toast.makeText(
            this,
            "策略: $name",
            Toast.LENGTH_SHORT
        ).show()
    }

    // ========================================
    // 更新策略按钮
    // ========================================

    private fun updateButtons() {

        val active =
            Color.rgb(
                231,
                76,
                60
            )

        val inactive =
            Color.rgb(
                70,
                70,
                70
            )

        val auto =
            Color.rgb(
                46,
                204,
                113
            )

        autoBtn?.setBackgroundColor(
            if (
                forcedStrategy == -1
            ) {
                auto
            } else {
                inactive
            }
        )

        bfsBtn?.setBackgroundColor(
            if (
                forcedStrategy == 0
            ) {
                active
            } else {
                inactive
            }
        )

        tailBtn?.setBackgroundColor(
            if (
                forcedStrategy == 1
            ) {
                active
            } else {
                inactive
            }
        )

        hamBtn?.setBackgroundColor(
            if (
                forcedStrategy == 2
            ) {
                active
            } else {
                inactive
            }
        )

        beamBtn?.setBackgroundColor(
            if (
                forcedStrategy == 3
            ) {
                active
            } else {
                inactive
            }
        )
    }

    // ========================================
    // AI 按钮
    // ========================================

    private fun updateAiButton() {

        if (aiOn) {

            aiBtn?.text =
                "AI ON"

            aiBtn?.setBackgroundColor(
                Color.rgb(
                    155,
                    89,
                    182
                )
            )

        } else {

            aiBtn?.text =
                "AI OFF"

            aiBtn?.setBackgroundColor(
                Color.rgb(
                    80,
                    80,
                    80
                )
            )
        }
    }

    // ========================================
    // 商店分类
    // ========================================

    private fun showShopCategoryDialog() {

        AlertDialog.Builder(this)
            .setTitle(
                "商店"
            )
            .setItems(
                arrayOf(
                    "蛇皮肤",
                    "棋盘主题"
                )
            ) { _, which ->

                if (
                    which == 0
                ) {

                    showSnakeShopDialog()

                } else {

                    showBoardShopDialog()
                }
            }
            .setNegativeButton(
                "关闭",
                null
            )
            .show()
    }

    // ========================================
    // 蛇皮肤商店
    // ========================================

    private fun showSnakeShopDialog() {

        val current =
            prefs.getInt(
                "money",
                0
            )

        val equipped =
            prefs.getString(
                "equipped_skin",
                "green"
            ) ?: "green"

        val skins =
            listOf(

                Skin(
                    "经典绿",
                    "green",
                    0
                ),

                Skin(
                    "海洋蓝",
                    "blue",
                    500
                ),

                Skin(
                    "烈焰红",
                    "red",
                    1000
                ),

                Skin(
                    "暗夜紫",
                    "purple",
                    2000
                ),

                Skin(
                    "黄金圣斗士",
                    "gold",
                    5000
                ),

                Skin(
                    "RGB神龙",
                    "rainbow",
                    100000
                )
            )

        val items =
            skins.map {

                val owned =
                    prefs.getBoolean(
                        "owned_${it.id}",
                        it.price == 0
                    )

                val status =
                    when {

                        it.id == equipped ->
                            "[已装备]"

                        owned ->
                            "点击装备"

                        else ->
                            "花费 ${it.price}"
                    }

                "${it.name} - $status"

            }.toTypedArray()

        AlertDialog.Builder(this)
            .setTitle(
                "蛇皮肤 (金币: $current)"
            )
            .setItems(
                items
            ) { _, which ->

                val s =
                    skins[which]

                val owned =
                    prefs.getBoolean(
                        "owned_${s.id}",
                        s.price == 0
                    )

                if (owned) {

                    prefs.edit()
                        .putString(
                            "equipped_skin",
                            s.id
                        )
                        .apply()

                    gameView?.updateCurrentSkin()

                } else if (
                    current >= s.price
                ) {

                    val nm =
                        current - s.price

                    prefs.edit()
                        .putInt(
                            "money",
                            nm
                        )
                        .putBoolean(
                            "owned_${s.id}",
                            true
                        )
                        .putString(
                            "equipped_skin",
                            s.id
                        )
                        .apply()

                    moneyView?.text =
                        "金币: $nm"

                    gameView?.updateCurrentSkin()

                } else {

                    Toast.makeText(
                        this,
                        "金币不足",
                        Toast.LENGTH_SHORT
                    ).show()
                }
            }
            .setNegativeButton(
                "返回",
                null
            )
            .show()
    }

    // ========================================
    // 棋盘商店
    // ========================================

    private fun showBoardShopDialog() {

        val current =
            prefs.getInt(
                "money",
                0
            )

        val equipped =
            prefs.getString(
                "equipped_board",
                "dark"
            ) ?: "dark"

        val boards =
            listOf(

                Board(
                    "经典纯黑",
                    "dark",
                    0
                ),

                Board(
                    "极简白",
                    "light",
                    500
                ),

                Board(
                    "霓虹蓝",
                    "neon",
                    1500
                ),

                Board(
                    "森林绿",
                    "forest",
                    3000
                ),

                Board(
                    "赛博朋克",
                    "cyberpunk",
                    6000
                ),

                Board(
                    "RGB流光",
                    "rainbow_board",
                    100000
                )
            )

        val items =
            boards.map {

                val owned =
                    prefs.getBoolean(
                        "owned_board_${it.id}",
                        it.price == 0
                    )

                val status =
                    when {

                        it.id == equipped ->
                            "[已装备]"

                        owned ->
                            "点击装备"

                        else ->
                            "花费 ${it.price}"
                    }

                "${it.name} - $status"

            }.toTypedArray()

        AlertDialog.Builder(this)
            .setTitle(
                "棋盘主题 (金币: $current)"
            )
            .setItems(
                items
            ) { _, which ->

                val b =
                    boards[which]

                val owned =
                    prefs.getBoolean(
                        "owned_board_${b.id}",
                        b.price == 0
                    )

                if (owned) {

                    prefs.edit()
                        .putString(
                            "equipped_board",
                            b.id
                        )
                        .apply()

                    gameView?.updateCurrentBoard()

                } else if (
                    current >= b.price
                ) {

                    val nm =
                        current - b.price

                    prefs.edit()
                        .putInt(
                            "money",
                            nm
                        )
                        .putBoolean(
                            "owned_board_${b.id}",
                            true
                        )
                        .putString(
                            "equipped_board",
                            b.id
                        )
                        .apply()

                    moneyView?.text =
                        "金币: $nm"

                    gameView?.updateCurrentBoard()

                } else {

                    Toast.makeText(
                        this,
                        "金币不足",
                        Toast.LENGTH_SHORT
                    ).show()
                }
            }
            .setNegativeButton(
                "返回",
                null
            )
            .show()
    }

    // ========================================
    // 数据类
    // ========================================

    private data class Skin(
        val name: String,
        val id: String,
        val price: Int
    )

    private data class Board(
        val name: String,
        val id: String,
        val price: Int
    )

    // ========================================
    // 生命周期
    // ========================================

    override fun onResume() {

        super.onResume()

        gameView?.resume()
    }

    override fun onPause() {

        gameView?.pause()

        super.onPause()
    }
}
