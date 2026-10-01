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
            val oldHandler = Thread.getDefaultUncaughtExceptionHandler()

            Thread.setDefaultUncaughtExceptionHandler { thread, throwable ->
                try {
                    val time = SimpleDateFormat(
                        "yyyy-MM-dd HH:mm:ss",
                        Locale.getDefault()
                    ).format(Date())

                    val file = File(appContext.filesDir, CRASH_FILE)

                    val text = buildString {
                        append("================================\n")
                        append("        SNAKE 崩溃诊断日志\n")
                        append("================================\n\n")

                        append("时间:\n")
                        append(time)
                        append("\n\n")

                        append("线程:\n")
                        append(thread.name)
                        append("\n\n")

                        append("异常类型:\n")
                        append(throwable.javaClass.name)
                        append("\n\n")

                        append("异常信息:\n")
                        append(throwable.message ?: "无")
                        append("\n\n")

                        append("========== STACK TRACE ==========\n")
                        append(throwable.stackTraceToString())

                        var cause = throwable.cause
                        var level = 1

                        while (cause != null) {
                            append("\n\n========== CAUSE $level ==========\n")
                            append(cause.stackTraceToString())

                            cause = cause.cause
                            level++
                        }
                    }

                    file.writeText(text)

                } catch (_: Throwable) {
                }

                try {
                    oldHandler?.uncaughtException(thread, throwable)
                } catch (_: Throwable) {
                }
            }
        }

        private fun getCrashFile(context: Context): File =
            File(context.applicationContext.filesDir, CRASH_FILE)

        private fun readCrashLog(context: Context): String? =
            try {
                val file = getCrashFile(context)
                if (file.exists()) file.readText() else null
            } catch (_: Throwable) {
                null
            }

        private fun deleteCrashLog(context: Context) {
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
    private var trainingBtn: Button? = null
    private var reinforceBtn: Button? = null

    private lateinit var prefs: android.content.SharedPreferences

    private var aiOn = true
    private var trainingMode = false
    private var reinforceMode = false

    override fun onCreate(savedInstanceState: Bundle?) {
        installCrashHandler(applicationContext)

        super.onCreate(savedInstanceState)

        val previousCrash = readCrashLog(applicationContext)

        try {
            window.addFlags(
                WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON
            )

            prefs = getSharedPreferences(
                "snake_prefs",
                Context.MODE_PRIVATE
            )

            aiOn = prefs.getBoolean(
                "ai_on",
                true
            )

            trainingMode = prefs.getBoolean(
                "training_mode",
                false
            )

            gameView = SnakeView(this)

            // gameView?.setTrainingMode(trainingMode)

            // gameView?.setAIMode(
                // if (aiOn || trainingMode) 1 else 0
            // )

            val row1 = LinearLayout(this).apply {
                orientation = LinearLayout.HORIZONTAL

                setPadding(
                    12,
                    10,
                    12,
                    4
                )

                gravity = Gravity.CENTER_VERTICAL
            }

            scoreView = TextView(this).apply {
                text = "分数: 0"
                textSize = 15f
                setTextColor(Color.WHITE)
            }

            moneyView = TextView(this).apply {
                text = "金币: ${prefs.getInt("money", 0)}"
                textSize = 15f

                setTextColor(
                    Color.rgb(
                        241,
                        196,
                        15
                    )
                )

                setPadding(
                    16,
                    0,
                    0,
                    0
                )
            }

            row1.addView(scoreView)
            row1.addView(moneyView)

            val row2 = LinearLayout(this).apply {
                orientation = LinearLayout.HORIZONTAL

                setPadding(
                    8,
                    4,
                    8,
                    10
                )

                gravity = Gravity.CENTER_VERTICAL
            }

            fun compactBtn(
                textInit: String,
                bg: Int
            ): Button =
                Button(this).apply {

                    text = textInit
                    textSize = 11f

                    setTextColor(Color.WHITE)

                    setPadding(
                        6,
                        0,
                        6,
                        0
                    )

                    setBackgroundColor(bg)

                    minWidth = 0
                    minimumWidth = 0

                    layoutParams =
                        LinearLayout.LayoutParams(
                            0,
                            LinearLayout.LayoutParams.WRAP_CONTENT,
                            1f
                        ).apply {
                            setMargins(
                                3,
                                0,
                                3,
                                0
                            )
                        }
                }

            trainingBtn =
                compactBtn(
                    "训练AI",
                    Color.rgb(52, 73, 94)
                ).apply {

                    updateTrainingButton()

                    setOnClickListener {

                        if (reinforceMode) {
                            reinforceMode = false

                            // gameView?.setReinforceTraining(
                                // false
                            // )

                            updateReinforceButton()
                        }

                        trainingMode = !trainingMode

                        prefs.edit()
                            .putBoolean(
                                "training_mode",
                                trainingMode
                            )
                            .apply()

                        if (trainingMode) {
                            aiOn = true

                            prefs.edit()
                                .putBoolean(
                                    "ai_on",
                                    true
                                )
                                .apply()

                            // gameView?.setAIMode(1)

                            updateAiButton()
                        }

                        // gameView?.setTrainingMode(
                            // trainingMode
                        // )

                        updateTrainingButton()

                        val msg =
                            if (trainingMode) {
                                "训练模式：AI 加速中"
                            } else {
                                "已退出训练"
                            }

                        Toast.makeText(
                            this@MainActivity,
                            msg,
                            Toast.LENGTH_SHORT
                        ).show()
                    }
                }

            reinforceBtn =
                compactBtn(
                    "强化",
                    Color.rgb(39, 174, 96)
                ).apply {

                    updateReinforceButton()

                    setOnClickListener {

                        reinforceMode = !reinforceMode

                        if (reinforceMode) {

                            trainingMode = true
                            aiOn = true

                            prefs.edit()
                                .putBoolean(
                                    "training_mode",
                                    true
                                )
                                .putBoolean(
                                    "ai_on",
                                    true
                                )
                                .apply()

                            // gameView?.setAIMode(1)

                            // gameView?.setReinforceTraining(
                                // true
                            // )

                            updateAiButton()
                            updateTrainingButton()

                            Toast.makeText(
                                this@MainActivity,
                                "强化训练：吃满 CPU",
                                Toast.LENGTH_SHORT
                            ).show()

                        } else {

                            // gameView?.setReinforceTraining(
                                // false
                            // )

                            Toast.makeText(
                                this@MainActivity,
                                "已停止强化训练",
                                Toast.LENGTH_SHORT
                            ).show()
                        }

                        updateReinforceButton()
                    }
                }

            aiBtn =
                compactBtn(
                    "AI ON",
                    Color.rgb(155, 89, 182)
                ).apply {

                    updateAiButton()

                    setOnClickListener {

                        if (
                            trainingMode ||
                            reinforceMode
                        ) {
                            Toast.makeText(
                                this@MainActivity,
                                "训练/强化模式下 AI 强制开启",
                                Toast.LENGTH_SHORT
                            ).show()

                            return@setOnClickListener
                        }

                        aiOn = !aiOn

                        prefs.edit()
                            .putBoolean(
                                "ai_on",
                                aiOn
                            )
                            .apply()

                        // gameView?.setAIMode(
                            // if (aiOn) 1 else 0
                        // )

                        updateAiButton()

                        val msg =
                            if (aiOn) {
                                "AI 已开启"
                            } else {
                                "AI 已关闭，滑动方向手动控制"
                            }

                        Toast.makeText(
                            this@MainActivity,
                            msg,
                            Toast.LENGTH_SHORT
                        ).show()
                    }
                }

            val shop =
                compactBtn(
                    "商店",
                    Color.rgb(46, 204, 113)
                ).apply {

                    setOnClickListener {
                        showShopCategoryDialog()
                    }
                }

            row2.addView(trainingBtn)
            row2.addView(reinforceBtn)
            row2.addView(aiBtn)
            row2.addView(shop)

            val top = LinearLayout(this).apply {
                orientation = LinearLayout.VERTICAL

                setBackgroundColor(
                    Color.argb(
                        220,
                        20,
                        20,
                        20
                    )
                )

                addView(row1)
                addView(row2)
            }

            // gameView?.onScoreChanged = { s ->
                // runOnUiThread {
                    // scoreView?.text = "分数: $s"
                // }
            // }

            // gameView?.onMoneyChanged = { m ->
                // runOnUiThread {
                    // moneyView?.text = "金币: $m"
                // }
            // }

            val root = FrameLayout(this).apply {
                setBackgroundColor(Color.BLACK)
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

            setContentView(root)

            if (!previousCrash.isNullOrBlank()) {
                window.decorView.post {
                    showPreviousCrash(
                        previousCrash
                    )
                }
            }

        } catch (e: Throwable) {

            val error = TextView(this).apply {

                setTextColor(Color.RED)
                textSize = 14f

                setPadding(
                    20,
                    20,
                    20,
                    20
                )

                text = buildString {

                    append("启动失败\n\n")

                    append(e.javaClass.name)
                    append("\n\n")

                    append(
                        e.message
                            ?: "无错误信息"
                    )

                    append("\n\n")

                    append(
                        e.stackTraceToString()
                    )
                }
            }

            setContentView(error)
        }
    }

    private fun showPreviousCrash(
        crash: String
    ) {
        val view = TextView(this).apply {

            setTextColor(Color.WHITE)
            textSize = 11f

            setPadding(
                30,
                20,
                30,
                20
            )

            text = crash
        }

        AlertDialog.Builder(this)
            .setTitle("上一次运行发生崩溃")
            .setView(view)
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

    private fun updateAiButton() {

        if (aiOn) {

            aiBtn?.text = "AI ON"

            aiBtn?.setBackgroundColor(
                Color.rgb(
                    155,
                    89,
                    182
                )
            )

        } else {

            aiBtn?.text = "AI OFF"

            aiBtn?.setBackgroundColor(
                Color.rgb(
                    80,
                    80,
                    80
                )
            )
        }
    }

    private fun updateTrainingButton() {

        if (trainingMode) {

            trainingBtn?.text = "训练中"

            trainingBtn?.setBackgroundColor(
                Color.rgb(
                    231,
                    76,
                    60
                )
            )

        } else {

            trainingBtn?.text = "训练AI"

            trainingBtn?.setBackgroundColor(
                Color.rgb(
                    52,
                    73,
                    94
                )
            )
        }
    }

    private fun updateReinforceButton() {

        if (reinforceMode) {

            reinforceBtn?.text = "停止"

            reinforceBtn?.setBackgroundColor(
                Color.rgb(
                    192,
                    57,
                    43
                )
            )

        } else {

            reinforceBtn?.text = "强化"

            reinforceBtn?.setBackgroundColor(
                Color.rgb(
                    39,
                    174,
                    96
                )
            )
        }
    }

    private fun showShopCategoryDialog() {

        AlertDialog.Builder(this)
            .setTitle("商店")
            .setItems(
                arrayOf(
                    "蛇皮肤",
                    "棋盘主题"
                )
            ) { _, which ->

                if (which == 0) {
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

        val skins = listOf(

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
            .setItems(items) { _, which ->

                val s = skins[which]

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

                    // gameView?.updateCurrentSkin()

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

                    // gameView?.updateCurrentSkin()

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

        val boards = listOf(

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
            .setItems(items) { _, which ->

                val b = boards[which]

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

                    // gameView?.updateCurrentBoard()

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

                    // gameView?.updateCurrentBoard()

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

    override fun onResume() {
        super.onResume()
        // gameView?.resume()
    }

    override fun onPause() {
        // gameView?.pause()
        super.onPause()
    }
}
