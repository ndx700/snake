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

        /**
         * 安装全局崩溃捕获器。
         */
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
                            append(
                                throwable.javaClass.name
                            )
                            append("\n\n")

                            append("异常信息:\n")
                            append(
                                throwable.message ?: "无"
                            )
                            append("\n\n")

                            append("========== STACK TRACE ==========\n")

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

                if (!file.exists()) {
                    null
                } else {
                    file.readText()
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
    private var mctsBtn: Button? = null

    private lateinit var prefs:
        android.content.SharedPreferences

    private var forcedStrategy = -1

    private var aiOn = true

    override fun onCreate(
        savedInstanceState: Bundle?
    ) {

        /*
         * 尽可能早安装崩溃捕获。
         */
        installCrashHandler(
            applicationContext
        )

        super.onCreate(savedInstanceState)

        /*
         * 如果上一次运行崩溃，
         * 读取之前的崩溃日志。
         */
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

            /*
             * 创建游戏。
             */
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

                   
