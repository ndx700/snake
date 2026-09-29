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

class MainActivity : AppCompatActivity() {

    private var gameView: SnakeView? = null

    private var scoreView: TextView? = null
    private var moneyView: TextView? = null

    private var aiBtn: Button? = null

    private var autoBtn: Button? = null
    private var bfsBtn: Button? = null
    private var tailBtn: Button? = null
    private var hamBtn: Button? = null
    private var mctsBtn: Button? = null

    private lateinit var prefs: android.content.SharedPreferences

    private var forcedStrategy = -1
    private var aiOn = true

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)

        try {

            window.addFlags(
                WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON
            )

            prefs = getSharedPreferences(
                "snake_prefs",
                Context.MODE_PRIVATE
            )

            forcedStrategy = prefs.getInt(
                "forced_strategy",
                -1
            )

            aiOn = prefs.getBoolean(
                "ai_on",
                true
            )

            gameView = SnakeView(this)

            gameView?.setAIMode(
                if (aiOn) 1 else 0
            )

            gameView?.setForcedStrategy(
                forcedStrategy
            )

            // ========================================
            // 第一行：分数 / 金币 / 商店
            // ========================================

            val row1 = LinearLayout(this).apply {

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

            scoreView = TextView(this).apply {

                text = "分数: 0"

                textSize = 14f

                setTextColor(
                    Color.WHITE
                )
            }

            moneyView = TextView(this).apply {

                text =
                    "金币: ${
                        prefs.getInt(
                            "money",
                            0
                        )
                    }"

                textSize = 14f

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

            val shop = Button(this).apply {

                text = "🛒"

                textSize = 12f

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

            val spacer = FrameLayout(this).apply {

                layoutParams =
                    LinearLayout.LayoutParams(
                        0,
                        1,
                        1f
                    )
            }

            row1.addView(scoreView)
            row1.addView(moneyView)
            row1.addView(spacer)
            row1.addView(shop)

            // ========================================
            // 第二行：策略按钮 + AI ON/OFF
            // ========================================

            val row2 = LinearLayout(this).apply {

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
                makeStrategyBtn("自动") {
                    setForcedStrategy(-1)
                }

            bfsBtn =
                makeStrategyBtn("BFS") {
                    setForcedStrategy(0)
                }

            tailBtn =
                makeStrategyBtn("追尾") {
                    setForcedStrategy(1)
                }

            hamBtn =
                makeStrategyBtn("HAM") {
                    setForcedStrategy(2)
                }

            mctsBtn =
                makeStrategyBtn("BEAM") {
                    setForcedStrategy(4)
                }

            // AI 按钮移动到第二行最右边
            ai
