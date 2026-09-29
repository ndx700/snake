package com.example.snake

import android.app.AlertDialog
import android.content.Context
import android.graphics.Color
import android.os.Build
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
            window.addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON)

            try {
                @Suppress("DEPRECATION")
                val display = windowManager.defaultDisplay
                if (display != null) {
                    val maxMode = display.supportedModes.maxByOrNull { it.refreshRate }
                    if (maxMode != null) {
                        val params = window.attributes
                        params.preferredDisplayModeId = maxMode.modeId
                        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.R) {
                            params.preferredRefreshRate = maxMode.refreshRate
                        }
                        window.attributes = params
                    }
                }
            } catch (e: Exception) { e.printStackTrace() }

            prefs = getSharedPreferences("snake_prefs", Context.MODE_PRIVATE)
            forcedStrategy = prefs.getInt("forced_strategy", -1)
            aiOn = prefs.getBoolean("ai_on", true)

            gameView = SnakeView(this)
            if (aiOn) gameView?.setAIMode(1)
            gameView?.setForcedStrategy(forcedStrategy)

            val row1 = LinearLayout(this).apply {
                orientation = LinearLayout.HORIZONTAL
                setPadding(16, 16, 16, 4)
                gravity = Gravity.CENTER_VERTICAL
            }

            scoreView = TextView(this).apply {
                setTextColor(Color.WHITE); textSize = 12f; text = "分数: 0"
            }
            moneyView = TextView(this).apply {
                setTextColor(Color.rgb(241, 196, 15)); textSize = 12f
                text = "金币: ${prefs.getInt("money", 0)}"; setPadding(16, 0, 0, 0)
            }
            aiBtn = Button(this).apply {
                textSize = 9f; setTextColor(Color.WHITE); setPadding(8, 0, 8, 0)
                updateAiBtn()
                setOnClickListener {
                    aiOn = !aiOn
                    gameView?.setAIMode(if (aiOn) 1 else 0)
                    prefs.edit().putBoolean("ai_on", aiOn).apply()
                    updateAiBtn()
                }
            }
            val shopBtn = Button(this).apply {
                text = "🛒"; textSize = 9f
                setBackgroundColor(Color.rgb(46, 204, 113))
                setTextColor(Color.WHITE); setPadding(8, 0, 8, 0)
                setOnClickListener { showShopCategoryDialog() }
            }
            val spacer1 = FrameLayout(this).apply {
                layoutParams = LinearLayout.LayoutParams(0, 1, 1f)
            }
            row1.addView(scoreView)
            row1.addView(moneyView)
            row1.addView(spacer1)
            row1.addView(aiBtn)
            row1.addView(shopBtn)

            val row2 = LinearLayout(this).apply {
                orientation = LinearLayout.HORIZONTAL
                setPadding(8, 2, 8, 8)
                gravity = Gravity.CENTER_VERTICAL
            }
            autoBtn = makeStrategyBtn("自动") { setForcedStrategy(-1) }
            bfsBtn = makeStrategyBtn("BFS") { setForcedStrategy(0) }
            tailBtn = makeStrategyBtn("追尾") { setForcedStrategy(1) }
            hamBtn = makeStrategyBtn("HAM") { setForcedStrategy(2) }
            mctsBtn = makeStrategyBtn("MCTS") { setForcedStrategy(4) }
            row2.addView(autoBtn)
            row2.addView(bfsBtn)
            row2.addView(tailBtn)
            row2.addView(hamBtn)
            row2.addView(mctsBtn)

            val topContainer = LinearLayout(this).apply {
                orientation = LinearLayout.VERTICAL
            }
            topContainer.addView(row1)
            topContainer.addView(row2)

            gameView?.onScoreChanged = { score ->
                runOnUiThread { scoreView?.text = "分数: $score" }
            }
            gameView?.onMoneyChanged = { money ->
                runOnUiThread { moneyView?.text = "金币: $money" }
            }

            updateAllStrategyButtons()

            val root = FrameLayout(this).apply { setBackgroundColor(Color.BLACK) }
            gameView?.let {
                root.addView(it, FrameLayout.LayoutParams(
                    FrameLayout.LayoutParams.MATCH_PARENT,
                    FrameLayout.LayoutParams.MATCH_PARENT
                ))
            }
            root.addView(topContainer, FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT,
                FrameLayout.LayoutParams.WRAP_CONTENT,
                Gravity.TOP
            ))
            setContentView(root)
        } catch (e: Exception) {
            // 崩溃时显示错误信息，而不是闪退
            val err = TextView(this).apply {
                setTextColor(Color.RED)
                textSize = 14f
                setPadding(20, 20, 20, 20)
                text = "启动失败:\n${e.javaClass.simpleName}\n${e.message}\n\n${e.stackTrace.take(5).joinToString("\n")}"
            }
            setContentView(err)
        }
    }

    private fun makeStrategyBtn(label: String, onClick: () -> Unit): Button {
        return Button(this).apply {
            text = label
            textSize = 8f
            setTextColor(Color.WHITE)
            setPadding(4, 0, 4, 0)
            layoutParams = LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f)
            setOnClickListener { onClick() }
        }
    }

    private fun setForcedStrategy(s: Int) {
        forcedStrategy = if (forcedStrategy == s) -1 else s
        gameView?.setForcedStrategy(forcedStrategy)
        prefs.edit().putInt("forced_strategy", forcedStrategy).apply()
        updateAllStrategyButtons()
        Toast.makeText(this, "策略: $forcedStrategy", Toast.LENGTH_SHORT).show()
    }

    private fun updateAllStrategyButtons() {
        val active = Color.RED
        val inactive = Color.rgb(80, 80, 80)
        val auto = Color.rgb(46, 204, 113)
        autoBtn?.setBackgroundColor(if (forcedStrategy == -1) auto else inactive)
        bfsBtn?.setBackgroundColor(if (forcedStrategy == 0) active else inactive)
        tailBtn?.setBackgroundColor(if (forcedStrategy == 1) active else inactive)
        hamBtn?.setBackgroundColor(if (forcedStrategy == 2) active else inactive)
        mctsBtn?.setBackgroundColor(if (forcedStrategy == 4) active else inactive)
    }

    private fun updateAiBtn() {
        if (aiOn) {
            aiBtn?.text = "AI ON"
            aiBtn?.setBackgroundColor(Color.rgb(155, 89, 182))
        } else {
            aiBtn?.text = "AI OFF"
            aiBtn?.setBackgroundColor(Color.rgb(80, 80, 80))
        }
    }

    private fun showShopCategoryDialog() {
        val options = arrayOf("蛇皮肤", "棋盘主题")
        AlertDialog.Builder(this)
            .setTitle("商店")
            .setItems(options) { _, which ->
                when (which) {
                    0 -> showSnakeShopDialog()
                    1 -> showBoardShopDialog()
                }
            }
            .setNegativeButton("关闭", null)
            .show()
    }

    private fun showSnakeShopDialog() {
        val currentMoney = prefs.getInt("money", 0)
        val equippedSkin = prefs.getString("equipped_skin", "green") ?: "green"
        val skins = listOf(
            Skin("经典绿", "green", 0),
            Skin("海洋蓝", "blue", 500),
            Skin("烈焰红", "red", 1000),
            Skin("暗夜紫", "purple", 2000),
            Skin("黄金圣斗士", "gold", 5000),
            Skin("RGB神龙", "rainbow", 100000)
        )
        val items = skins.map { skin ->
            val status = if (skin.id == equippedSkin) "[已装备]" else if (prefs.getBoolean("owned_${skin.id}", skin.price == 0)) "点击装备" else "花费 ${skin.price}"
            "${skin.name}  -  $status"
        }.toTypedArray()
        AlertDialog.Builder(this)
            .setTitle("蛇皮肤 (金币: $currentMoney)")
            .setItems(items) { _, which ->
                val s = skins[which]
                val owned = prefs.getBoolean("owned_${s.id}", s.price == 0)
                if (owned) {
                    prefs.edit().putString("equipped_skin", s.id).apply()
                    gameView?.updateCurrentSkin()
                } else if (currentMoney >= s.price) {
                    val nm = currentMoney - s.price
                    prefs.edit().putInt("money", nm)
                        .putBoolean("owned_${s.id}", true)
                        .putString("equipped_skin", s.id).apply()
                    moneyView?.text = "金币: $nm"
                    gameView?.updateCurrentSkin()
                } else {
                    Toast.makeText(this, "金币不足", Toast.LENGTH_SHORT).show()
                }
            }.setNegativeButton("返回", null).show()
    }

    private fun showBoardShopDialog() {
        val currentMoney = prefs.getInt("money", 0)
        val equippedBoard = prefs.getString("equipped_board", "dark") ?: "dark"
        val boards = listOf(
            Board("经典纯黑", "dark", 0),
            Board("极简白", "light", 500),
            Board("霓虹蓝", "neon", 1500),
            Board("森林绿", "forest", 3000),
            Board("赛博朋克", "cyberpunk", 6000),
            Board("RGB流光", "rainbow_board", 100000)
        )
        val items = boards.map { board ->
            val status = if (board.id == equippedBoard) "[已装备]" else if (prefs.getBoolean("owned_board_${board.id}", board.price == 0)) "点击装备" else "花费 ${board.price}"
            "${board.name}  -  $status"
        }.toTypedArray()
        AlertDialog.Builder(this)
            .setTitle("棋盘主题 (金币: $currentMoney)")
            .setItems(items) { _, which ->
                val b = boards[which]
                val owned = prefs.getBoolean("owned_board_${b.id}", b.price == 0)
                if (owned) {
                    prefs.edit().putString("equipped_board", b.id).apply()
                    gameView?.updateCurrentBoard()
                } else if (currentMoney >= b.price) {
                    val nm = currentMoney - b.price
                    prefs.edit().putInt("money", nm)
                        .putBoolean("owned_board_${b.id}", true)
                        .putString("equipped_board", b.id).apply()
                    moneyView?.text = "金币: $nm"
                    gameView?.updateCurrentBoard()
                } else {
                    Toast.makeText(this, "金币不足", Toast.LENGTH_SHORT).show()
                }
            }.setNegativeButton("返回", null).show()
    }

    private data class Skin(val name: String, val id: String, val price: Int)
    private data class Board(val name: String, val id: String, val price: Int)

    override fun onResume() { super.onResume(); gameView?.resume() }
    override fun onPause() { super.onPause(); gameView?.pause() }
}
