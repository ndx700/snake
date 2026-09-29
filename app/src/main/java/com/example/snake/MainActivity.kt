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

    private lateinit var gameView: SnakeView
    private lateinit var scoreView: TextView
    private lateinit var moneyView: TextView
    private lateinit var aiBtn: Button
    private lateinit var autoBtn: Button
    private lateinit var bfsBtn: Button
    private lateinit var hamBtn: Button
    private lateinit var mctsBtn: Button
    private lateinit var tailBtn: Button
    private lateinit var prefs: android.content.SharedPreferences

    // -1 = 自动；0=BFS；1=追尾；2=加权HAM；3=纯HAM；4=MCTS
    private var forcedStrategy = -1
    private var aiOn = true

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)

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
        gameView.setMctsEnabled(true)
        if (aiOn) gameView.setAIMode(1)
        gameView.setForcedStrategy(forcedStrategy)

        // ===== 第一行：分数、金币、AI总开关、商店 =====
        val row1 = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            setPadding(16, 16, 16, 4)
            gravity = Gravity.CENTER_VERTICAL
        }

        scoreView = TextView(this).apply {
            setTextColor(Color.WHITE)
            textSize = 12f
            text = "分数: 0"
        }

        moneyView = TextView(this).apply {
            setTextColor(Color.rgb(241, 196, 15))
            textSize = 12f
            text = "金币: ${prefs.getInt("money", 0)}"
            setPadding(16, 0, 0, 0)
        }

        aiBtn = Button(this).apply {
            textSize = 9f
            setTextColor(Color.WHITE)
            setPadding(8, 0, 8, 0)
            updateAiBtn()
            setOnClickListener {
                aiOn = !aiOn
                gameView.setAIMode(if (aiOn) 1 else 0)
                prefs.edit().putBoolean("ai_on", aiOn).apply()
                updateAiBtn()
            }
        }

        val shopBtn = Button(this).apply {
            text = "🛒"
            textSize = 9f
            setBackgroundColor(Color.rgb(46, 204, 113))
            setTextColor(Color.WHITE)
            setPadding(8, 0, 8, 0)
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

        // ===== 第二行：5 个策略按钮 =====
        val row2 = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            setPadding(8, 2, 8, 8)
            gravity = Gravity.CENTER_VERTICAL
        }

        autoBtn = makeStrategyBtn("🎯自动") {
            setForcedStrategy(-1)
        }
        bfsBtn = makeStrategyBtn("🚀BFS") {
            setForcedStrategy(0)
        }
        tailBtn = makeStrategyBtn("🔄追尾") {
            setForcedStrategy(1)
        }
        hamBtn = makeStrategyBtn("🛤HAM") {
            setForcedStrategy(2)
        }
        mctsBtn = makeStrategyBtn("🧠MCTS") {
            setForcedStrategy(4)
        }

        row2.addView(autoBtn)
        row2.addView(bfsBtn)
        row2.addView(tailBtn)
        row2.addView(hamBtn)
        row2.addView(mctsBtn)

        // ===== 顶部容器 =====
        val topContainer = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
        }
        topContainer.addView(row1)
        topContainer.addView(row2)

        gameView.onScoreChanged = { score ->
            runOnUiThread { scoreView.text = "分数: $score" }
        }
        gameView.onMoneyChanged = { money ->
            runOnUiThread { moneyView.text = "金币: $money" }
        }

        updateAllStrategyButtons()

        val root = FrameLayout(this).apply { setBackgroundColor(Color.BLACK) }
        root.addView(gameView, FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT))
        root.addView(topContainer, FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.WRAP_CONTENT, Gravity.TOP))

        setContentView(root)
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
        gameView.setForcedStrategy(forcedStrategy)
        prefs.edit().putInt("forced_strategy", forcedStrategy).apply()
        updateAllStrategyButtons()
        val name = when (forcedStrategy) {
            -1 -> "自动模式"
            0 -> "强制 BFS + Beam Search"
            1 -> "强制 追尾保命"
            2 -> "强制 加权汉密尔顿"
            3 -> "强制 纯汉密尔顿"
            4 -> "强制 MCTS 深推"
            else -> "未知"
        }
        Toast.makeText(this, name, Toast.LENGTH_SHORT).show()
    }

    private fun updateAllStrategyButtons() {
        val activeColor = Color.RED
        val inactiveColor = Color.rgb(80, 80, 80)
        val autoColor = Color.rgb(46, 204, 113)

        autoBtn.setBackgroundColor(if (forcedStrategy == -1) autoColor else inactiveColor)
        bfsBtn.setBackgroundColor(if (forcedStrategy == 0) activeColor else inactiveColor)
        tailBtn.setBackgroundColor(if (forcedStrategy == 1) activeColor else inactiveColor)
        hamBtn.setBackgroundColor(if (forcedStrategy == 2) activeColor else inactiveColor)
        mctsBtn.setBackgroundColor(if (forcedStrategy == 4) activeColor else inactiveColor)
    }

    private fun updateAiBtn() {
        if (aiOn) {
            aiBtn.text = "🤖AI ON"
            aiBtn.setBackgroundColor(Color.rgb(155, 89, 182))
        } else {
            aiBtn.text = "🤖AI OFF"
            aiBtn.setBackgroundColor(Color.rgb(80, 80, 80))
        }
    }

    private fun showShopCategoryDialog() {
        val options = arrayOf("🐍 蛇皮肤", "🏁 棋盘主题")
        AlertDialog.Builder(this)
            .setTitle("🛒 商店")
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
            val status = if (skin.id == equippedSkin) "[已装备]" else if (prefs.getBoolean("owned_${skin.id}", skin.price == 0)) "点击装备" else "花费 ${skin.price} 金币"
            "${skin.name}  -  $status"
        }.toTypedArray()

        AlertDialog.Builder(this)
            .setTitle("🐍 蛇皮肤 (金币: $currentMoney)")
            .setItems(items) { _, which ->
                val selectedSkin = skins[which]
                val isOwned = prefs.getBoolean("owned_${selectedSkin.id}", selectedSkin.price == 0)
                if (isOwned) {
                    prefs.edit().putString("equipped_skin", selectedSkin.id).apply()
                    gameView.updateCurrentSkin()
                    Toast.makeText(this, "已装备: ${selectedSkin.name}", Toast.LENGTH_SHORT).show()
                } else {
                    if (currentMoney >= selectedSkin.price) {
                        val newMoney = currentMoney - selectedSkin.price
                        prefs.edit().putInt("money", newMoney).apply()
                        prefs.edit().putBoolean("owned_${selectedSkin.id}", true).apply()
                        prefs.edit().putString("equipped_skin", selectedSkin.id).apply()
                        moneyView.text = "金币: $newMoney"
                        gameView.updateCurrentSkin()
                        Toast.makeText(this, "购买成功！已装备: ${selectedSkin.name}", Toast.LENGTH_SHORT).show()
                    } else {
                        Toast.makeText(this, "金币不足！还需要 ${selectedSkin.price - currentMoney} 金币", Toast.LENGTH_SHORT).show()
                    }
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
            val status = if (board.id == equippedBoard) "[已装备]" else if (prefs.getBoolean("owned_board_${board.id}", board.price == 0)) "点击装备" else "花费 ${board.price} 金币"
            "${board.name}  -  $status"
        }.toTypedArray()

        AlertDialog.Builder(this)
            .setTitle("🏁 棋盘主题 (金币: $currentMoney)")
            .setItems(items) { _, which ->
                val selectedBoard = boards[which]
                val isOwned = prefs.getBoolean("owned_board_${selectedBoard.id}", selectedBoard.price == 0)
                if (isOwned) {
                    prefs.edit().putString("equipped_board", selectedBoard.id).apply()
                    gameView.updateCurrentBoard()
                    Toast.makeText(this, "已装备: ${selectedBoard.name}", Toast.LENGTH_SHORT).show()
                } else {
                    if (currentMoney >= selectedBoard.price) {
                        val newMoney = currentMoney - selectedBoard.price
                        prefs.edit().putInt("money", newMoney).apply()
                        prefs.edit().putBoolean("owned_board_${selectedBoard.id}", true).apply()
                        prefs.edit().putString("equipped_board", selectedBoard.id).apply()
                        moneyView.text = "金币: $newMoney"
                        gameView.updateCurrentBoard()
                        Toast.makeText(this, "购买成功！已装备: ${selectedBoard.name}", Toast.LENGTH_SHORT).show()
                    } else {
                        Toast.makeText(this, "金币不足！还需要 ${selectedBoard.price - currentMoney} 金币", Toast.LENGTH_SHORT).show()
                    }
                }
            }.setNegativeButton("返回", null).show()
    }

    private data class Skin(val name: String, val id: String, val price: Int)
    private data class Board(val name: String, val id: String, val price: Int)

    override fun onResume() { super.onResume(); gameView.resume() }
    override fun onPause() { super.onPause(); gameView.pause() }
}
