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
    private lateinit var autoBtn: Button
    private lateinit var prefs: android.content.SharedPreferences

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)

        window.addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON)

        // 申请 120Hz 刷新率（修复了之前的编译错误）
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
        } catch (e: Exception) {
            e.printStackTrace()
        }

        prefs = getSharedPreferences("snake_prefs", Context.MODE_PRIVATE)
        gameView = SnakeView(this)

        val topBar = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            setPadding(32, 32, 32, 32)
            gravity = Gravity.CENTER_VERTICAL
        }

        scoreView = TextView(this).apply {
            setTextColor(Color.WHITE)
            textSize = 16f
            text = "分数: 0"
        }

        moneyView = TextView(this).apply {
            setTextColor(Color.rgb(241, 196, 15))
            textSize = 16f
            text = "金币: ${prefs.getInt("money", 0)}"
            setPadding(32, 0, 0, 0)
        }

        autoBtn = Button(this).apply {
            text = "🤖 演示"
            textSize = 12f
            setBackgroundColor(Color.rgb(155, 89, 182)) // 紫色
            setTextColor(Color.WHITE)
            setPadding(16, 0, 16, 0)
            setOnClickListener {
                gameView.toggleAutoPlay()
            }
        }

        val shopBtn = Button(this).apply {
            text = "🛒 商店"
            textSize = 12f
            setBackgroundColor(Color.rgb(52, 152, 219))
            setTextColor(Color.WHITE)
            setPadding(16, 0, 16, 0)
            setOnClickListener { showShopCategoryDialog() }
        }

        val spacer = FrameLayout(this).apply {
            layoutParams = LinearLayout.LayoutParams(0, 1, 1f)
        }

        topBar.addView(scoreView)
        topBar.addView(moneyView)
        topBar.addView(spacer)
        topBar.addView(autoBtn)
        topBar.addView(shopBtn)

        gameView.onScoreChanged = { score ->
            runOnUiThread { scoreView.text = "分数: $score" }
        }
        gameView.onMoneyChanged = { money ->
            runOnUiThread { moneyView.text = "金币: $money" }
        }

        // 监听 AI 状态，当 AI 死亡时按钮会自动变回紫色
        gameView.onAutoPlayChanged = { isAuto ->
            runOnUiThread {
                if (isAuto) {
                    autoBtn.text = "🛑 停止演示"
                    autoBtn.setBackgroundColor(Color.RED)
                } else {
                    autoBtn.text = "🤖 演示"
                    autoBtn.setBackgroundColor(Color.rgb(155, 89, 182))
                }
            }
        }

        val root = FrameLayout(this).apply { setBackgroundColor(Color.BLACK) }
        root.addView(gameView, FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT))
        root.addView(topBar, FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.WRAP_CONTENT, Gravity.TOP))

        setContentView(root)
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
            Skin("经典绿", "green", 0), Skin("海洋蓝", "blue", 500),
            Skin("烈焰红", "red", 1000), Skin("暗夜紫", "purple", 2000), Skin("黄金圣斗士", "gold", 5000)
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
            Board("经典纯黑", "dark", 0), Board("极简白", "light", 500),
            Board("霓虹蓝", "neon", 1500), Board("森林绿", "forest", 3000), Board("赛博朋克", "cyberpunk", 6000)
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
