package com.example.snake

import android.graphics.Color
import android.os.Bundle
import android.view.Gravity
import android.view.WindowManager
import android.widget.FrameLayout
import android.widget.TextView
import androidx.appcompat.app.AppCompatActivity

class MainActivity : AppCompatActivity() {

    private lateinit var gameView: SnakeView
    private lateinit var scoreView: TextView

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)

        window.addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON)

        gameView = SnakeView(this)

        scoreView = TextView(this).apply {
            setTextColor(Color.WHITE)
            textSize = 20f
            setPadding(48, 48, 48, 48)
            text = "分数: 0"
        }

        gameView.onScoreChanged = { score ->
            runOnUiThread {
                scoreView.text = "分数: $score"
            }
        }

        val root = FrameLayout(this).apply {
            setBackgroundColor(Color.BLACK)
        }

        root.addView(
            gameView,
            FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT,
                FrameLayout.LayoutParams.MATCH_PARENT
            )
        )

        root.addView(
            scoreView,
            FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.WRAP_CONTENT,
                FrameLayout.LayoutParams.WRAP_CONTENT,
                Gravity.TOP or Gravity.START
            )
        )

        setContentView(root)
    }

    override fun onResume() {
        super.onResume()
        gameView.resume()
    }

    override fun onPause() {
        super.onPause()
        gameView.pause()
    }
}
