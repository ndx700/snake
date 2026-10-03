package com.example.snake
import android.media.*
import android.os.Build

internal class BgmPlayer {
        private var audioTrack: AudioTrack? = null
        @Volatile private var playing = false
        private var generation = 0L
        private var thread: Thread? = null

        @Synchronized fun start() {
            if (playing) return
            playing = true
            val session = ++generation
            thread = Thread {
                try {
                    val sr = 22050; val pcm = generateMelody(sr)
                    val track = AudioTrack.Builder()
                        .setAudioAttributes(AudioAttributes.Builder().setUsage(AudioAttributes.USAGE_GAME).setContentType(AudioAttributes.CONTENT_TYPE_MUSIC).build())
                        .setAudioFormat(AudioFormat.Builder().setEncoding(AudioFormat.ENCODING_PCM_16BIT).setSampleRate(sr).setChannelMask(AudioFormat.CHANNEL_OUT_MONO).build())
                        .setBufferSizeInBytes(pcm.size * 2).setTransferMode(AudioTrack.MODE_STATIC).build()
                    track.write(pcm, 0, pcm.size)
                    if (Build.VERSION.SDK_INT >= 23) track.setLoopPoints(0, pcm.size, -1)
                    synchronized(this) {
                        if (playing && session == generation) { audioTrack = track; track.play() } else track.release()
                    }
                } catch (_: Throwable) {}
            }.also { it.start() }
        }

        @Synchronized fun stop() {
            playing = false; generation++
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
