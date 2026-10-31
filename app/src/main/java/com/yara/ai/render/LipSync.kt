package com.yara.ai.render

import kotlinx.coroutines.delay
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.flow

data class LipFrame(val jawOpen: Float, val mouthWide: Float)

object LipSync {

    /**
     * Emit jaw/mouth morph frames from reply text so the avatar's mouth
     * moves in sync with TTS.
     */
    fun forText(text: String, durationMs: Long): Flow<LipFrame> = flow {
        val chars: String = text.lowercase().filter { it.isLetter() || it == ' ' }
        val vowels = "aeiou"
        val step: Long = (durationMs / chars.length.coerceAtLeast(1).toLong())
            .coerceIn(45L, 160L)

        for (ch in chars) {
            val vowel: Boolean = vowels.contains(ch)
            val jaw: Float = when {
                ch == ' ' -> 0f
                ch == 'm' || ch == 'b' || ch == 'p' -> 0.08f
                vowel -> 0.65f
                else -> 0.3f
            }
            val wide: Float = when {
                vowel -> 0.45f
                ch == 'm' || ch == 'b' || ch == 'p' -> 0.05f
                else -> 0.25f
            }
            emit(LipFrame(jaw, wide))
            delay(step)
            emit(LipFrame(jaw * 0.25f, wide))
            delay(step / 2)
        }
        emit(LipFrame(0f, 0f))
    }
}
