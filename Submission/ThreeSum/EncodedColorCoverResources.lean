import Submission.ThreeSum.EncodedColorResourceScale

/-! # Polynomial bounds for the retained local cover and complete global key array -/

namespace ThreeSum.EncodedColorResources

open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000

theorem local_count_le (n : ℕ) : LightGlobalKeys.localCount (half n) ≤ (scale n)^2 := by
  have hS : scheduleSize (half n) ≤ scale n := by have h := (local_bounds n).rounds; omega
  simpa only [LightGlobalKeys.localCount,pow_two] using Nat.mul_le_mul hS (layer_le n)

theorem after_cover_bound (free n : ℕ) : LightCoverKeys.afterCover free (half n) ≤ free+scale n := by
  have hs := LightLocalCoverInitResources.space_bound free (half n)
  have he := LightLocalCoverRetention.nextFree_le_space (LightLocalCoverInit.base free) (half n)
  have hm : LightLocalCoverLayout.space (LightLocalCoverInit.base free) (half n) ≤
      LightLocalCoverInit.space free (half n) := le_max_right _ _
  exact ((he.trans hm).trans hs).trans (Nat.add_le_add_left (scale_bounds n).2.2.2.1 free)

theorem global_keys_space_bound (free n : ℕ) :
    LightGlobalKeys.space free (half n) (blocks n) ≤ free+10*(scale n)^3 := by
  have hb := (scale_bounds n).1
  have hL := (local_bounds n).width
  have hJ := (dimensions n).2.1
  have hl := layer_le n
  have hm := local_count_le n
  have hG := totalKeys_le n
  have hp3 : scale n ≤ (scale n)^3 := Nat.le_self_pow (by decide) _
  have hp23 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 2 ≤ 3)
  have hprod := Nat.mul_le_mul hJ (Nat.add_le_add_right hG 1)
  have hs := LightRadixKeys.space_bound (LightGlobalKeys.scratch free (half n))
    (LightGlobalKeys.localCount (half n)) (blocks n) (LightGlobalKeys.localCount_pos (half n))
  change LightRadixKeys.space (LightGlobalKeys.scratch free (half n)) (LightGlobalKeys.localCount (half n)) (blocks n) ≤
    LightGlobalKeys.scratch free (half n)+(blocks n+1)*(LightGuardedWanted.totalKeys (half n) (blocks n)+1) at hs
  have hradix : LightRadixKeys.space (LightGlobalKeys.scratch free (half n))
      (LightGlobalKeys.localCount (half n)) (blocks n) ≤ free+10*(scale n)^3 := by
    unfold LightGlobalKeys.scratch at hs ⊢
    nlinarith only [hb,hl,hm,hprod,hs,hp3,hp23]
  unfold LightGlobalKeys.space
  apply max_le
  · unfold LightLocalKeyRow.space LightGlobalKeys.scratch
    nlinarith only [hb,hL,hl,hm,hp3,hp23]
  · exact hradix

theorem cover_space_bound (free n : ℕ) :
    LightCoverKeys.space free (half n) (blocks n) ≤ free+20*(scale n)^3 := by
  have hb := (scale_bounds n).1
  have hlocal := LightLocalCoverInitResources.space_bound free (half n)
  change LightLocalCoverInit.space free (half n) ≤ free+localEnvelope n at hlocal
  have henv := (scale_bounds n).2.2.2.1
  have hafter := after_cover_bound free n
  have hglobal := global_keys_space_bound (LightCoverKeys.afterCover free (half n)) n
  have hp3 : scale n ≤ (scale n)^3 := Nat.le_self_pow (by decide) _
  unfold LightCoverKeys.space
  apply max_le <;> nlinarith only [hlocal,henv,hafter,hglobal,hp3]

theorem key_end_bound (free n : ℕ) :
    LightCoverKeyData.keyEnd free (half n) (blocks n) ≤ free+20*(scale n)^3 :=
  (LightCoverKeyData.keyEnd_le_space free (half n) (blocks n)).trans (cover_space_bound free n)

theorem global_keys_word_bound (n : ℕ) : LightGlobalKeys.word (half n) (blocks n) ≤ 1000*(scale n)^5 := by
  have hb := (scale_bounds n).1
  have H := local_bounds n
  have hL := H.width
  have hP := H.prime
  have hS := H.rounds
  have hJ := (dimensions n).2.1
  have hpow : 2^(512*half n+1) ≤ scale n := by have hh := H.maskPower; omega
  have hprod := Nat.mul_le_mul hL (show localPrime (half n) ≤ scale n by omega)
  have hLP := Nat.mul_le_mul (show 512*half n ≤ scale n by omega) (show localPrime (half n) ≤ scale n by omega)
  have hkey := Nat.mul_le_mul (show localPrime (half n) ≤ scale n by omega)
    (Nat.mul_le_mul hLP (radix_power_le n))
  have hp5 : scale n ≤ (scale n)^5 := Nat.le_self_pow (by decide) _
  have hp25 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 2 ≤ 5)
  unfold LightGlobalKeys.word LightLocalKeys.word LightLocalKeyRow.word LightOneHot.word
    LightRadixKeys.word LightRadixRows.word
  nlinarith only [hb,hL,hP,hS,hJ,hpow,hprod,hLP,hkey,hp5,hp25]

theorem cover_word_bound (n : ℕ) : LightCoverKeys.word (half n) (blocks n) ≤ 1000*(scale n)^5 := by
  have hlocal := (LightLocalCoverInitResources.word_bound (half n)).trans (scale_bounds n).2.2.2.1
  have hp5 : scale n ≤ (scale n)^5 := Nat.le_self_pow (by decide) _
  unfold LightCoverKeys.word
  exact max_le (by omega) (global_keys_word_bound n)

end ThreeSum.EncodedColorResources
