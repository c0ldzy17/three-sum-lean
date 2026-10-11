import Submission.ThreeSum.EncodedColorResourceScale
import Submission.ThreeSum.LightEncodedColorPrimeHost
import Submission.ThreeSum.EncodedColorPipelineData

/-! # Affine storage and finite word bounds for the unchanged prime host -/

namespace ThreeSum.EncodedColorResources

open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open EncodedColorLayout KaratsubaInterface

set_option maxHeartbeats 2400000
set_option maxRecDepth 13000

theorem count_le (n : ℕ) : ColorBandBounds.count n (bandSize n) ≤ 3*(scale n)^2 := by
  have hn : n ≤ scale n := by have h := (scale_bounds n).2.1; omega
  exact (LightBandRawAResources.count_le n (bandSize n)).trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hn 2))

theorem incidence_cap_le (n : ℕ) : EncodedColorStageCosts.incidenceCap n ≤ 3*(scale n)^3 := by
  have hh := Nat.mul_le_mul (dimensions n).2.2.2.1 (count_le n)
  unfold EncodedColorStageCosts.incidenceCap
  nlinarith only [hh]

theorem normalized_cells_bound (n : ℕ) :
    LightBandRawAResources.cells (inputBits n+1) n (bandSize n) ≤ 1000*(scale n)^3 := by
  have hm : SharedReportingBankResourceBounds.magnitude n+1 ≤ scale n := by unfold scale; omega
  have hn := (scale_bounds n).2.1
  apply (LightBandRawAResources.cells_bound n).trans
  unfold LightBandRawAResources.envelope LightBandRawAResources.base
  have hh := Nat.mul_le_mul hm (Nat.pow_le_pow_left hn 2)
  nlinarith only [hh]

theorem normalized_space_bound (free n : ℕ) :
    LightEncodedColorNormalize.space free n ≤ free+1000*(scale n)^3+1 := by
  unfold LightEncodedColorNormalize.space
  rw [LightBandRawAResources.space_eq]
  exact Nat.add_le_add_right (Nat.add_le_add_left (normalized_cells_bound n) free) 1

theorem normalized_end_bound (free n : ℕ) : normalizedEnd free n (bandSize n) ≤ free+1000*(scale n)^3 := by
  have hh : normalizedEnd free n (bandSize n) ≤
      LightBandRawAColor.space (tables free n) (vals free n (bandSize n)) (inputBits n+1) n (bandSize n) :=
    le_max_right _ _
  rw [LightBandRawAResources.space_eq] at hh
  exact hh.trans (Nat.add_le_add_left (normalized_cells_bound n) free)

theorem prime_address_bound (free n : ℕ) : prime free n (bandSize n) ≤ free+1000*(scale n)^3+1 :=
  Nat.add_le_add_right (normalized_end_bound free n) 1

theorem depth_control_bound (n : ℕ) : LightBandPrimeDepth.depth (radix n) (primeWindow n) ≤ scale n := by
  exact ((Nat.log_le_self _ _).trans (Nat.div_le_self _ _)).trans (dimensions n).2.2.2.2

theorem cover_address_bound (free n : ℕ) :
    EncodedColorPipelineData.coverBase free n ≤ free+2000*(scale n)^3 := by
  have hp := prime_address_bound free n
  have hy := (scale_bounds n).2.2.2.2.2
  have hd := depth_control_bound n
  have hb := (scale_bounds n).1
  unfold EncodedColorPipelineData.coverBase cover EncodedColorPrimeData.nextFree
    EncodedColorPrimeData.prefixBase EncodedColorPrimeData.poolBase
  have hp3 : scale n ≤ (scale n)^3 := Nat.le_self_pow (by decide) _
  nlinarith only [hp,hy,hd,hb,hp3]

theorem normalized_word_bound (n U : ℕ) : LightEncodedColorNormalize.word n U ≤ 400*(scale n)^2+9*U := by
  have hb := (scale_bounds n).1
  have hn := (scale_bounds n).2.1
  have hg := (dimensions n).2.2.2.1
  have hW := (Nat.add_le_add_right (LightScales.inputBits_le_self n) 1).trans hn
  have hpow := (LightBandRawAResources.color_power_le n).trans (Nat.mul_le_mul_left 4 hn)
  have hcount := count_le n
  have hn2 := Nat.pow_le_pow_left (show n ≤ scale n by omega) 2
  have hraw := LightBandRawAResources.word_le (inputBits n+1) n (bandSize n) U
  unfold LightEncodedColorNormalize.word LightEncodedColorLayout.word
  nlinarith only [hb,hn,hg,hW,hpow,hcount,hn2,hraw]

theorem capacity_bound (n : ℕ) : capacity (maxMod n) ≤ 2*scale n :=
  (capacity_lt_twice (maxMod_pos n)).le.trans (Nat.mul_le_mul_left 2 (scale_bounds n).2.2.2.2.1)

theorem prime_core_word_bound (n U : ℕ) :
    LightEncodedColorPrimeCore.word (maxMod n) n n n (bandSize n)
      (ColorBandBounds.count n (bandSize n)) (radix n) (primeWindow n) U ≤ 5000*(scale n)^6+4*U := by
  have hb := (scale_bounds n).1
  have hn := (scale_bounds n).2.1
  have hg := (dimensions n).2.2.2.1
  have hM := (dimensions n).2.2.2.2
  have hP := (scale_bounds n).2.2.2.2.1
  have hy := (scale_bounds n).2.2.2.2.2
  have hR := count_le n
  have hs := (LightPrimePool.size_le (primeWindow n)).trans (Nat.mul_le_mul_left 3 hy)
  have hcap := capacity_bound n
  have hg2 : bandSize n+1 ≤ 2*scale n := by omega
  have hkar : LightKaratsuba.wordBound (capacity (maxMod n)) (bandSize n) ≤ 4096*(scale n)^5 := by
    unfold LightKaratsuba.wordBound
    calc
      _ ≤ 128*(2*scale n)^3*(2*scale n)^2 := by gcongr
      _ = _ := by ring
  have hg3 := Nat.pow_le_pow_left hg 3
  have hsg := Nat.mul_le_mul (show LightPrimePool.size (primeWindow n)+1 ≤ 3*scale n+1 by omega) hg3
  have hrg := Nat.mul_le_mul hR (Nat.mul_le_mul hs hg3)
  have hdprod := Nat.mul_le_mul hy (Nat.add_le_add_right hM 4)
  have hp16 : scale n ≤ (scale n)^6 := Nat.le_self_pow (by decide) _
  have hp26 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 2 ≤ 6)
  have hp36 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 3 ≤ 6)
  have hp46 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 4 ≤ 6)
  have hp56 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 5 ≤ 6)
  have hweighted : LightBandWeightedScore.word (maxMod n) n n n (bandSize n)
      (ColorBandBounds.count n (bandSize n)) (LightPrimePool.size (primeWindow n)) U ≤ 5000*(scale n)^6+4*U := by
    unfold LightBandWeightedScore.word LightBandWeightedScoreCell.word LightWeightedScore.word LightModuloCounts.word
    nlinarith only [hb,hn,hg,hP,hR,hkar,hg3,hsg,hrg,hp16,hp26,hp36,hp46,hp56]
  unfold LightEncodedColorPrimeCore.word
  apply max_le
  · unfold LightBandPrimeDepth.word
    nlinarith only [hb,hM,hdprod,hp16,hp26]
  · apply max_le
    · unfold LightPrimePool.word
      nlinarith only [hb,hy,hp16]
    · exact hweighted

theorem prime_word_bound (n U : ℕ) : LightEncodedColorPrimeHost.inputWord n U ≤ 10000*(scale n)^6+9*U := by
  have hb := (scale_bounds n).1
  have hn := (scale_bounds n).2.1
  have hg := (dimensions n).2.2.2.1
  have hM := (dimensions n).2.2.2.2
  have hy := (scale_bounds n).2.2.2.2.2
  have hR := count_le n
  have hnrm := normalized_word_bound n U
  have hcore := prime_core_word_bound n U
  have hp16 : scale n ≤ (scale n)^6 := Nat.le_self_pow (by decide) _
  have hp26 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 2 ≤ 6)
  have hcountEq : LightEncodedColorPrime.count n n n (bandSize n)=ColorBandBounds.count n (bandSize n) := by
    unfold LightEncodedColorPrime.count ColorBandBounds.count
    ring
  have hprime : LightEncodedColorPrime.word (maxMod n) n n n (bandSize n) (radix n) (primeWindow n) U ≤
      6000*(scale n)^6+4*U := by
    unfold LightEncodedColorPrime.word
    rw [hcountEq]
    nlinarith only [hb,hn,hR,hcore,hp16,hp26]
  have hmax : max (LightEncodedColorNormalize.word n U)
      (LightEncodedColorPrime.word (maxMod n) n n n (bandSize n) (radix n) (primeWindow n) U) ≤
      9000*(scale n)^6+9*U := max_le (by nlinarith only [hnrm,hp26]) (by omega)
  unfold LightEncodedColorPrimeHost.inputWord
  nlinarith only [hb,hg,hM,hy,hmax,hp16]

theorem prime_core_space_bound (free n U : ℕ) :
    LightEncodedColorPrimeCore.space free (maxMod n) (bandSize n) (radix n) (primeWindow n) U ≤
      free+40*scale n+U+10 := by
  have hy := (scale_bounds n).2.2.2.2.2
  have hd := depth_control_bound n
  have hp := (scale_bounds n).2.2.2.2.1
  have hg := (dimensions n).2.2.2.1
  have hc := capacity_bound n
  have hlogy := Nat.log_le_self 2 (4*primeWindow n+1)
  have hlogp := Nat.log_le_self 2 (maxMod n+1)
  have hlogU := Nat.log_le_self 2 (U+1)
  unfold LightEncodedColorPrimeCore.space LightPrimePool.space LightBandPrimeChain.space
    LightWeightedScore.space LightModuloCounts.space EncodedColorPrimeData.prefixBase EncodedColorPrimeData.poolBase
  apply max_le
  · omega
  · apply max_le <;> omega

theorem prime_space_bound (free n U : ℕ) :
    LightEncodedColorPrimeHost.inputSpace free n U ≤ free+2000*(scale n)^3+U := by
  have hb := (scale_bounds n).1
  have hnrm := normalized_space_bound free n
  have hprime := prime_address_bound free n
  have hcore := prime_core_space_bound (prime free n (bandSize n)) n U
  have hp3 : scale n ≤ (scale n)^3 := Nat.le_self_pow (by decide) _
  unfold LightEncodedColorPrimeHost.inputSpace
  apply max_le <;> nlinarith only [hb,hnrm,hprime,hcore,hp3]

theorem prime_depth_bound (n : ℕ) : LightEncodedColorPrimeHost.depth n ≤ 10*scale n := by
  have hb := (scale_bounds n).1
  have hn := (scale_bounds n).2.1
  have hW := (Nat.add_le_add_right (LightScales.inputBits_le_self n) 1).trans hn
  have hp := (scale_bounds n).2.2.2.2.1
  have hraw := LightBandRawAResources.depth_le (inputBits n+1) n (bandSize n)
  have hc := (LightBandRawAResources.clog_le_self (maxMod n)).trans hp
  unfold LightEncodedColorPrimeHost.depth
  apply max_le <;> omega

end ThreeSum.EncodedColorResources
