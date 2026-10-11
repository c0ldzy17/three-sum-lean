import Submission.ThreeSum.EncodedColorCoverResources
import Submission.ThreeSum.EncodedColorPrimeResources
import Submission.ThreeSum.EncodedColorSourceResources

/-! # Finite affine resource bounds for balanced wanted records and shared sources -/

namespace ThreeSum.EncodedColorResources

open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open KaratsubaInterface

set_option maxHeartbeats 2400000
set_option maxRecDepth 13000

theorem wanted_source_base_bound (free n : ℕ) :
    EncodedColorWantedCosts.sourceBase free (radix n) (half n) (blocks n)
      (EncodedColorStageCosts.incidenceCap n) ≤ free+100*(scale n)^5 := by
  have hb := (scale_bounds n).1
  have hlen := incidence_cap_le n
  have hG := totalKeys_le n
  have hM := (dimensions n).2.2.2.2
  have hkey := key_end_bound free n
  have hp5 : scale n ≤ (scale n)^5 := Nat.le_self_pow (by decide) _
  have hp25 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 2 ≤ 5)
  have hp35 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 3 ≤ 5)
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul_left 3 hlen) hG
  have hdiv := Nat.div_le_self
    (3*EncodedColorStageCosts.incidenceCap n*LightGuardedWanted.totalKeys (half n) (blocks n)) (radix n)
  rw [EncodedColorWantedCosts.sourceBase_eq]
  nlinarith only [hb,hlen,hG,hM,hkey,hprod,hdiv,hp5,hp25,hp35]

theorem wanted_space_bound (free n U : ℕ) :
    EncodedColorWantedCosts.space free (maxMod n) (radix n) (half n) (blocks n) U
      (EncodedColorStageCosts.incidenceCap n) ≤ free+200*(scale n)^5+U := by
  have hb := (scale_bounds n).1
  have hlen := incidence_cap_le n
  have hG := totalKeys_le n
  have hM := (dimensions n).2.2.2.2
  have hkey := key_end_bound free n
  have hbound := keyBound_le n
  have hbase := wanted_source_base_bound free n
  have hcover := cover_space_bound free n
  have hcapacity := (capacity_lt_twice (radix_pos n)).le.trans (Nat.mul_le_mul_left 2 hM)
  have hlogU := Nat.log_le_self 2 (U+1)
  have hlogK := Nat.log_le_self 2 (LightGuardedWanted.keyBound (maxMod n) (half n) (blocks n)+1)
  have hlogM := Nat.log_le_self 2 (radix n+radix n+1)
  have hp5 : scale n ≤ (scale n)^5 := Nat.le_self_pow (by decide) _
  have hp25 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 2 ≤ 5)
  have hp35 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 3 ≤ 5)
  have hp45 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 4 ≤ 5)
  have hpair : LightWantedSetup.pairBase
      (LightGuardedWanted.wantedFree free (half n) (blocks n) (EncodedColorStageCosts.incidenceCap n))
      (3*EncodedColorStageCosts.incidenceCap n) (LightGuardedWanted.totalKeys (half n) (blocks n)) (radix n) ≤
      free+100*(scale n)^5 := by
    unfold EncodedColorWantedCosts.sourceBase at hbase
    omega
  have hlogs : max (Nat.log 2 (LightGuardedWanted.keyBound (maxMod n) (half n) (blocks n)+1)+2)
      (Nat.log 2 (radix n+radix n+1)+2) ≤ 3*(scale n)^4+2*scale n+3 := by omega
  unfold EncodedColorWantedCosts.space
  refine max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ ?_)))
  · omega
  · unfold LightRawAKeys.space
    omega
  · unfold LightOriginalOffset.space LightGuardedWanted.wantedFree
    nlinarith only [hb,hkey,hlen,hG,hcapacity,hlogK,hbound,hp5,hp25,hp35,hp45]
  · unfold LightSourceResidues.space
    nlinarith only [hb,hpair,hlogs,hp5,hp45]
  · omega

theorem wanted_word_bound (n U : ℕ) :
    LightGuardedWanted.word (maxMod n) (radix n) (half n) (blocks n) U
      (EncodedColorStageCosts.incidenceCap n) ≤ 150000*(scale n)^9+4*U := by
  have hb := (scale_bounds n).1
  have hlen := incidence_cap_le n
  have hG := totalKeys_le n
  have hM := (dimensions n).2.2.2.2
  have hP := (scale_bounds n).2.2.2.2.1
  have hbound := keyBound_le n
  have hcover := cover_word_bound n
  have hcapacity := (capacity_lt_twice (radix_pos n)).le.trans (Nat.mul_le_mul_left 2 hM)
  have hp3 : scale n ≤ (scale n)^3 := Nat.le_self_pow (by decide) _
  have hp23 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 2 ≤ 3)
  have hp9 : scale n ≤ (scale n)^9 := Nat.le_self_pow (by decide) _
  have hp49 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 4 ≤ 9)
  have hp59 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 5 ≤ 9)
  have hN : 3*EncodedColorStageCosts.incidenceCap n+LightGuardedWanted.totalKeys (half n) (blocks n)+1 ≤
      11*(scale n)^3 := by nlinarith only [hb,hlen,hG,hp3,hp23]
  have hkar : LightKaratsuba.wordBound (capacity (radix n))
      (3*EncodedColorStageCosts.incidenceCap n+LightGuardedWanted.totalKeys (half n) (blocks n)) ≤
      123904*(scale n)^9 := by
    unfold LightKaratsuba.wordBound
    calc
      _ ≤ 128*(2*scale n)^3*(11*(scale n)^3)^2 := by gcongr
      _ = _ := by ring
  have hbalanced : LightBalancedWanted.word (radix n) (3*EncodedColorStageCosts.incidenceCap n)
      (LightGuardedWanted.totalKeys (half n) (blocks n))
      (LightGuardedWanted.keyBound (maxMod n) (half n) (blocks n)) ≤ 150000*(scale n)^9 := by
    unfold LightBalancedWanted.word LightOriginalOffset.word LightSourceResidues.word
    apply max_le <;> nlinarith only [hb,hM,hbound,hkar,hp9,hp49]
  unfold LightGuardedWanted.word
  refine max_le ?_ (max_le ?_ ?_)
  · nlinarith only [hcover,hp59]
  · unfold LightRawAKeys.word
    nlinarith only [hb,hP,hp9]
  · omega

theorem stage_space_bound (free n U : ℕ) :
    EncodedColorStageCosts.space free n (maxMod n) (radix n) U (EncodedColorStageCosts.incidenceCap n) ≤
      free+300*(scale n)^5+U := by
  have hw := wanted_space_bound free n U
  have hb := wanted_source_base_bound free n
  have hs := source_space_bound (EncodedColorStageCosts.sourceBase free n (radix n)
    (EncodedColorStageCosts.incidenceCap n)) n U
  unfold EncodedColorStageCosts.sourceBase at hs
  dsimp only [half,blocks] at hw hb
  unfold EncodedColorStageCosts.space EncodedColorStageCosts.sourceBase
  apply max_le <;> omega

theorem stage_word_bound (n U : ℕ) :
    EncodedColorStageCosts.word n (maxMod n) (radix n) U (EncodedColorStageCosts.incidenceCap n) ≤
      150000*(scale n)^9+4*U := by
  have hw := wanted_word_bound n U
  have hs := source_word_bound n U
  have hp39 := Nat.pow_le_pow_right (by have h := (scale_bounds n).1; omega : 1 ≤ scale n) (by decide : 3 ≤ 9)
  unfold EncodedColorStageCosts.word LightEncodedColorWantedSources.word
  exact max_le hw (by omega)

theorem stage_depth_bound (n : ℕ) :
    EncodedColorStageCosts.depth n (radix n) (EncodedColorStageCosts.incidenceCap n) ≤ 20*(scale n)^3 := by
  have hb := (scale_bounds n).1
  have hL := (local_bounds n).width
  have hJ := (dimensions n).2.1
  have hW := (dimensions n).1
  have hM := (dimensions n).2.2.2.2
  have hc := (LightBandRawAResources.clog_le_self (radix n)).trans hM
  have hlen := incidence_cap_le n
  have hp3 : scale n ≤ (scale n)^3 := Nat.le_self_pow (by decide) _
  unfold EncodedColorStageCosts.depth LightEncodedColorWantedSources.depth
  rw [← width_eq]
  change max (512*half n+blocks n+Nat.clog 2 (radix n)+3*EncodedColorStageCosts.incidenceCap n+13)
    (width n+18) ≤ _
  apply max_le <;> nlinarith only [hb,hL,hJ,hW,hc,hlen,hp3]

end ThreeSum.EncodedColorResources
