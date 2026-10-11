import Submission.ThreeSum.SharedReportingBankResourceBoundsWantedScalars
import Submission.ThreeSum.EncodedColorPrimeResources

/-! # Exact finite resources for constructing the dense-stop counter

The power-loop bound includes its actual `(base+1)^(J+1)` intermediate.
The modular scoring workspace remains affine in an arbitrary destination.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light Scales BandScales ArithmeticStageBounds GlobalEncoding LocalCoverBounds
open KaratsubaInterface

set_option maxHeartbeats 2300000
set_option maxRecDepth 14000

theorem dense_base_le (n : ℕ) :
    LightDenseCap.base (half n) ≤ (EncodedColorResources.scale n)^3 := by
  have H := EncodedColorResources.local_bounds n
  have hs : scheduleSize (half n) ≤ EncodedColorResources.scale n := by
    have hh := H.rounds
    change scheduleSize (half n)+1 ≤ EncodedColorResources.scale n at hh
    omega
  have hc : localBucketCap (half n) ≤ EncodedColorResources.scale n := by
    have hh := H.cap
    change localBucketCap (half n)+1 ≤ EncodedColorResources.scale n at hh
    omega
  calc
    _ ≤ EncodedColorResources.scale n*(EncodedColorResources.scale n)^2 :=
      Nat.mul_le_mul hs (Nat.pow_le_pow_left hc 2)
    _ = _ := by ring

theorem dense_representation_le (n : ℕ) :
    representationCap (half n) (blocks n) ≤ (EncodedColorResources.scale n)^2 :=
  (wanted_representation_cap_le n).trans
    (Nat.pow_le_pow_left (EncodedColorResources.scale_bounds n).2.2.1 2)

theorem dense_power_le (n : ℕ) :
    (LightDenseCap.base (half n)+1)^(blocks n+1) ≤
      2*(EncodedColorResources.scale n)^6 := by
  have hS : 1 ≤ EncodedColorResources.scale n := by
    have hh := (EncodedColorResources.scale_bounds n).1
    omega
  by_cases hz : LightDenseCap.base (half n)=0
  · rw [hz]
    simp only [zero_add,one_pow]
    have hh : 1 ≤ (EncodedColorResources.scale n)^6 := Nat.one_le_pow _ _ hS
    omega
  · have hb : LightDenseCap.base (half n)+1 ≤ 2*LightDenseCap.base (half n) := by omega
    have hrep : (LightDenseCap.base (half n))^(blocks n) ≤
        (EncodedColorResources.scale n)^2 := dense_representation_le n
    have htwo : 2^(blocks n) ≤ EncodedColorResources.scale n :=
      (EncodedColorResources.powers n).2.2.2
    calc
      _ ≤ (2*LightDenseCap.base (half n))^(blocks n+1) := Nat.pow_le_pow_left hb _
      _ = 2*(2^(blocks n)*(LightDenseCap.base (half n))^(blocks n)*LightDenseCap.base (half n)) := by
        rw [mul_pow,pow_succ,pow_succ]
        ring
      _ ≤ 2*(EncodedColorResources.scale n*(EncodedColorResources.scale n)^2*
          (EncodedColorResources.scale n)^3) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul (Nat.mul_le_mul htwo hrep) (dense_base_le n))
      _ = _ := by ring

theorem dense_cap_word_le (n : ℕ) :
    LightDenseCap.word (half n) (blocks n) ≤ 100*(EncodedColorResources.scale n)^6 := by
  have H := EncodedColorResources.local_bounds n
  have hS : 1 ≤ EncodedColorResources.scale n := by
    have hh := (EncodedColorResources.scale_bounds n).1
    omega
  have hj : blocks n+1 ≤ EncodedColorResources.scale n := (EncodedColorResources.dimensions n).2.1
  have hs : scheduleSize (half n) ≤ EncodedColorResources.scale n := by
    have hh := H.rounds
    change scheduleSize (half n)+1 ≤ EncodedColorResources.scale n at hh
    omega
  have hc : localBucketCap (half n) ≤ EncodedColorResources.scale n := by
    have hh := H.cap
    change localBucketCap (half n)+1 ≤ EncodedColorResources.scale n at hh
    omega
  have hp := dense_power_le n
  have hb := dense_base_le n
  have hcs := Nat.pow_le_pow_left hc 2
  have h1 : 1 ≤ (EncodedColorResources.scale n)^6 := Nat.one_le_pow _ _ hS
  have h16 : EncodedColorResources.scale n ≤ (EncodedColorResources.scale n)^6 :=
    Nat.le_self_pow (by decide) _
  have h26 : (EncodedColorResources.scale n)^2 ≤ (EncodedColorResources.scale n)^6 :=
    Nat.pow_le_pow_right hS (by decide)
  have h36 : (EncodedColorResources.scale n)^3 ≤ (EncodedColorResources.scale n)^6 :=
    Nat.pow_le_pow_right hS (by decide)
  unfold LightDenseCap.word
  omega

theorem dense_score_word_le (n U : ℕ) :
    LightBandWeightedScore.word (maxMod n) n n n (bandSize n)
      (ColorBandBounds.count n (bandSize n)) (LightPrimePool.size (primeWindow n)) U ≤
      5000*(EncodedColorResources.scale n)^6+4*U := by
  have hh := EncodedColorResources.prime_core_word_bound n U
  unfold LightEncodedColorPrimeCore.word at hh
  exact (le_max_right _ _).trans ((le_max_right _ _).trans hh)

theorem dense_score_product_le (n : ℕ) :
    representationCap (half n) (blocks n)*
      (ColorBandBounds.count n (bandSize n)*
        (LightPrimePool.size (primeWindow n)*(bandSize n)^3)) ≤
      9*(EncodedColorResources.scale n)^8 := by
  have hs : LightPrimePool.size (primeWindow n) ≤ 3*EncodedColorResources.scale n :=
    (LightPrimePool.size_le _).trans
      (Nat.mul_le_mul_left 3 (EncodedColorResources.scale_bounds n).2.2.2.2.2)
  have hg : bandSize n ≤ EncodedColorResources.scale n := (EncodedColorResources.dimensions n).2.2.2.1
  calc
    _ ≤ (EncodedColorResources.scale n)^2*((3*(EncodedColorResources.scale n)^2)*
        ((3*EncodedColorResources.scale n)*(EncodedColorResources.scale n)^3)) :=
      Nat.mul_le_mul (dense_representation_le n)
        (Nat.mul_le_mul (EncodedColorResources.count_le n) (Nat.mul_le_mul hs (Nat.pow_le_pow_left hg 3)))
    _ = _ := by ring

/-- Exactly the word reservation of the physical twenty-one-procedure setup. -/
def denseWord (n U : ℕ) : ℕ :=
  LightDenseSetup.word (maxMod n) n n n (bandSize n) (ColorBandBounds.count n (bandSize n))
    (LightPrimePool.size (primeWindow n)) U (half n) (blocks n)+
    n+bandSize n+blocks n+ColorBandBounds.count n (bandSize n)+maxMod n+
    LightPrimePool.size (primeWindow n)+20

def denseCells (n U : ℕ) : ℕ := 4+LightWeightedScore.space 0 (maxMod n) (bandSize n) U
def denseDepth (n : ℕ) : ℕ := Nat.clog 2 (maxMod n)+8

theorem dense_word_le (n U : ℕ) : denseWord n U ≤ 10000*(EncodedColorResources.scale n)^8+4*U := by
  have H := EncodedColorResources.scale_bounds n
  have hS : 1 ≤ EncodedColorResources.scale n := by omega
  have hn := H.2.1
  have hp := H.2.2.2.2.1
  have hy := H.2.2.2.2.2
  have hg := (EncodedColorResources.dimensions n).2.2.2.1
  have hj : blocks n+1 ≤ EncodedColorResources.scale n := (EncodedColorResources.dimensions n).2.1
  have hr := EncodedColorResources.count_le n
  have hs := (LightPrimePool.size_le (primeWindow n)).trans (Nat.mul_le_mul_left 3 hy)
  have hcap := dense_cap_word_le n
  have hscore := dense_score_word_le n U
  have hprod := dense_score_product_le n
  have hrep := dense_representation_le n
  have h1 : 1 ≤ (EncodedColorResources.scale n)^8 := Nat.one_le_pow _ _ hS
  have h18 : EncodedColorResources.scale n ≤ (EncodedColorResources.scale n)^8 :=
    Nat.le_self_pow (by decide) _
  have h28 : (EncodedColorResources.scale n)^2 ≤ (EncodedColorResources.scale n)^8 :=
    Nat.pow_le_pow_right hS (by decide)
  have h68 : (EncodedColorResources.scale n)^6 ≤ (EncodedColorResources.scale n)^8 :=
    Nat.pow_le_pow_right hS (by decide)
  unfold denseWord LightDenseSetup.word
  omega

theorem dense_space_eq (dst n U : ℕ) :
    LightWeightedScore.space (dst+4) (maxMod n) (bandSize n) U=dst+denseCells n U := by
  unfold denseCells LightWeightedScore.space LightModuloCounts.space
  simp only [zero_add]
  omega

theorem dense_cells_le (n U : ℕ) : denseCells n U ≤ 40*EncodedColorResources.scale n+U+20 := by
  have hp := (EncodedColorResources.scale_bounds n).2.2.2.2.1
  have hg := (EncodedColorResources.dimensions n).2.2.2.1
  have hc := EncodedColorResources.capacity_bound n
  have hlogp := Nat.log_le_self 2 (maxMod n+1)
  have hlogU := Nat.log_le_self 2 (U+1)
  unfold denseCells LightWeightedScore.space LightModuloCounts.space
  omega

theorem dense_depth_le (n : ℕ) : denseDepth n ≤ EncodedColorResources.scale n+8 := by
  have hh := (LightBandRawAResources.clog_le_self (maxMod n)).trans
    (EncodedColorResources.scale_bounds n).2.2.2.2.1
  unfold denseDepth
  omega

end ThreeSum.SharedReportingBankResourceBounds
