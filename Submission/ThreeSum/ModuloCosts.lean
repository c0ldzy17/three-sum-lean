import Submission.ThreeSum.ModuloRuntime
import Submission.ThreeSum.LightBalancedOffset

/-!
# Finite arithmetic-operation bounds for the complete counting backend

The only input-size dependence outside the Karatsuba term is the number of
original elements times their remainder bit budget. Histogram initialization,
capacity computation and folding are included in the displayed constant.
-/

namespace ThreeSum.ModuloCosts

open KaratsubaInterface

def roundedPower (p : ℕ) : ℕ := 3 ^ Nat.clog 2 p

theorem capacity_le_roundedPower (p : ℕ) : capacity p ≤ roundedPower p :=
  Nat.pow_le_pow_left (by decide) _

theorem log_le_roundedPower (p : ℕ) : Nat.clog 2 p ≤ roundedPower p :=
  (Nat.lt_pow_self (by decide : 1 < 2)).le.trans (capacity_le_roundedPower p)

theorem time_bound (p nA nB nC N U : ℕ)
    (ha : nA ≤ N) (hb : nB ≤ N) (hc : nC ≤ N) :
    LightModuloCounts.time p nA nB nC U ≤
      10000 * (roundedPower p + N*(Nat.log 2 (U+1)+1) + 1) := by
  have hcap := capacity_le_roundedPower p
  have hlog := log_le_roundedPower p
  have hp := (le_capacity p).trans hcap
  have hK : LightKaratsuba.time (Nat.clog 2 p) ≤ 2530*roundedPower p :=
    LightKaratsuba.time_le _
  have hNa := Nat.mul_le_mul_right (Nat.log 2 (U+1)+1) ha
  have hNb := Nat.mul_le_mul_right (Nat.log 2 (U+1)+1) hb
  have hNc := Nat.mul_le_mul_right (Nat.log 2 (U+1)+1) hc
  unfold LightModuloCounts.time LightCapacity.time LightResidueHistogram.time
    LightHistogram.histogramTime LightHistogram.countTime LightCyclic.combinedTime
    LightArray.linearTime LightResidues.residuesTime LightResidues.residueBudget
    LightLookupSum.time
  simp only [Light.fillTime]
  nlinarith

theorem roundedPower_fifth {p : ℕ} (hp : 0 < p) :
    roundedPower p ^ 5 ≤ 2^8*p^8 := by
  have ht : (3 : ℕ)^5 ≤ 2^8 := by norm_num
  calc
    _ = ((3 : ℕ)^5)^(Nat.clog 2 p) := by
      unfold roundedPower
      rw [← pow_mul, Nat.mul_comm (Nat.clog 2 p) 5, pow_mul]
    _ ≤ ((2 : ℕ)^8)^(Nat.clog 2 p) := Nat.pow_le_pow_left ht _
    _ = capacity p ^ 8 := by
      unfold capacity
      rw [← pow_mul, Nat.mul_comm 8 (Nat.clog 2 p), pow_mul]
    _ ≤ (2*p)^8 := Nat.pow_le_pow_left (capacity_lt_twice hp).le _
    _ = _ := by rw [mul_pow]

theorem balance_time_bound (p : ℕ) :
    LightBalancedOffset.time (Nat.clog 2 p) p ≤ 2982*roundedPower p := by
  exact (LightBalancedOffset.time_bound _ _ (le_capacity p)).trans
    (time_with_linear_bound (Nat.clog 2 p) 226)

end ThreeSum.ModuloCosts
