import Submission.ThreeSum.TernaryPairedCollisionRate
import Submission.ThreeSum.TernaryPairedBudgetSelector

noncomputable section
namespace ThreeSum.TernaryPairedBudgetCollision
open Real TernaryPairedCollisionRate TernaryOversizePrime TernaryCoverScale TernaryLocalParameters

theorem collision_bound {K m n value : ℕ} (hm : 0<m) (hn : 1<n)
    (hp9 : 9<nativePrime K m)
    (hbudget : nativePrime K m^(radixLength m n)*value≤9^(radixLength m n)*n^2) :
    (value : ℝ)≤(n : ℝ)^charge K m := by
  let p := nativePrime K m
  let r := radixLength m n
  have hp : (0 : ℝ)<p := by exact_mod_cast (nativePrime_prime K m).pos
  have hnR : (0 : ℝ)<n := by exact_mod_cast lt_trans Nat.zero_lt_one hn
  have hM : 1<outputSize m := by have := outputSize_ge_sixteen hm; omega
  have hlogM := TernaryPrincipalDimensions.output_log_pos hm
  have hboundR : (p : ℝ)^r*(value : ℝ)≤(9 : ℝ)^r*(n : ℝ)^2 := by
    exact_mod_cast hbudget
  have hfirst : (value : ℝ)≤(9/(p : ℝ))^r*(n : ℝ)^2 := by
    have he : (9/(p : ℝ))^r*(n : ℝ)^2=((9 : ℝ)^r*(n : ℝ)^2)/(p : ℝ)^r := by
      rw [div_pow]
      ring
    rw [he]
    apply (le_div_iff₀ (pow_pos hp r)).mpr
    nlinarith [hboundR]
  have hcover : (n : ℝ)^2≤(outputSize m : ℝ)^r := by
    exact_mod_cast Nat.le_pow_clog hM (n^2)
  have hlogcover := Real.log_le_log (pow_pos hnR 2) hcover
  rw [Real.log_pow,Real.log_pow] at hlogcover
  have hr : 2*Real.log (n : ℝ)/Real.log (outputSize m : ℝ)≤(r : ℝ) := by
    apply (div_le_iff₀ hlogM).mpr
    simpa only [Nat.cast_ofNat] using hlogcover
  have hbase : 0<9/(p : ℝ) := by positivity
  have hbase1 : 9/(p : ℝ)≤1 := (div_le_one hp).mpr (by exact_mod_cast hp9.le)
  have hpow := Real.rpow_le_rpow_of_exponent_ge hbase hbase1 hr
  rw [Real.rpow_natCast] at hpow
  have heq : (9/(p : ℝ))^(2*Real.log (n : ℝ)/Real.log (outputSize m : ℝ))*(n : ℝ)^2=
      (n : ℝ)^charge K m := by
    rw [charge_eq hm,Real.rpow_def_of_pos hbase,←Real.rpow_natCast (n : ℝ) 2,
      Real.rpow_def_of_pos hnR,Real.rpow_def_of_pos hnR,←Real.exp_add]
    congr 1
    dsimp [p]
    push_cast
    ring
  exact hfirst.trans ((mul_le_mul_of_nonneg_right hpow (sq_nonneg (n : ℝ))).trans_eq heq)

end ThreeSum.TernaryPairedBudgetCollision
