import Submission.ThreeSum.BandPrimeCosts

/-!
# Exponent bound for the actual common-prime setup budget

The candidate pool and number of minimum rounds contribute only a
subpolynomial factor. This proves the arithmetic term for the executed
aggregate program; it does not assert completion of the whole solver.
-/

namespace ThreeSum.BandPrimeCosts

open Filter Real Scales BandScales CostLedger Parameters StageBounds HierarchyScales
  ArithmeticStageBounds
open scoped Topology

set_option maxHeartbeats 1400000

noncomputable section

theorem primeDepth_powerBound : PowerBound (primeDepth radix) 0 := by
  apply PowerBound.of_rate
  apply squeeze_zero' _ _ primeDepth_log_ratio_tendsto_zero
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact div_nonneg (Real.log_natCast_nonneg _)
      (Real.log_nonneg (by exact_mod_cast hn))
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact div_le_div_of_nonneg_right (Real.log_le_self (Nat.cast_nonneg _))
      (Real.log_nonneg (by exact_mod_cast hn))

theorem pool_time_powerBound : PowerBound (fun n => LightPrimePool.time (primeWindow n)) 0 := by
  have hh := (PowerBound.const 100000).mul
    ((window_powerBound.add_same (PowerBound.const 1)).pow 3)
  have hh' : PowerBound (fun n => 100000*(primeWindow n+1)^3) 0 := by
    simpa only [mul_zero,zero_add] using hh
  exact powerBound_mono hh' (Eventually.of_forall fun n => pool_time_le (primeWindow n))

theorem prime_size_powerBound : PowerBound (fun n => LightPrimePool.size (primeWindow n)) 0 := by
  have hh := PowerBound.of_rate MassScales.candidateCount_log_rate
  change PowerBound (fun n => (PrimeDensity.candidates (primeWindow n)).card) 0 at hh
  simpa only [LightPrimePool.size_eq_card] using hh

theorem owner_count_powerBound :
    PowerBound (fun n => 3*bandCount n^2+1) (2*(1-(E+bandShift)/5)) := by
  have hc := (PowerBound.const 3).mul ((PowerBound.of_rate bandCount_log_rate).pow 2)
  have hc' : PowerBound (fun n => 3*bandCount n^2) (2*(1-(E+bandShift)/5)) := by
    simpa only [Nat.cast_ofNat,zero_add] using hc
  have he : (0 : ℝ) ≤ 2*(1-(E+bandShift)/5) := by
    have hh := E_bounds.2
    unfold bandShift
    linarith
  exact hc'.add_same ((PowerBound.const 1).mono_exponent he)

/-- Exact exponent of the size-only bound for all executed arithmetic work. -/
theorem timeBudget_powerBound (k : ℕ) :
    PowerBound (timeBudget k) (2+epsilon*(4/5-(2/5)*E-2*bandShift)) := by
  have hdepth := primeDepth_powerBound.add_same (PowerBound.const 1)
  have hsize := (prime_size_powerBound.add_same (PowerBound.const 1)).pow 2
  have hh := ((((PowerBound.const 15).mul hdepth).mul owner_count_powerBound).mul hsize).mul
    (perTriple_powerBound k)
  have heq : (0 : ℝ)+2*(1-(E+bandShift)/5)+0+(8/5)*((E+1/2)/5)=
      2+epsilon*(4/5-(2/5)*E-2*bandShift) := by unfold epsilon; ring
  norm_num only [Nat.cast_ofNat] at hh
  rw [heq] at hh
  have he : (0 : ℝ) ≤ 2+epsilon*(4/5-(2/5)*E-2*bandShift) := by
    have hh := E_bounds.2
    unfold epsilon bandShift
    linarith
  exact (pool_time_powerBound.mono_exponent he).add_same hh

theorem timeBudget_certificate (k : ℕ) : PowerBound (timeBudget k) certificateExponent :=
  (timeBudget_powerBound k).mono_exponent (all_costs_le_certificate _ (by simp [costLedger]))

theorem timeBudget_eventually_target (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, (timeBudget k n : ℝ) ≤ (n : ℝ)^targetExponent := by
  have hh := (timeBudget_certificate k) (targetExponent-certificateExponent)
    (sub_pos.mpr certificate_lt_target)
  simpa only [add_sub_cancel] using hh

theorem timeBudget_endStatementBigO (k : ℕ) :
    EndStatement.BigO (timeBudget k) (981/500 : Rat) := by
  apply BudgetTime.endStatementBigO_of_eventually_le_rpow (by norm_num)
  simpa [targetExponent] using timeBudget_eventually_target k

end
end ThreeSum.BandPrimeCosts
