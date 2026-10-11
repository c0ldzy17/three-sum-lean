import Submission.ThreeSum.SharedTraversalScanCosts
import Submission.ThreeSum.ThreeSumColorDriverCosts
import Submission.ThreeSum.LightBruteThreeSum
import Submission.ThreeSum.LightNatPower

/-!
# The exact hybrid cost along every fixed input-magnitude exponent

The exceptional-size and excessive-magnitude branches use the original
triple scan. Once the size reaches the fixed cutoff, every bound at most
n^κ selects the same fast cost. The scalar exponentiation and fixed caller
cost fit within the proved gap between the certificate and target exponents.
-/

namespace ThreeSum.ThreeSumHybridCosts

open Light Parameters StageBounds Filter

set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

def time (κ cutoff n U : ℕ) : ℕ :=
  if n<cutoff ∨ n^κ<U then
    LightBruteThreeSum.time n+LightNatPower.time κ+1000
  else
    LightThreeSumFastDriver.time (SharedTraversalCosts.colorBudget κ n) n+
      LightNatPower.time κ+1000

def fastTime (κ n : ℕ) : ℕ :=
  LightThreeSumFastDriver.time (SharedTraversalCosts.colorBudget κ n) n+
    LightNatPower.time κ+1000

theorem time_of_large {κ cutoff n U : ℕ} (hn : cutoff≤n) (hU : U≤n^κ) :
    time κ cutoff n U=fastTime κ n := by
  simp only [time,fastTime,if_neg (not_or_intro (Nat.not_lt.mpr hn) (Nat.not_lt.mpr hU))]

noncomputable section

theorem fastTime_powerBound (κ : ℕ) : PowerBound (fastTime κ) certificateExponent := by
  have hfast := ThreeSumColorDriverCosts.time_certificate
    (SharedTraversalCosts.color_budget_powerBound κ)
  have hp := (PowerBound.const (LightNatPower.time κ)).mono_exponent
    (show (0 : ℝ)≤certificateExponent by norm_num [certificateExponent])
  have hc := (PowerBound.const 1000).mono_exponent
    (show (0 : ℝ)≤certificateExponent by norm_num [certificateExponent])
  exact (hfast.add_same hp).add_same hc

theorem time_powerBound (κ cutoff : ℕ) :
    PowerBound (fun n => time κ cutoff n (n^κ)) certificateExponent := by
  intro δ hδ
  filter_upwards [fastTime_powerBound κ δ hδ,eventually_ge_atTop cutoff] with n ht hn
  simpa only [time_of_large hn le_rfl] using ht

theorem fastTime_eventually_target (κ : ℕ) :
    ∀ᶠ n : ℕ in atTop, (fastTime κ n : ℝ)≤(n : ℝ)^targetExponent := by
  have hh := fastTime_powerBound κ (targetExponent-certificateExponent)
    (sub_pos.mpr certificate_lt_target)
  simpa only [add_sub_cancel] using hh

/-- One eventual size threshold bounds all admissible natural magnitudes. -/
theorem time_eventually_target_uniform (κ cutoff : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ U : ℕ, U≤n^κ →
      (time κ cutoff n U : ℝ)≤(n : ℝ)^targetExponent := by
  filter_upwards [fastTime_eventually_target κ,eventually_ge_atTop cutoff] with n ht hn
  intro U hU
  simpa only [time_of_large hn hU] using ht

theorem timeUpTo_le_fastTime {κ cutoff n : ℕ} {u : ℝ}
    (hn : cutoff≤n) (hu : u≤(n : ℝ)^(κ : ℝ)) :
    timeUpTo (time κ cutoff) n u≤(fastTime κ n : ℝ) := by
  apply timeUpTo_le
  intro U hU
  have hp : 0≤(n : ℝ)^(κ : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hU' : (U : ℝ)≤(n : ℝ)^(κ : ℝ) := hU.trans (max_le hu hp)
  have hUnat : U≤n^κ := by
    rw [Real.rpow_natCast] at hU'
    exact_mod_cast hU'
  rw [time_of_large hn hUnat]

/-- The finite supremum over all input bounds is exactly the fast branch. -/
theorem timeUpTo_eq_fastTime {κ cutoff n : ℕ} (hn : cutoff≤n) :
    timeUpTo (time κ cutoff) n ((n : ℝ)^(κ : ℝ))=(fastTime κ n : ℝ) := by
  apply le_antisymm (timeUpTo_le_fastTime hn le_rfl)
  have hzero : (0 : ℝ)≤(n : ℝ)^(κ : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hh := le_timeUpTo (time κ cutoff) n (U := 0) (u := (n : ℝ)^(κ : ℝ))
    (by simpa only [Nat.cast_zero] using hzero)
  simpa only [time_of_large hn (Nat.zero_le (n^κ))] using hh

theorem timeUpTo_eventually_target (κ cutoff : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      timeUpTo (time κ cutoff) n ((n : ℝ)^(κ : ℝ))≤(n : ℝ)^targetExponent := by
  filter_upwards [fastTime_eventually_target κ,eventually_ge_atTop cutoff] with n ht hn
  simpa only [timeUpTo_eq_fastTime hn] using ht

theorem time_endStatementBigO (κ cutoff : ℕ) :
    EndStatement.BigO (fun n => time κ cutoff n (n^κ)) (981/500 : Rat) := by
  apply BudgetTime.endStatementBigO_of_eventually_le_rpow (by norm_num)
  have hh := time_powerBound κ cutoff (targetExponent-certificateExponent)
    (sub_pos.mpr certificate_lt_target)
  simpa [targetExponent] using hh

end
end ThreeSum.ThreeSumHybridCosts
