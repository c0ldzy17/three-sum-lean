import Submission.ThreeSum.StageBounds

/-!
# A uniform size-only budget for the six principal stage counts

Both mass budgets are executable integer divisions of the concrete size
majorants.  The final bound is uniform in the input-dependent masses: the
eventual size threshold is chosen before `W`, `H`, `P`, or `H1` are quantified.
This remains a theorem about the specified finite work quantities, not a
claim that a complete machine has been proved to execute within them.
-/

namespace ThreeSum.UniformStageBounds

open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales ThreeSum.StageBounds
open scoped Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def wantedBudget (n : ℕ) : ℕ := wantedNumerator n / radix n

def falseBudget (k n : ℕ) : ℕ := falseNumerator k n / radix n

def workBudget (C k n : ℕ) : ℕ := amplifiedCoreWork C wantedBudget (falseBudget k) n

theorem wanted_le_budget {n W : ℕ} (hW : W * radix n ≤ wantedNumerator n) :
    W ≤ wantedBudget n := (Nat.le_div_iff_mul_le (radix_pos n)).mpr hW

theorem wantedBudget_mul_le (n : ℕ) : wantedBudget n * radix n ≤ wantedNumerator n :=
  Nat.div_mul_le_self _ _

noncomputable section

theorem false_le_budget {n k P H H1 : ℕ}
    (hscore : P * H ≤ scoreLoss k n * H1)
    (hinit : H1 ≤ candidateCount n * rawTripleBound n)
    (hmod : radix n ≤ primeLoss radix n * P) : H ≤ falseBudget k n := by
  have hr := false_mass_le hscore hinit hmod
  rw [falseMajorant, le_div_iff₀ (show (0 : ℝ) < radix n by exact_mod_cast radix_pos n)] at hr
  apply (Nat.le_div_iff_mul_le (radix_pos n)).mpr
  exact_mod_cast hr

theorem wantedBudget_powerBound : PowerBound wantedBudget (2 - (1 / 2 + bandShift) / 5) :=
  wanted_powerBound (Filter.Eventually.of_forall wantedBudget_mul_le)

theorem falseBudget_powerBound (k : ℕ) : PowerBound (falseBudget k) (2 - (1 / 2 - bandShift) / 5) := by
  intro d hd
  filter_upwards [falseMajorant_eventually_le k hd] with n hn
  have hb : (falseBudget k n : ℝ) ≤ falseMajorant k n := by
    rw [falseMajorant, le_div_iff₀ (show (0 : ℝ) < radix n by exact_mod_cast radix_pos n)]
    exact_mod_cast Nat.div_mul_le_self (falseNumerator k n) (radix n)
  exact hb.trans hn

theorem budget_initial_powerBound :
    PowerBound (initialCount wantedBudget)
      (2 - epsilon * (1 / 2 + bandShift - entropy initialTheta)) :=
  initial_powerBound (Filter.Eventually.of_forall wantedBudget_mul_le)

theorem budget_active_powerBound (k : ℕ) :
    PowerBound (activeCount (falseBudget k))
      (2 - epsilon * (1 / 2 - bandShift - kappa - entropyRatio * (1 + boxSaving - 2 * bandShift))) := by
  have hG : PowerBound microPartitions 0 := by
    intro d hd
    simpa only [zero_add] using microPartitions_subpolynomial hd
  have hQ : PowerBound allQueryTerms ((entropyRatio * (1 + boxSaving - 2 * bandShift)) / 5) :=
    fun _ hd => allQueryTerms_eventually_le hd
  have hh := (((falseBudget_powerBound k).mul
    (PowerBound.of_rate representationBound_log_rate)).mul hG).mul hQ
  have heq : ((2 - (1 / 2 - bandShift) / 5) + kappa / 5 + 0) +
      (entropyRatio * (1 + boxSaving - 2 * bandShift)) / 5 =
      2 - epsilon * (1 / 2 - bandShift - kappa - entropyRatio * (1 + boxSaving - 2 * bandShift)) := by
    unfold epsilon
    ring
  rw [heq] at hh
  exact hh

theorem budget_terminal_powerBound (k : ℕ) :
    PowerBound (terminalCount (falseBudget k))
      (2 - epsilon * (terminalFraction - 1 / 2 - bandShift - kappa)) := by
  have hh := (((PowerBound.const 2).mul (falseBudget_powerBound k)).mul
    (PowerBound.of_rate representationBound_log_rate)).mul (PowerBound.of_rate terminalChoices_log_rate)
  have heq : ((0 : ℝ) + (2 - (1 / 2 - bandShift) / 5) + kappa / 5) +
      (1 - terminalFraction) / 5 =
      2 - epsilon * (terminalFraction - 1 / 2 - bandShift - kappa) := by unfold epsilon; ring
  rw [heq] at hh
  exact hh

theorem budget_core_powerBound (k : ℕ) :
    PowerBound (coreWork wantedBudget (falseBudget k)) certificateExponent := by
  have ht := table_powerBound.mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have he := encoder_powerBound.mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have hb := boxes_powerBound.mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have hi := budget_initial_powerBound.mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have ha := (budget_active_powerBound k).mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have hf := (budget_terminal_powerBound k).mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  exact ((((ht.add_same he).add_same hb).add_same hi).add_same ha).add_same hf

theorem workBudget_powerBound (C k : ℕ) : PowerBound (workBudget C k) certificateExponent := by
  intro d hd
  have hh := ((concreteOverhead_powerBound C).mul (budget_core_powerBound k)) d hd
  simpa only [workBudget, amplifiedCoreWork, zero_add] using hh

theorem workBudget_eventually_target (C k : ℕ) :
    ∀ᶠ n : ℕ in atTop, (workBudget C k n : ℝ) ≤ (n : ℝ) ^ targetExponent := by
  have hh := (workBudget_powerBound C k)
    (targetExponent - certificateExponent) (sub_pos.mpr certificate_lt_target)
  have hid : certificateExponent + (targetExponent - certificateExponent) = targetExponent := by ring
  rw [hid] at hh
  exact hh

theorem coreWork_mono {W W' H H' : ℕ → ℕ} {n : ℕ}
    (hW : W n ≤ W' n) (hH : H n ≤ H' n) : coreWork W H n ≤ coreWork W' H' n := by
  have hi := Nat.mul_le_mul_right (queryTerms n 0) hW
  have ha := Nat.mul_le_mul_right (allQueryTerms n)
    (Nat.mul_le_mul_right (microPartitions n) (Nat.mul_le_mul_right (representationBound n) hH))
  have ht := Nat.mul_le_mul_right (terminalChoices n)
    (Nat.mul_le_mul_right (representationBound n) (Nat.mul_le_mul_left 2 hH))
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.le_refl _) hi) ha) ht

theorem amplified_core_le_budget {n C k W H P H1 : ℕ}
    (hW : W * radix n ≤ wantedNumerator n)
    (hscore : P * H ≤ scoreLoss k n * H1)
    (hinit : H1 ≤ candidateCount n * rawTripleBound n)
    (hmod : radix n ≤ primeLoss radix n * P) :
    amplifiedCoreWork C (fun _ => W) (fun _ => H) n ≤ workBudget C k n := by
  have hm := coreWork_mono (n := n) (W := fun _ => W) (W' := wantedBudget)
    (H := fun _ => H) (H' := falseBudget k)
    (wanted_le_budget hW) (false_le_budget hscore hinit hmod)
  exact Nat.mul_le_mul_left (concreteOverhead C n) hm

/-- The size threshold is selected before all input-dependent masses. -/
theorem uniform_amplified_core_eventually (C k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ W H P H1 : ℕ,
      W * radix n ≤ wantedNumerator n →
      P * H ≤ scoreLoss k n * H1 →
      H1 ≤ candidateCount n * rawTripleBound n →
      radix n ≤ primeLoss radix n * P →
      (amplifiedCoreWork C (fun _ => W) (fun _ => H) n : ℝ) ≤ (n : ℝ) ^ targetExponent := by
  filter_upwards [workBudget_eventually_target C k] with n hn
  intro W H P H1 hW hs hi hm
  have hb := amplified_core_le_budget (C := C) hW hs hi hm
  exact (show (amplifiedCoreWork C (fun _ => W) (fun _ => H) n : ℝ) ≤ workBudget C k n by
    exact_mod_cast hb).trans hn

theorem workBudget_isBigO (C k : ℕ) :
    (fun n : ℕ => (workBudget C k n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ targetExponent) := by
  apply _root_.Asymptotics.IsBigO.of_norm_eventuallyLE
  filter_upwards [workBudget_eventually_target C k] with n hn
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (workBudget C k n)),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) n) targetExponent)] using hn

end
end ThreeSum.UniformStageBounds
