import Submission.ThreeSum.Parameters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Absorbing the explicit subpolynomial overhead budget

`Parameters` proves the real exponent ledger. This file proves the analytic absorption
step, including an explicit overhead envelope whose four terms account for:

* exhaustive local work on blocks of size proportional to `(log n)^(1/3)`;
* prime-window enumeration on the `exp(O(sqrt(log n)))` scale;
* polynomial local factors raised to `O(log n / (log n)^(1/3))` schedules;
* fixed constants and ordinary polylogarithmic factors.

This file does **not** assert that the algorithm has the stated envelope without a proof.
Its final runtime lemmas explicitly require the eventual upper bound on the actual cost.
Deriving that bound from the deterministic routines, their word sizes, all loop counts,
the integer-rounded block schedule and prime construction remains an algorithmic obligation.
-/

noncomputable section

namespace ThreeSum.Asymptotics

open Filter Real _root_.Asymptotics
open ThreeSum.Parameters
open scoped Topology

set_option maxRecDepth 10000

/-- An explicit vanishing exponent that covers all four overhead scales above. -/
def overheadExponent (C : ℝ) (n : ℕ) : ℝ :=
  C * ((Real.log n) ^ (-(1 / 3 : ℝ)) +
    (Real.log n) ^ (-(1 / 2 : ℝ)) +
    Real.log (Real.log n) / (Real.log n) ^ (1 / 3 : ℝ) +
    (Real.log n)⁻¹)

/-- The overhead budget itself, written as a power to retain exact real semantics. -/
def overheadEnvelope (C : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ overheadExponent C n

theorem log_nat_tendsto_atTop :
    Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem overheadExponent_tendsto_zero (C : ℝ) :
    Tendsto (overheadExponent C) atTop (𝓝 0) := by
  unfold overheadExponent
  have hthird := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
    log_nat_tendsto_atTop
  have hhalf := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
    log_nat_tendsto_atTop
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).tendsto_div_nhds_zero.comp
    log_nat_tendsto_atTop
  have hinv := log_nat_tendsto_atTop.inv_tendsto_atTop
  simpa [Function.comp_def] using
    (hthird.add hhalf |>.add hlog |>.add hinv).const_mul C

/-- Any fixed positive exponent allowance eventually dominates the whole envelope. -/
theorem overheadEnvelope_eventually_le {C d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, overheadEnvelope C n ≤ (n : ℝ) ^ d := by
  have ho := (overheadExponent_tendsto_zero C).eventually (gt_mem_nhds hd)
  filter_upwards [ho, eventually_ge_atTop (1 : ℕ)] with n hn hge
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hge) hn.le

/-- Generic absorption. Its cost hypothesis is explicit, and is not supplied by arithmetic. -/
theorem natCost_isBigO_of_vanishing_exponent {T : ℕ → ℕ} {w : ℕ → ℝ}
    (hw : Tendsto w atTop (𝓝 0))
    (hcost : ∀ᶠ n : ℕ in atTop,
      (T n : ℝ) ≤ (n : ℝ) ^ (certificateExponent + w n)) :
    (fun n : ℕ => (T n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ targetExponent) := by
  have hgap : 0 < targetExponent - certificateExponent := sub_pos.mpr certificate_lt_target
  have hwsmall := hw.eventually (gt_mem_nhds hgap)
  apply Asymptotics.IsBigO.of_norm_eventuallyLE
  filter_upwards [hcost, hwsmall, eventually_ge_atTop (1 : ℕ)] with n hc hw hn
  have hle : (T n : ℝ) ≤ (n : ℝ) ^ targetExponent :=
    hc.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (T n : ℝ)),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ targetExponent)] using hle

/-- The same bridge with the explicit, separately proved overhead scale. -/
theorem natCost_isBigO_of_explicit_envelope {T : ℕ → ℕ} {C : ℝ}
    (hcost : ∀ᶠ n : ℕ in atTop,
      (T n : ℝ) ≤ (n : ℝ) ^ certificateExponent * overheadEnvelope C n) :
    (fun n : ℕ => (T n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ targetExponent) := by
  apply natCost_isBigO_of_vanishing_exponent (overheadExponent_tendsto_zero C)
  filter_upwards [hcost, eventually_ge_atTop (1 : ℕ)] with n hc hn
  rw [overheadEnvelope, ← Real.rpow_add (by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hn))] at hc
  exact hc

end ThreeSum.Asymptotics
