import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Analytic and rational parameter certificate for the proposed 3SUM algorithm

This module certifies the real-variable inequalities and the resulting exponent ledger.
It does not by itself prove that an implementation has those costs: the reduction,
cover, encoding, reporting, arithmetic and machine-model lemmas are separate obligations.

All decimal-looking constants below are exact rational numbers. There are no numerical
oracles, admitted declarations, or native-code decision procedures in this certificate.
-/

noncomputable section

namespace ThreeSum.Parameters

open Set Real

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048

/-- Binary entropy measured in bits. -/
noncomputable def entropy (t : ℝ) : ℝ := Real.binEntropy t / Real.log 2

/-- Half of the output-support exponent at `c = 256`. -/
noncomputable def E : ℝ := 128 * entropy (1 / 256)

/-- The vertex-multiplicity exponent of the trimmed cover at `c = 256`. -/
noncomputable def kappa : ℝ :=
  512 * entropy (1 / 512) - 256 * entropy (1 / 256) - 1

/-- Entropy loss when the output layer is reduced by a fraction `t`. -/
noncomputable def gamma (t : ℝ) : ℝ :=
  256 * entropy (1 / 256) - 256 * entropy ((1 - t) / 256)

/-- A rational polynomial below `gamma` on the interval used by the algorithm. -/
def phi (t : ℝ) : ℝ := 799 / 100 * t + 18 / 25 * t ^ 2 + 6 / 25 * t ^ 3

def phiDeriv (t : ℝ) : ℝ := 799 / 100 + 36 / 25 * t + 18 / 25 * t ^ 2

def epsilon : ℝ := 1 / 5
def bandShift : ℝ := -(1 / 20)
def boxSaving : ℝ := 191 / 1000
def terminalFraction : ℝ := 13 / 20
def entropyRatio : ℝ := 277 / 1000
def initialTheta : ℝ := 1 / 25
def tangentPoint : ℝ := 17 / 100
def kappaCap : ℝ := 3 / 2000
def certificateExponent : ℝ := 9809107 / 5000000
def targetExponent : ℝ := 981 / 500

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem log_two_lower : (2 / 3 : ℝ) < Real.log 2 := by
  linarith [Real.log_two_gt_d9]

theorem log_two_upper : Real.log 2 < (25 / 36 : ℝ) := by
  linarith [Real.log_two_lt_d9]

/-! ## Exact integer witnesses for the logarithmic comparisons -/

theorem power_255 : (2 : ℕ) ^ 799 < 255 ^ 100 := by norm_num

theorem power_tangent_left : (100 : ℕ) ^ 100 < 2 ^ 27 * 83 ^ 100 := by norm_num

theorem power_tangent_right :
    (10000 : ℕ) ^ 500 < 2 ^ 1413 * 1411 ^ 500 := by norm_num

theorem power_initial_entropy : (25 : ℕ) ^ 100 < 2 ^ 25 * 24 ^ 96 := by norm_num

theorem power_karatsuba : (3 : ℕ) ^ 5 < 2 ^ 8 := by norm_num

theorem log_255_lower : (799 / 100 : ℝ) * Real.log 2 < Real.log 255 := by
  have hp : (2 : ℝ) ^ 799 < 255 ^ 100 := by exact_mod_cast power_255
  have h := Real.log_lt_log (by positivity : (0 : ℝ) < 2 ^ 799) hp
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith

theorem karatsuba_log_bound : Real.log 3 / Real.log 2 < (8 / 5 : ℝ) := by
  have hp : (3 : ℝ) ^ 5 < 2 ^ 8 := by exact_mod_cast power_karatsuba
  have h := Real.log_lt_log (by positivity : (0 : ℝ) < 3 ^ 5) hp
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  apply (div_lt_iff₀ log_two_pos).2
  linarith

theorem entropy_eq (t : ℝ) :
    entropy t = (-t * Real.log t - (1 - t) * Real.log (1 - t)) / Real.log 2 := by
  simp only [entropy, Real.binEntropy, Real.log_inv]
  ring

private theorem log_256 : Real.log 256 = 8 * Real.log 2 := by
  have h := Real.log_pow (2 : ℝ) 8
  norm_num at h
  exact h

private theorem log_512 : Real.log 512 = 9 * Real.log 2 := by
  have h := Real.log_pow (2 : ℝ) 9
  norm_num at h
  exact h

theorem E_formula : E = 4 + 255 * Real.log (256 / 255) / (2 * Real.log 2) := by
  norm_num [E, entropy, Real.binEntropy]
  rw [log_256]
  field_simp
  ring

theorem E_bounds : (4 : ℝ) < E ∧ E < 19 / 4 := by
  have hpos : 0 < Real.log (256 / 255 : ℝ) := Real.log_pos (by norm_num)
  have hlt : Real.log (256 / 255 : ℝ) < 1 / 255 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 256 / 255)
      (by norm_num : (256 / 255 : ℝ) ≠ 1)
    norm_num at h
    exact h
  rw [E_formula]
  constructor
  · have : 0 < 255 * Real.log (256 / 255 : ℝ) / (2 * Real.log 2) := by positivity
    linarith
  · have : 255 * Real.log (256 / 255 : ℝ) / (2 * Real.log 2) < 3 / 4 := by
      apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.log 2)).2
      linarith [log_two_lower]
    linarith

/-- A one-term atanh estimate, proved by Mathlib's uniform remainder theorem. -/
theorem log_ratio_upper_one {x : ℝ} (hx : |x| < 1) :
    Real.log ((1 + x) / (1 - x)) ≤ 2 * x + 2 * |x| ^ 3 / (1 - x ^ 2) := by
  have h := (abs_le.mp (Real.sum_range_sub_log_div_le hx 1)).2
  norm_num [Finset.sum_range_succ] at h
  rw [show 2 * |x| ^ 3 / (1 - x ^ 2) = 2 * (|x| ^ 3 / (1 - x ^ 2)) by ring]
  linarith

theorem kappa_formula :
    kappa * Real.log 2 =
      256 * Real.log (512 / 511) + 255 * Real.log (510 / 511) := by
  have h510 : Real.log (510 : ℝ) = Real.log 2 + Real.log 255 := by
    rw [show (510 : ℝ) = 2 * 255 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  norm_num [kappa, entropy, Real.binEntropy]
  rw [Real.log_div (by norm_num : (512 : ℝ) ≠ 0) (by norm_num : (511 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (256 : ℝ) ≠ 0) (by norm_num : (255 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (510 : ℝ) ≠ 0) (by norm_num : (511 : ℝ) ≠ 0),
    log_256, log_512, h510]
  field_simp
  ring

theorem kappa_bound : kappa < kappaCap := by
  have hp := log_ratio_upper_one (x := (1 / 1023 : ℝ)) (by norm_num)
  have hm := log_ratio_upper_one (x := -(1 / 1021 : ℝ)) (by norm_num)
  norm_num at hp hm
  have hnum : kappa * Real.log 2 ≤ (1 / 1021 : ℝ) := by
    rw [kappa_formula]
    linarith
  have hsmall : kappa * Real.log 2 < (3 / 2000) * Real.log 2 := by
    linarith [log_two_lower]
  exact (mul_lt_mul_iff_of_pos_right log_two_pos).mp hsmall

theorem kappa_positive : 0 < kappa := by
  have hp := (abs_le.mp (Real.sum_range_sub_log_div_le
    (by norm_num : |(1 / 1023 : ℝ)| < 1) 1)).1
  have hm := (abs_le.mp (Real.sum_range_sub_log_div_le
    (by norm_num : |(-(1 / 1021) : ℝ)| < 1) 1)).1
  norm_num [Finset.sum_range_succ] at hp hm
  have hnum : (1 / 1023 : ℝ) ≤ kappa * Real.log 2 := by
    rw [kappa_formula]
    linarith
  by_contra h
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) log_two_pos.le
  linarith

/-- Coefficients of the tangent to binary entropy at `17/100`. -/
noncomputable def tangentA : ℝ := (Real.log 100 - Real.log 83) / Real.log 2
noncomputable def tangentB : ℝ := (Real.log 83 - Real.log 17) / Real.log 2

theorem tangentA_bound : tangentA < (27 / 100 : ℝ) := by
  have hp : (100 : ℝ) ^ 100 < 2 ^ 27 * 83 ^ 100 := by
    exact_mod_cast power_tangent_left
  have h := Real.log_lt_log (by positivity : (0 : ℝ) < 100 ^ 100) hp
  rw [Real.log_mul (by positivity : (2 : ℝ) ^ 27 ≠ 0)
    (by positivity : (83 : ℝ) ^ 100 ≠ 0)] at h
  simp only [Real.log_pow] at h
  norm_num at h
  apply (div_lt_iff₀ log_two_pos).2
  linarith

theorem tangentAB_bound : tangentA + tangentB / 2 < (1413 / 1000 : ℝ) := by
  have hp : (10000 : ℝ) ^ 500 < 2 ^ 1413 * 1411 ^ 500 := by
    exact_mod_cast power_tangent_right
  have h := Real.log_lt_log (by positivity : (0 : ℝ) < 10000 ^ 500) hp
  rw [Real.log_mul (by positivity : (2 : ℝ) ^ 1413 ≠ 0)
    (by positivity : (1411 : ℝ) ^ 500 ≠ 0)] at h
  simp only [Real.log_pow] at h
  have h10000 : Real.log (10000 : ℝ) = 2 * Real.log 100 := by
    rw [show (10000 : ℝ) = 100 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have h1411 : Real.log (1411 : ℝ) = Real.log 83 + Real.log 17 := by
    rw [show (1411 : ℝ) = 83 * 17 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  rw [h10000, h1411] at h
  norm_num at h
  have heq : tangentA + tangentB / 2 =
      (Real.log 100 - Real.log 83 / 2 - Real.log 17 / 2) / Real.log 2 := by
    unfold tangentA tangentB
    ring
  rw [heq, div_lt_iff₀ log_two_pos]
  linarith

theorem initial_entropy_bound : entropy initialTheta < (1 / 4 : ℝ) := by
  have hp : (25 : ℝ) ^ 100 < 2 ^ 25 * 24 ^ 96 := by
    exact_mod_cast power_initial_entropy
  have h := Real.log_lt_log (by positivity : (0 : ℝ) < 25 ^ 100) hp
  rw [Real.log_mul (by positivity : (2 : ℝ) ^ 25 ≠ 0)
    (by positivity : (24 : ℝ) ^ 96 ≠ 0)] at h
  simp only [Real.log_pow] at h
  norm_num at h
  norm_num [initialTheta, entropy, Real.binEntropy]
  rw [Real.log_div (by norm_num : (25 : ℝ) ≠ 0) (by norm_num : (24 : ℝ) ≠ 0),
    div_lt_iff₀ log_two_pos]
  linarith

/-! ## Exact rational inequalities for the schedule -/

theorem phi_zero : phi 0 = 0 := by norm_num [phi]

theorem phi_half : phi (1 / 2) = (841 / 200 : ℝ) := by norm_num [phi]

theorem phi_initial : boxSaving - 2 * bandShift < phi initialTheta := by
  norm_num [boxSaving, bandShift, phi, initialTheta]

theorem schedule_maximum :
    (boxSaving - 2 * bandShift + terminalFraction) / (1 - terminalFraction)
      = (941 / 350 : ℝ) := by
  norm_num [boxSaving, bandShift, terminalFraction]

theorem schedule_room : (941 / 350 : ℝ) < phi (1 / 2) := by norm_num [phi]

theorem phi_derivative_bound {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    phiDeriv t ≤ (889 / 100 : ℝ) := by
  dsimp [phiDeriv]
  have ht2 : t ^ 2 ≤ (1 / 4 : ℝ) := by
    nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  nlinarith [ht.1, ht.2]

theorem phi_derivative_lt_nine {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    phiDeriv t < 9 := lt_of_le_of_lt (phi_derivative_bound ht) (by norm_num)

theorem tangent_left_polynomial :
    entropyRatio * (1 + phi tangentPoint - tangentPoint * phiDeriv tangentPoint)
      = (1691143447 / 6250000000 : ℝ) := by
  norm_num [entropyRatio, tangentPoint, phi, phiDeriv]

theorem tangent_right_polynomial :
    entropyRatio * (1 + phi tangentPoint + (1 / 2 - tangentPoint) * phiDeriv tangentPoint)
      = (4418702061 / 3125000000 : ℝ) := by
  norm_num [entropyRatio, tangentPoint, phi, phiDeriv]

theorem tangent_left_margin :
    (27 / 100 : ℝ) < entropyRatio *
      (1 + phi tangentPoint - tangentPoint * phiDeriv tangentPoint) := by
  rw [tangent_left_polynomial]
  norm_num

theorem tangent_right_margin :
    (1413 / 1000 : ℝ) < entropyRatio *
      (1 + phi tangentPoint + (1 / 2 - tangentPoint) * phiDeriv tangentPoint) := by
  rw [tangent_right_polynomial]
  norm_num

theorem entropy_tangent {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    entropy t ≤ tangentA + tangentB * t := by
  have hu : (17 / 100 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hd := Real.hasDerivAt_binEntropy (p := (17 / 100 : ℝ)) (by norm_num) (by norm_num)
  have hconc := Real.strictConcave_binEntropy.concaveOn
  have htan : Real.binEntropy t ≤ Real.binEntropy (17 / 100) +
      (t - 17 / 100) * (Real.log (1 - 17 / 100) - Real.log (17 / 100)) := by
    rcases lt_trichotomy t (17 / 100) with h | h | h
    · have hs := hconc.le_slope_of_hasDerivAt ht hu h hd
      rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at hs
      nlinarith
    · subst t
      simp
    · have hs := hconc.slope_le_of_hasDerivAt hu ht h hd
      rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h)] at hs
      nlinarith
  have heq : Real.binEntropy (17 / 100) +
      (t - 17 / 100) * (Real.log (1 - 17 / 100) - Real.log (17 / 100)) =
      Real.log 100 - Real.log 83 + t * (Real.log 83 - Real.log 17) := by
    norm_num [Real.binEntropy]
    rw [Real.log_div (by norm_num : (100 : ℝ) ≠ 0) (by norm_num : (17 : ℝ) ≠ 0),
      Real.log_div (by norm_num : (100 : ℝ) ≠ 0) (by norm_num : (83 : ℝ) ≠ 0),
      Real.log_div (by norm_num : (83 : ℝ) ≠ 0) (by norm_num : (100 : ℝ) ≠ 0),
      Real.log_div (by norm_num : (17 : ℝ) ≠ 0) (by norm_num : (100 : ℝ) ≠ 0)]
    ring
  rw [heq] at htan
  unfold entropy tangentA tangentB
  have hdiv := div_le_div_of_nonneg_right htan log_two_pos.le
  apply le_of_le_of_eq hdiv
  ring

theorem phi_above_tangent {t : ℝ} (ht : 0 ≤ t) :
    phi tangentPoint + (t - tangentPoint) * phiDeriv tangentPoint ≤ phi t := by
  have hfact : phi t - (phi tangentPoint + (t - tangentPoint) * phiDeriv tangentPoint) =
      (t - tangentPoint) ^ 2 * (18 / 25 + (6 / 25) * (t + 2 * tangentPoint)) := by
    unfold phi phiDeriv
    ring
  have hnonneg : 0 ≤ (t - tangentPoint) ^ 2 *
      (18 / 25 + (6 / 25) * (t + 2 * tangentPoint)) := by
    apply mul_nonneg (sq_nonneg _)
    dsimp [tangentPoint]
    linarith
  linarith

/-- A single supporting line gives a uniform bound, including both endpoints. -/
theorem entropy_phi_bound {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    entropy t < entropyRatio * (1 + phi t) := by
  have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, by linarith [ht.2]⟩
  have hl := lt_trans tangentA_bound tangent_left_margin
  have hr := lt_trans tangentAB_bound tangent_right_margin
  have hline : tangentA + tangentB * t <
      entropyRatio * (1 + phi tangentPoint + (t - tangentPoint) * phiDeriv tangentPoint) := by
    by_cases hhalf : t < 1 / 2
    · have hp := mul_lt_mul_of_pos_left hl (by linarith : 0 < 1 - 2 * t)
      have hq := mul_le_mul_of_nonneg_left hr.le (by linarith [ht.1] : 0 ≤ 2 * t)
      nlinarith
    · have heq : t = 1 / 2 := by linarith [ht.2]
      rw [heq]
      simpa [div_eq_mul_inv] using hr
  have hpoly := mul_le_mul_of_nonneg_left (phi_above_tangent ht.1)
    (by norm_num [entropyRatio] : 0 ≤ entropyRatio)
  have hent := entropy_tangent ht1
  linarith

/-- The two nonnegative initial terms of the convergent logarithm series. -/
theorem neg_log_one_sub_lower {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    t + t ^ 2 / 2 ≤ -Real.log (1 - t) := by
  have habs : |t| < 1 := by rwa [abs_of_nonneg ht0]
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one habs
  have h := sum_le_hasSum (Finset.range 2)
    (fun n _ => div_nonneg (pow_nonneg ht0 _) (by positivity)) hs
  norm_num [Finset.sum_range_succ] at h
  exact h

noncomputable def gammaNumerator (t : ℝ) : ℝ :=
  (1 - t) * Real.log (1 - t) + (255 + t) * Real.log (255 + t) - 255 * Real.log 255

theorem gamma_formula {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    gamma t = gammaNumerator t / Real.log 2 := by
  have h1 : (1 - t : ℝ) ≠ 0 := by linarith [ht.2]
  have h255 : (255 + t : ℝ) ≠ 0 := by linarith [ht.1]
  unfold gamma
  rw [entropy_eq, entropy_eq]
  rw [show 1 - (1 - t) / 256 = (255 + t) / 256 by ring]
  norm_num
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (256 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (255 : ℝ) ≠ 0) (by norm_num : (256 : ℝ) ≠ 0),
    Real.log_div h1 (by norm_num : (256 : ℝ) ≠ 0),
    Real.log_div h255 (by norm_num : (256 : ℝ) ≠ 0)]
  simp only [Real.log_one]
  unfold gammaNumerator
  ring

theorem hasDerivAt_phi (t : ℝ) : HasDerivAt phi (phiDeriv t) t := by
  have hd := (((hasDerivAt_id t).const_mul (799 / 100)).add
    (((hasDerivAt_id t).pow 2).const_mul (18 / 25))).add
      (((hasDerivAt_id t).pow 3).const_mul (6 / 25))
  change HasDerivAt phi _ t at hd
  apply hd.congr_deriv
  dsimp [phiDeriv]
  ring

theorem phi_increment_bound {u v : ℝ}
    (hu : u ∈ Icc (0 : ℝ) (1 / 2)) (hv : v ∈ Icc (0 : ℝ) (1 / 2)) (huv : u < v) :
    phi v - phi u < 9 * (v - u) := by
  apply (convex_Icc (0 : ℝ) (1 / 2)).image_sub_lt_mul_sub_of_deriv_lt
    (fun y _ => (hasDerivAt_phi y).continuousAt.continuousWithinAt)
    (fun y _ => (hasDerivAt_phi y).differentiableAt.differentiableWithinAt)
    (fun y hy => ?_) u hu v hv huv
  rw [(hasDerivAt_phi y).deriv]
  exact phi_derivative_lt_nine (interior_subset hy)

theorem phi_step_rounding {u v m K : ℝ}
    (hu : u ∈ Icc (0 : ℝ) (1 / 2)) (hv : v ∈ Icc (0 : ℝ) (1 / 2))
    (hm : 0 < m) (hstep : v - u = 1 / m) (hprev : phi u < K) :
    phi v < K + 9 / m := by
  have huv : u < v := by
    have : 0 < 1 / m := by positivity
    linarith
  have h := phi_increment_bound hu hv huv
  rw [hstep] at h
  rw [show 9 / m = 9 * (1 / m) by ring]
  linarith

theorem hasDerivAt_gammaNumerator {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    HasDerivAt gammaNumerator (Real.log (255 + t) - Real.log (1 - t)) t := by
  have h1 : (1 - t : ℝ) ≠ 0 := by linarith [ht.2]
  have h255 : (255 + t : ℝ) ≠ 0 := by linarith [ht.1]
  have hd1 := (hasDerivAt_id t).const_sub 1
  have hd255 := (hasDerivAt_id t).const_add 255
  have hd := ((hd1.mul (hd1.log h1)).add (hd255.mul (hd255.log h255))).sub_const
    (255 * Real.log 255)
  change HasDerivAt gammaNumerator _ t at hd
  apply hd.congr_deriv
  dsimp only [id_eq]
  field_simp [h1, h255]
  <;> ring

theorem gamma_derivative_above_phi {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    Real.log 2 * phiDeriv t ≤ Real.log (255 + t) - Real.log (1 - t) := by
  have hlog : Real.log 255 ≤ Real.log (255 + t) :=
    Real.log_le_log (by norm_num) (by linarith [ht.1])
  have hneg := neg_log_one_sub_lower ht.1 (by linarith [ht.2])
  have hpoly : 0 ≤ (36 / 25 : ℝ) * t + (18 / 25) * t ^ 2 := by
    nlinarith [ht.1, sq_nonneg t]
  have hprod := mul_le_mul_of_nonneg_right log_two_upper.le hpoly
  dsimp [phiDeriv]
  nlinarith [log_255_lower]

/-- The cubic switch is valid for the entire interval used by every level. -/
theorem phi_le_gamma {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    phi t ≤ gamma t := by
  let F : ℝ → ℝ := fun y => gammaNumerator y - Real.log 2 * phi y
  let F' : ℝ → ℝ := fun y =>
    Real.log (255 + y) - Real.log (1 - y) - Real.log 2 * phiDeriv y
  have hd : ∀ y ∈ Icc (0 : ℝ) (1 / 2), HasDerivAt F (F' y) y := by
    intro y hy
    exact (hasDerivAt_gammaNumerator hy).sub ((hasDerivAt_phi y).const_mul (Real.log 2))
  have hm : MonotoneOn F (Icc (0 : ℝ) (1 / 2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) (1 / 2))
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
    intro y hy
    exact sub_nonneg.mpr (gamma_derivative_above_phi (interior_subset hy))
  have hmono := hm (by constructor <;> norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) (1 / 2)) ht ht.1
  have hzero : F 0 = 0 := by norm_num [F, gammaNumerator, phi]
  rw [hzero] at hmono
  rw [gamma_formula ht, le_div_iff₀ log_two_pos]
  dsimp [F] at hmono
  nlinarith

/-- The rational threshold tested by the integer cubic switch. -/
def switchThreshold (a : ℝ) : ℝ := (boxSaving - 2 * bandShift + a) / (1 - a)

theorem switchThreshold_upper {a : ℝ} (ha : a ∈ Icc (0 : ℝ) terminalFraction) :
    switchThreshold a ≤ 941 / 350 := by
  have hden : 0 < 1 - a := by dsimp [terminalFraction] at ha; linarith [ha.2]
  rw [switchThreshold, div_le_iff₀ hden]
  dsimp [boxSaving, bandShift, terminalFraction] at *
  linarith [ha.2]

theorem switch_box_bound {a t : ℝ} (ha : a ∈ Icc (0 : ℝ) terminalFraction)
    (ht : t ∈ Icc (0 : ℝ) (1 / 2)) (hswitch : switchThreshold a ≤ phi t) :
    boxSaving ≤ 2 * bandShift - a + (1 - a) * gamma t := by
  have hden : 0 < 1 - a := by dsimp [terminalFraction] at ha; linarith [ha.2]
  have hs := (div_le_iff₀ hden).mp hswitch
  have hg := mul_le_mul_of_nonneg_left (phi_le_gamma ht) hden.le
  linarith

/-- The entropy charge including the exact `9/mu` integer-rounding allowance. -/
theorem switch_entropy_bound {a t mu : ℝ}
    (ha : a ∈ Icc (0 : ℝ) terminalFraction) (ht : t ∈ Icc (0 : ℝ) (1 / 2))
    (hmu : 0 < mu)
    (hswitch : phi t < switchThreshold a + 9 / ((1 - a) * mu)) :
    (1 - a) * entropy t <
      entropyRatio * (1 + boxSaving - 2 * bandShift) + 9 * entropyRatio / mu := by
  have hden : 0 < 1 - a := by dsimp [terminalFraction] at ha; linarith [ha.2]
  have hr : 0 < entropyRatio := by norm_num [entropyRatio]
  have hh := mul_lt_mul_of_pos_left (entropy_phi_bound ht) hden
  have hp := mul_lt_mul_of_pos_left hswitch (mul_pos hden hr)
  have hid : (1 - a) * entropyRatio *
      (1 + (switchThreshold a + 9 / ((1 - a) * mu))) =
      entropyRatio * (1 + boxSaving - 2 * bandShift) + 9 * entropyRatio / mu := by
    unfold switchThreshold
    field_simp [ne_of_gt hden, ne_of_gt hmu]
    ring
  rw [← hid]
  nlinarith

theorem recursive_saving_value :
    1 / 2 - bandShift - kappaCap - entropyRatio * (1 + boxSaving - 2 * bandShift)
      = (190893 / 1000000 : ℝ) := by
  norm_num [bandShift, kappaCap, entropyRatio, boxSaving]

theorem recursive_exponent_value :
    2 - epsilon *
      (1 / 2 - bandShift - kappaCap - entropyRatio * (1 + boxSaving - 2 * bandShift))
      = certificateExponent := by
  norm_num [epsilon, bandShift, kappaCap, entropyRatio, boxSaving, certificateExponent]

theorem certificate_margin : targetExponent - certificateExponent = (893 / 5000000 : ℝ) := by
  norm_num [targetExponent, certificateExponent]

theorem certificate_lt_target : certificateExponent < targetExponent := by
  norm_num [certificateExponent, targetExponent]

/-! ## The real-valued ledger, before the algorithmic cost lemmas are applied -/

/-- The twelve charges in the proposed implementation, including reading the input. -/
def costLedger (e k h : ℝ) : List ℝ :=
  [2 * epsilon * e,
   1 + epsilon * (e - bandShift),
   2 - epsilon * boxSaving,
   2 - epsilon * (1 / 2 + bandShift - h),
   2 - epsilon * (1 / 2 - bandShift - k - entropyRatio * (1 + boxSaving - 2 * bandShift)),
   2 - epsilon * (terminalFraction - 1 / 2 - bandShift - k),
   epsilon * (8 / 5) * (e + 1 / 2),
   2 + epsilon * (4 / 5 - (2 / 5) * e - 2 * bandShift),
   1 + epsilon * (1 / 2 - bandShift),
   2 - epsilon * (e + bandShift),
   2 - 2 * epsilon * (e + bandShift),
   1]

/-- Uniform ledger bounds; the hypotheses must be supplied by the analytic certificate. -/
theorem cost_ledger_bounds {e k h : ℝ} (he0 : 4 < e) (he1 : e < 19 / 4)
    (hk : k < kappaCap) (hh : h < 1 / 4) :
    2 * epsilon * e < 19 / 10 ∧
    1 + epsilon * (e - bandShift) < 49 / 25 ∧
    2 - epsilon * boxSaving = 9809 / 5000 ∧
    2 - epsilon * (1 / 2 + bandShift - h) < 49 / 25 ∧
    2 - epsilon * (1 / 2 - bandShift - k - entropyRatio * (1 + boxSaving - 2 * bandShift))
      < certificateExponent ∧
    2 - epsilon * (terminalFraction - 1 / 2 - bandShift - k) < 19603 / 10000 ∧
    epsilon * (8 / 5) * (e + 1 / 2) < 42 / 25 ∧
    2 + epsilon * (4 / 5 - (2 / 5) * e - 2 * bandShift) < 93 / 50 ∧
    1 + epsilon * (1 / 2 - bandShift) = 111 / 100 ∧
    2 - epsilon * (e + bandShift) < 121 / 100 ∧
    2 - 2 * epsilon * (e + bandShift) < 21 / 50 ∧
    epsilon * (e + bandShift) < 1 := by
  dsimp [epsilon, bandShift, boxSaving, entropyRatio, terminalFraction,
    certificateExponent, kappaCap] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem all_ledger_caps_le_certificate :
    ∀ t ∈ ([19 / 10, 49 / 25, 9809 / 5000, 19603 / 10000,
      42 / 25, 93 / 50, 111 / 100, 121 / 100, 21 / 50, 1] : List ℝ),
      t ≤ certificateExponent := by
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [certificateExponent]

/-- The ledger instantiated with the entropy-defined parameters, with no analytic hypotheses. -/
theorem all_costs_le_certificate :
    ∀ t ∈ costLedger E kappa (entropy initialTheta), t ≤ certificateExponent := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    cost_ledger_bounds E_bounds.1 E_bounds.2 kappa_bound initial_entropy_bound
  intro t ht
  simp only [costLedger, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    dsimp [certificateExponent] at * <;> linarith

/-- Each certified exponent is strictly smaller than `1.962`. -/
theorem all_costs_lt_target :
    ∀ t ∈ costLedger E kappa (entropy initialTheta), t < targetExponent := by
  intro t ht
  exact lt_of_le_of_lt (all_costs_le_certificate t ht) certificate_lt_target

end ThreeSum.Parameters
