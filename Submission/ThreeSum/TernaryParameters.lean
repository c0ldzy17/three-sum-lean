import Submission.ThreeSum.BinomialEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Exact rational and logarithmic certificate for the three-symbol construction.
Every logarithm bound is proved from Mathlib's finite atanh remainder theorem.
This module certifies parameters and the real-valued ledger, not algorithm costs.
There are no axioms, admitted proofs, or native-code decision procedures.
-/

noncomputable section
namespace ThreeSum.TernaryParameters

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048

def pi0 : ℝ := (81204903 / 100000000 : ℝ)
def pi1 : ℝ := (317207 / 2000000 : ℝ)
def pi2 : ℝ := (2934747 / 100000000 : ℝ)
def alpha0 : ℝ := (90113327 / 100000000 : ℝ)
def alpha1 : ℝ := (1113553 / 12500000 : ℝ)
def alpha2 : ℝ := (978249 / 100000000 : ℝ)
def three : ℝ := 3
def y : ℝ := (3632479 / 20000000 : ℝ)
def bankArg : ℝ := (485844483685441 / 400000000000000 : ℝ)
def z : ℝ := (7523953 / 100000000 : ℝ)
def queryArg1 : ℝ := (107523953 / 100000000 : ℝ)
def queryArg2 : ℝ := (10809005168746209 / 10000000000000000 : ℝ)
def deficit : ℝ := (268969 / 20000000 : ℝ)
def mean : ℝ := pi1 + 2 * pi2
def certificateExponent : ℝ := 19203 / 10000
def targetExponent : ℝ := 1921 / 1000
def Hpi : ℝ := (-pi0 * Real.log pi0 - pi1 * Real.log pi1 -
  pi2 * Real.log pi2) / Real.log 2
def Halpha : ℝ := (-alpha0 * Real.log alpha0 - alpha1 * Real.log alpha1 -
  alpha2 * Real.log alpha2) / Real.log 2
def partitionEntropy : ℝ := (pi1 * Real.log 2 + pi2 * Real.log three) / Real.log 2
def bankEntropy : ℝ := (Real.log bankArg - (mean - deficit) * Real.log y) / Real.log 2
def queryEntropy : ℝ := (pi1 * Real.log queryArg1 + pi2 * Real.log queryArg2 -
  deficit * Real.log z) / Real.log 2

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

private theorem log_two_bounds :
    (6931471 / 10000000 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (433217 / 625000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |((1 / 3 : ℝ) : ℝ)| < 1) 8
  have hratio : ((1 + (1 / 3 : ℝ)) / (1 - (1 / 3 : ℝ)) : ℝ) = 2 := by
    norm_num []
  rw [hratio] at h
  norm_num [Finset.sum_range_succ] at h
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1, hh.2]

private def normalized_pi0 : ℝ := (81204903 / 50000000 : ℝ)

private theorem log_normalized_pi0_bounds :
    (2424763 / 5000000 : ℝ) ≤ Real.log normalized_pi0 ∧ Real.log normalized_pi0 ≤ (4849527 / 10000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |((31204903 / 131204903 : ℝ) : ℝ)| < 1) 8
  have hratio : ((1 + (31204903 / 131204903 : ℝ)) / (1 - (31204903 / 131204903 : ℝ)) : ℝ) = normalized_pi0 := by
    norm_num [normalized_pi0]
  rw [hratio] at h
  norm_num [Finset.sum_range_succ] at h
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1, hh.2]

theorem log_pi0_bounds :
    (-1040973 / 5000000 : ℝ) ≤ Real.log pi0 ∧ Real.log pi0 ≤ (-260243 / 1250000 : ℝ) := by
  have hu := log_normalized_pi0_bounds
  have htwo := log_two_bounds
  have heq : pi0 = normalized_pi0 / (2 : ℝ) ^ 1 := by norm_num [pi0, normalized_pi0]
  rw [heq, Real.log_div (by norm_num [normalized_pi0]) (by norm_num),
    Real.log_pow]
  norm_num
  constructor <;> linarith [hu.1, hu.2, htwo.1, htwo.2]

private def normalized_pi1 : ℝ := (317207 / 250000 : ℝ)

private theorem log_normalized_pi1_bounds :
    (297617 / 1250000 : ℝ) ≤ Real.log normalized_pi1 ∧ Real.log normalized_pi1 ≤ (2380937 / 10000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |((67207 / 567207 : ℝ) : ℝ)| < 1) 8
  have hratio : ((1 + (67207 / 567207 : ℝ)) / (1 - (67207 / 567207 : ℝ)) : ℝ) = normalized_pi1 := by
    norm_num [normalized_pi1]
  rw [hratio] at h
  norm_num [Finset.sum_range_succ] at h
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1, hh.2]

theorem log_pi1_bounds :
    (-460337 / 250000 : ℝ) ≤ Real.log pi1 ∧ Real.log pi1 ≤ (-4603369 / 2500000 : ℝ) := by
  have hu := log_normalized_pi1_bounds
  have htwo := log_two_bounds
  have heq : pi1 = normalized_pi1 / (2 : ℝ) ^ 3 := by norm_num [pi1, normalized_pi1]
  rw [heq, Real.log_div (by norm_num [normalized_pi1]) (by norm_num),
    Real.log_pow]
  norm_num
  constructor <;> linarith [hu.1, hu.2, htwo.1, htwo.2]

private def normalized_pi2 : ℝ := (2934747 / 1562500 : ℝ)

private theorem log_normalized_pi2_bounds :
    (6303341 / 10000000 : ℝ) ≤ Real.log normalized_pi2 ∧ Real.log normalized_pi2 ≤ (3151671 / 5000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |((1372247 / 4497247 : ℝ) : ℝ)| < 1) 8
  have hratio : ((1 + (1372247 / 4497247 : ℝ)) / (1 - (1372247 / 4497247 : ℝ)) : ℝ) = normalized_pi2 := by
    norm_num [normalized_pi2]
  rw [hratio] at h
  norm_num [Finset.sum_range_succ] at h
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1, hh.2]

theorem log_pi2_bounds :
    (-35285491 / 10000000 : ℝ) ≤ Real.log pi2 ∧ Real.log pi2 ≤ (-8821371 / 2500000 : ℝ) := by
  have hu := log_normalized_pi2_bounds
  have htwo := log_two_bounds
  have heq : pi2 = normalized_pi2 / (2 : ℝ) ^ 6 := by norm_num [pi2, normalized_pi2]
  rw [heq, Real.log_div (by norm_num [normalized_pi2]) (by norm_num),
    Real.log_pow]
  norm_num
  constructor <;> linarith [hu.1, hu.2, htwo.1, htwo.2]

private def normalized_alpha0 : ℝ := (90113327 / 50000000 : ℝ)

private theorem log_normalized_alpha0_bounds :
    (117809 / 200000 : ℝ) ≤ Real.log normalized_alpha0 ∧ Real.log normalized_alpha0 ≤ (5890451 / 10000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |((40113327 / 140113327 : ℝ) : ℝ)| < 1) 8
  have hratio : ((1 + (40113327 / 140113327 : ℝ)) / (1 - (40113327 / 140113327 : ℝ)) : ℝ) = normalized_alpha0 := by
    norm_num [normalized_alpha0]
  rw [hratio] at h
  norm_num [Finset.sum_range_succ] at h
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1, hh.2]

theorem log_alpha0_bounds :
    (-520511 / 5000000 : ℝ) ≤ Real.log alpha0 ∧ Real.log alpha0 ≤ (-52051 / 500000 : ℝ) := by
  have hu := log_normalized_alpha0_bounds
  have htwo := log_two_bounds
  have heq : alpha0 = normalized_alpha0 / (2 : ℝ) ^ 1 := by norm_num [alpha0, normalized_alpha0]
  rw [heq, Real.log_div (by norm_num [normalized_alpha0]) (by norm_num),
    Real.log_pow]
  norm_num
  constructor <;> linarith [hu.1, hu.2, htwo.1, htwo.2]

private def normalized_alpha1 : ℝ := (1113553 / 781250 : ℝ)

private theorem log_normalized_alpha1_bounds :
    (1772079 / 5000000 : ℝ) ≤ Real.log normalized_alpha1 ∧ Real.log normalized_alpha1 ≤ (3544159 / 10000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |((332303 / 1894803 : ℝ) : ℝ)| < 1) 8
  have hratio : ((1 + (332303 / 1894803 : ℝ)) / (1 - (332303 / 1894803 : ℝ)) : ℝ) = normalized_alpha1 := by
    norm_num [normalized_alpha1]
  rw [hratio] at h
  norm_num [Finset.sum_range_succ] at h
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1, hh.2]

theorem log_alpha1_bounds :
    (-2418173 / 1000000 : ℝ) ≤ Real.log alpha1 ∧ Real.log alpha1 ≤ (-967269 / 400000 : ℝ) := by
  have hu := log_normalized_alpha1_bounds
  have htwo := log_two_bounds
  have heq : alpha1 = normalized_alpha1 / (2 : ℝ) ^ 4 := by norm_num [alpha1, normalized_alpha1]
  rw [heq, Real.log_div (by norm_num [normalized_alpha1]) (by norm_num),
    Real.log_pow]
  norm_num
  constructor <;> linarith [hu.1, hu.2, htwo.1, htwo.2]

private def normalized_alpha2 : ℝ := (978249 / 781250 : ℝ)

private theorem log_normalized_alpha2_bounds :
    (224869 / 1000000 : ℝ) ≤ Real.log normalized_alpha2 ∧ Real.log normalized_alpha2 ≤ (2248691 / 10000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |((196999 / 1759499 : ℝ) : ℝ)| < 1) 8
  have hratio : ((1 + (196999 / 1759499 : ℝ)) / (1 - (196999 / 1759499 : ℝ)) : ℝ) = normalized_alpha2 := by
    norm_num [normalized_alpha2]
  rw [hratio] at h
  norm_num [Finset.sum_range_succ] at h
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1, hh.2]

theorem log_alpha2_bounds :
    (-23135807 / 5000000 : ℝ) ≤ Real.log alpha2 ∧ Real.log alpha2 ≤ (-23135803 / 5000000 : ℝ) := by
  have hu := log_normalized_alpha2_bounds
  have htwo := log_two_bounds
  have heq : alpha2 = normalized_alpha2 / (2 : ℝ) ^ 7 := by norm_num [alpha2, normalized_alpha2]
  rw [heq, Real.log_div (by norm_num [normalized_alpha2]) (by norm_num),
    Real.log_pow]
  norm_num
  constructor <;> linarith [hu.1, hu.2, htwo.1, htwo.2]

private def normalized_three : ℝ := (3 / 2 : ℝ)

private theorem log_normalized_three_bounds :
    (4054651 / 10000000 : ℝ) ≤ Real.log normalized_three ∧ Real.log normalized_three ≤ (1013663 / 2500000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |((1 / 5 : ℝ) : ℝ)| < 1) 8
  have hratio : ((1 + (1 / 5 : ℝ)) / (1 - (1 / 5 : ℝ)) : ℝ) = normalized_three := by
    norm_num [normalized_three]
  rw [hratio] at h
  norm_num [Finset.sum_range_succ] at h
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1, hh.2]

theorem log_three_bounds :
    (5493061 / 5000000 : ℝ) ≤ Real.log three ∧ Real.log three ≤ (2746531 / 2500000 : ℝ) := by
  have hu := log_normalized_three_bounds
  have htwo := log_two_bounds
  have heq : three = normalized_three * (2 : ℝ) ^ 1 := by norm_num [three, normalized_three]
  rw [heq, Real.log_mul (by norm_num [normalized_three]) (by norm_num),
    Real.log_pow]
  norm_num
  constructor <;> linarith [hu.1, hu.2, htwo.1, htwo.2]

private def normalized_y : ℝ := (3632479 / 2500000 : ℝ)

private theorem log_normalized_y_bounds :
    (1868123 / 5000000 : ℝ) ≤ Real.log normalized_y ∧ Real.log normalized_y ≤ (3736247 / 10000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |((1132479 / 6132479 : ℝ) : ℝ)| < 1) 8
  have hratio : ((1 + (1132479 / 6132479 : ℝ)) / (1 - (1132479 / 6132479 : ℝ)) : ℝ) = normalized_y := by
    norm_num [normalized_y]
  rw [hratio] at h
  norm_num [Finset.sum_range_succ] at h
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1, hh.2]

theorem log_y_bounds :
    (-1705817 / 1000000 : ℝ) ≤ Real.log y ∧ Real.log y ≤ (-8529083 / 5000000 : ℝ) := by
  have hu := log_normalized_y_bounds
  have htwo := log_two_bounds
  have heq : y = normalized_y / (2 : ℝ) ^ 3 := by norm_num [y, normalized_y]
  rw [heq, Real.log_div (by norm_num [normalized_y]) (by norm_num),
    Real.log_pow]
  norm_num
  constructor <;> linarith [hu.1, hu.2, htwo.1, htwo.2]

private theorem log_bankArg_bounds :
    (24303 / 125000 : ℝ) ≤ Real.log bankArg ∧ Real.log bankArg ≤ (1944241 / 10000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |((85844483685441 / 885844483685441 : ℝ) : ℝ)| < 1) 8
  have hratio : ((1 + (85844483685441 / 885844483685441 : ℝ)) / (1 - (85844483685441 / 885844483685441 : ℝ)) : ℝ) = bankArg := by
    norm_num [bankArg]
  rw [hratio] at h
  norm_num [Finset.sum_range_succ] at h
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1, hh.2]

private def normalized_z : ℝ := (7523953 / 6250000 : ℝ)

private theorem log_normalized_z_bounds :
    (927551 / 5000000 : ℝ) ≤ Real.log normalized_z ∧ Real.log normalized_z ≤ (1855103 / 10000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |((1273953 / 13773953 : ℝ) : ℝ)| < 1) 8
  have hratio : ((1 + (1273953 / 13773953 : ℝ)) / (1 - (1273953 / 13773953 : ℝ)) : ℝ) = normalized_z := by
    norm_num [normalized_z]
  rw [hratio] at h
  norm_num [Finset.sum_range_succ] at h
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1, hh.2]

theorem log_z_bounds :
    (-12935393 / 5000000 : ℝ) ≤ Real.log z ∧ Real.log z ≤ (-25870781 / 10000000 : ℝ) := by
  have hu := log_normalized_z_bounds
  have htwo := log_two_bounds
  have heq : z = normalized_z / (2 : ℝ) ^ 4 := by norm_num [z, normalized_z]
  rw [heq, Real.log_div (by norm_num [normalized_z]) (by norm_num),
    Real.log_pow]
  norm_num
  constructor <;> linarith [hu.1, hu.2, htwo.1, htwo.2]

private theorem log_queryArg1_bounds :
    (362717 / 5000000 : ℝ) ≤ Real.log queryArg1 ∧ Real.log queryArg1 ≤ (145087 / 2000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |((7523953 / 207523953 : ℝ) : ℝ)| < 1) 8
  have hratio : ((1 + (7523953 / 207523953 : ℝ)) / (1 - (7523953 / 207523953 : ℝ)) : ℝ) = queryArg1 := by
    norm_num [queryArg1]
  rw [hratio] at h
  norm_num [Finset.sum_range_succ] at h
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1, hh.2]

private theorem log_queryArg2_bounds :
    (155589 / 2000000 : ℝ) ≤ Real.log queryArg2 ∧ Real.log queryArg2 ≤ (388973 / 5000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |((809005168746209 / 20809005168746209 : ℝ) : ℝ)| < 1) 8
  have hratio : ((1 + (809005168746209 / 20809005168746209 : ℝ)) / (1 - (809005168746209 / 20809005168746209 : ℝ)) : ℝ) = queryArg2 := by
    norm_num [queryArg2]
  rw [hratio] at h
  norm_num [Finset.sum_range_succ] at h
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1, hh.2]

theorem Hpi_bounds : (407317 / 500000 : ℝ) ≤ Hpi ∧ Hpi ≤ (814637 / 1000000 : ℝ) := by
  have h_pi0 := log_pi0_bounds
  have h_pi1 := log_pi1_bounds
  have h_pi2 := log_pi2_bounds
  have h_two := log_two_bounds
  constructor
  · unfold Hpi
    apply (le_div_iff₀ log_two_pos).2
    norm_num [Hpi, mean, deficit, pi0, pi1, pi2, alpha0, alpha1, alpha2] at *
    linarith [h_pi0.1, h_pi0.2, h_pi1.1, h_pi1.2, h_pi2.1, h_pi2.2, h_two.1, h_two.2]
  · unfold Hpi
    apply (div_le_iff₀ log_two_pos).2
    norm_num [Hpi, mean, deficit, pi0, pi1, pi2, alpha0, alpha1, alpha2] at *
    linarith [h_pi0.1, h_pi0.2, h_pi1.1, h_pi1.2, h_pi2.1, h_pi2.2, h_two.1, h_two.2]

theorem Halpha_bounds : (127857 / 250000 : ℝ) ≤ Halpha ∧ Halpha ≤ (63929 / 125000 : ℝ) := by
  have h_alpha0 := log_alpha0_bounds
  have h_alpha1 := log_alpha1_bounds
  have h_alpha2 := log_alpha2_bounds
  have h_two := log_two_bounds
  constructor
  · unfold Halpha
    apply (le_div_iff₀ log_two_pos).2
    norm_num [Halpha, mean, deficit, pi0, pi1, pi2, alpha0, alpha1, alpha2] at *
    linarith [h_alpha0.1, h_alpha0.2, h_alpha1.1, h_alpha1.2, h_alpha2.1, h_alpha2.2, h_two.1, h_two.2]
  · unfold Halpha
    apply (div_le_iff₀ log_two_pos).2
    norm_num [Halpha, mean, deficit, pi0, pi1, pi2, alpha0, alpha1, alpha2] at *
    linarith [h_alpha0.1, h_alpha0.2, h_alpha1.1, h_alpha1.2, h_alpha2.1, h_alpha2.2, h_two.1, h_two.2]

theorem partitionEntropy_bounds : (205117 / 1000000 : ℝ) ≤ partitionEntropy ∧ partitionEntropy ≤ (641 / 3125 : ℝ) := by
  have h_three := log_three_bounds
  have h_two := log_two_bounds
  constructor
  · unfold partitionEntropy
    apply (le_div_iff₀ log_two_pos).2
    norm_num [partitionEntropy, mean, deficit, pi0, pi1, pi2, alpha0, alpha1, alpha2] at *
    linarith [h_three.1, h_three.2, h_two.1, h_two.2]
  · unfold partitionEntropy
    apply (div_le_iff₀ log_two_pos).2
    norm_num [partitionEntropy, mean, deficit, pi0, pi1, pi2, alpha0, alpha1, alpha2] at *
    linarith [h_three.1, h_three.2, h_two.1, h_two.2]

theorem bankEntropy_bounds : (782163 / 1000000 : ℝ) ≤ bankEntropy ∧ bankEntropy ≤ (391083 / 500000 : ℝ) := by
  have h_bankArg := log_bankArg_bounds
  have h_y := log_y_bounds
  have h_two := log_two_bounds
  constructor
  · unfold bankEntropy
    apply (le_div_iff₀ log_two_pos).2
    norm_num [bankEntropy, mean, deficit, pi0, pi1, pi2, alpha0, alpha1, alpha2] at *
    linarith [h_bankArg.1, h_bankArg.2, h_y.1, h_y.2, h_two.1, h_two.2]
  · unfold bankEntropy
    apply (div_le_iff₀ log_two_pos).2
    norm_num [bankEntropy, mean, deficit, pi0, pi1, pi2, alpha0, alpha1, alpha2] at *
    linarith [h_bankArg.1, h_bankArg.2, h_y.1, h_y.2, h_two.1, h_two.2]

theorem queryEntropy_bounds : (35043 / 500000 : ℝ) ≤ queryEntropy ∧ queryEntropy ≤ (70089 / 1000000 : ℝ) := by
  have h_queryArg1 := log_queryArg1_bounds
  have h_queryArg2 := log_queryArg2_bounds
  have h_z := log_z_bounds
  have h_two := log_two_bounds
  constructor
  · unfold queryEntropy
    apply (le_div_iff₀ log_two_pos).2
    norm_num [queryEntropy, mean, deficit, pi0, pi1, pi2, alpha0, alpha1, alpha2] at *
    linarith [h_queryArg1.1, h_queryArg1.2, h_queryArg2.1, h_queryArg2.2, h_z.1, h_z.2, h_two.1, h_two.2]
  · unfold queryEntropy
    apply (div_le_iff₀ log_two_pos).2
    norm_num [queryEntropy, mean, deficit, pi0, pi1, pi2, alpha0, alpha1, alpha2] at *
    linarith [h_queryArg1.1, h_queryArg1.2, h_queryArg2.1, h_queryArg2.2, h_z.1, h_z.2, h_two.1, h_two.2]

theorem pi_total : pi0 + pi1 + pi2 = 1 := by norm_num [pi0, pi1, pi2]
theorem pi_positive : 0 < pi0 ∧ 0 < pi1 ∧ 0 < pi2 := by norm_num [pi0, pi1, pi2]
theorem alpha_positive : 0 < alpha0 ∧ 0 < alpha1 ∧ 0 < alpha2 := by
  norm_num [alpha0, alpha1, alpha2]
theorem alpha_ordered : alpha2 ≤ alpha1 ∧ alpha1 ≤ alpha0 := by
  norm_num [alpha0, alpha1, alpha2]
theorem alpha_total : alpha0 + alpha1 + alpha2 = 1 := by
  norm_num [alpha0, alpha1, alpha2]
theorem alpha_formulas :
    alpha0 = pi0 + pi1 / 2 + pi2 / 3 ∧
    alpha1 = pi1 / 2 + pi2 / 3 ∧ alpha2 = pi2 / 3 := by
  norm_num [alpha0, alpha1, alpha2, pi0, pi1, pi2]
theorem deficit_room : mean / 2 - deficit = (9520077 / 100000000 : ℝ) := by
  norm_num [mean, pi1, pi2, deficit]
theorem deficit_positive : 0 < deficit := by norm_num [deficit]
theorem endpoint_below_cut : mean / 2 < mean - deficit := by
  have h := deficit_room
  linarith
theorem generating_polynomials :
    bankArg = 1 + y + y ^ 2 ∧ queryArg1 = 1 + z ∧ queryArg2 = 1 + z + z ^ 2 := by
  norm_num [bankArg, queryArg1, queryArg2, y, z]
theorem gibbs_parameters : 0 < y ∧ y < 1 ∧ 0 < z ∧ z < 1 := by norm_num [y, z]
theorem Hpi_pos : 0 < Hpi := by linarith [Hpi_bounds.1]

/-- The exceptional mixed-projection binomial fiber has a strict quarter-bit margin. -/
theorem projection_fiber_entropy_bound :
    Real.binEntropy alpha2 / Real.log 2 < (1 / 4 : ℝ) := by
  have hm := Real.binEntropy_strictMonoOn
    (by norm_num [alpha2] : alpha2 ∈ Set.Icc (0 : ℝ) 2⁻¹)
    (by norm_num [Parameters.initialTheta] :
      Parameters.initialTheta ∈ Set.Icc (0 : ℝ) 2⁻¹)
    (by norm_num [alpha2, Parameters.initialTheta] :
      alpha2 < Parameters.initialTheta)
  have hd := div_lt_div_of_pos_right hm log_two_pos
  have hb := Parameters.initial_entropy_bound
  unfold Parameters.entropy at hb
  exact hd.trans hb

/-- A `choose(L, alpha2*L)` fiber is strictly smaller than a half-Hpi layer. -/
theorem projection_fiber_entropy_lt_half_Hpi :
    Real.binEntropy alpha2 / Real.log 2 < Hpi / 2 := by
  linarith [projection_fiber_entropy_bound, Hpi_bounds.1]

/-- Exact finite bound on the mixed projection fiber in the integer schedule. -/
theorem projection_fiber_log_choose_bound {m : ℕ} (hm : 0 < m) :
    Real.log (((100000000 * m).choose (978249 * m) : ℕ) : ℝ) <
      (100000000 * m : ℕ) * Real.log 2 / 4 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hL : (0 : ℝ) < (100000000 * m : ℕ) := by
    exact_mod_cast (Nat.mul_pos (by decide : 0 < 100000000) hm)
  have hk : 978249 * m ≤ 100000000 * m :=
    Nat.mul_le_mul_right m (by decide : 978249 ≤ 100000000)
  have hr : ((978249 * m : ℕ) : ℝ) / (100000000 * m : ℕ) = alpha2 := by
    push_cast
    unfold alpha2
    field_simp
  have hb := (BinomialEntropy.log_choose_entropy_bounds hk).2
  rw [hr] at hb
  have he := (div_lt_iff₀ log_two_pos).mp projection_fiber_entropy_bound
  calc
    Real.log (((100000000 * m).choose (978249 * m) : ℕ) : ℝ)
      ≤ (100000000 * m : ℕ) * Real.binEntropy alpha2 := hb
    _ < (100000000 * m : ℕ) * ((1 / 4 : ℝ) * Real.log 2) :=
      mul_lt_mul_of_pos_left he hL
    _ = (100000000 * m : ℕ) * Real.log 2 / 4 := by ring

theorem projection_fiber_bits_lt_quarter {m : ℕ} (hm : 0 < m) :
    Real.log (((100000000 * m).choose (978249 * m) : ℕ) : ℝ) /
      ((100000000 * m : ℕ) * Real.log 2) < (1 / 4 : ℝ) := by
  have hL : (0 : ℝ) < (100000000 * m : ℕ) := by
    exact_mod_cast (Nat.mul_pos (by decide : 0 < 100000000) hm)
  apply (div_lt_iff₀ (mul_pos hL log_two_pos)).mpr
  calc
    Real.log (((100000000 * m).choose (978249 * m) : ℕ) : ℝ)
      < (100000000 * m : ℕ) * Real.log 2 / 4 := projection_fiber_log_choose_bound hm
    _ = (1 / 4 : ℝ) * ((100000000 * m : ℕ) * Real.log 2) := by ring

theorem projection_fiber_bits_lt_half_Hpi {m : ℕ} (hm : 0 < m) :
    Real.log (((100000000 * m).choose (978249 * m) : ℕ) : ℝ) /
      ((100000000 * m : ℕ) * Real.log 2) < Hpi / 2 := by
  linarith [projection_fiber_bits_lt_quarter hm, Hpi_bounds.1]

theorem analytic_admissibility :
    0 < bankEntropy ∧ 0 < queryEntropy ∧ partitionEntropy < Hpi ∧
    Halpha < bankEntropy ∧ (Hpi + partitionEntropy) / 2 < Halpha ∧
    0 < Hpi - partitionEntropy + 2 * queryEntropy := by
  obtain ⟨hH0, hH1⟩ := Hpi_bounds
  obtain ⟨hA0, hA1⟩ := Halpha_bounds
  obtain ⟨hG0, hG1⟩ := partitionEntropy_bounds
  obtain ⟨hB0, hB1⟩ := bankEntropy_bounds
  obtain ⟨hQ0, hQ1⟩ := queryEntropy_bounds
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

def costLedger : List ℝ :=
  [2 * bankEntropy / Hpi,
   2 - partitionEntropy / Hpi + 2 * queryEntropy / Hpi,
   2 * Halpha / Hpi,
   1 + partitionEntropy / Hpi,
   2 - partitionEntropy / Hpi,
   1]

theorem ledger_individual_bounds :
    2 * bankEntropy / Hpi < certificateExponent ∧
    2 - partitionEntropy / Hpi + 2 * queryEntropy / Hpi < certificateExponent ∧
    2 * Halpha / Hpi < certificateExponent ∧
    1 + partitionEntropy / Hpi < certificateExponent ∧
    2 - partitionEntropy / Hpi < certificateExponent := by
  obtain ⟨hH0, hH1⟩ := Hpi_bounds
  obtain ⟨hA0, hA1⟩ := Halpha_bounds
  obtain ⟨hG0, hG1⟩ := partitionEntropy_bounds
  obtain ⟨hB0, hB1⟩ := bankEntropy_bounds
  obtain ⟨hQ0, hQ1⟩ := queryEntropy_bounds
  have hn : Hpi ≠ 0 := ne_of_gt Hpi_pos
  have hquery : 2 - partitionEntropy / Hpi + 2 * queryEntropy / Hpi =
      (2 * Hpi - partitionEntropy + 2 * queryEntropy) / Hpi := by
    field_simp [hn]
  have hhist : 1 + partitionEntropy / Hpi = (Hpi + partitionEntropy) / Hpi := by
    field_simp [hn]
  have hinc : 2 - partitionEntropy / Hpi = (2 * Hpi - partitionEntropy) / Hpi := by
    field_simp [hn]
  rw [hquery, hhist, hinc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    apply (div_lt_iff₀ Hpi_pos).2 <;>
    norm_num [certificateExponent] at * <;> linarith

theorem all_costs_lt_certificate : ∀ t ∈ costLedger, t < certificateExponent := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ledger_individual_bounds
  intro t ht
  simp only [costLedger, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · norm_num [certificateExponent]

theorem certificate_margin : targetExponent - certificateExponent = (7 / 10000 : ℝ) := by
  norm_num [targetExponent, certificateExponent]
theorem certificate_lt_target : certificateExponent < targetExponent := by
  norm_num [targetExponent, certificateExponent]
theorem all_costs_lt_target : ∀ t ∈ costLedger, t < targetExponent := by
  intro t ht
  exact lt_trans (all_costs_lt_certificate t ht) certificate_lt_target

end ThreeSum.TernaryParameters
