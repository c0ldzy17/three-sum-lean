import Submission.ThreeSum.Switch
import Mathlib.Tactic.LinearCombination

/-!
# Actual finite hierarchy counts

These are the binomial counts used by the concrete microblock hierarchy.
Every prefix partition is included.  The integer switch and its rounding
allowance are applied before any asymptotic estimate is made.  The counts
in this module are combinatorial work counts; the implementation's operation
counts, raw wanted incidences, and false-mass bounds are separate interfaces.
-/

namespace ThreeSum.CostLedger

open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch
open scoped Topology BigOperators

set_option maxHeartbeats 400000

def bandCount (n : ℕ) : ℕ := n ⌈/⌉ BandScales.bandSize n

def microOutputs (n : ℕ) : ℕ := (256 * muZero n).choose (muZero n)

def microPartitions (n : ℕ) : ℕ := (muZero n).choose (muZero n / 2)

def prefixChoices (n j : ℕ) : ℕ := (microOutputs n * microPartitions n) ^ j

def suffixBoxes (n j : ℕ) : ℕ :=
  (256 * residualSize n j).choose (residualSize n j - actualSwitch n j)

def prefixBoxes (n j : ℕ) : ℕ := prefixChoices n j * suffixBoxes n j

def queryTerms (n j : ℕ) : ℕ := (residualSize n j).choose (actualSwitch n j)

def allPrefixBoxes (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (terminalDepth n + 1), prefixBoxes n j

def allQueryTerms (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (terminalDepth n + 1), queryTerms n j

theorem bandCount_mul_bounds (n : ℕ) :
    n ≤ BandScales.bandSize n * bandCount n ∧
      BandScales.bandSize n * bandCount n < n + BandScales.bandSize n := by
  constructor
  · exact (ceilDiv_le_iff_le_mul (a := BandScales.bandSize n) (b := n)
      (c := bandCount n) (BandScales.bandSize_pos n)).mp le_rfl
  · have h := Nat.div_mul_le_self (n + BandScales.bandSize n - 1) (BandScales.bandSize n)
    simp only [bandCount, Nat.ceilDiv_eq_add_pred_div]
    rw [Nat.mul_comm (BandScales.bandSize n)]
    have hpos := BandScales.bandSize_pos n
    omega

theorem microOutputs_pos (n : ℕ) : 0 < microOutputs n :=
  Nat.choose_pos (by omega)

theorem microPartitions_pos (n : ℕ) : 0 < microPartitions n :=
  Nat.choose_pos (Nat.div_le_self _ _)

theorem prefixChoices_pos (n j : ℕ) : 0 < prefixChoices n j :=
  Nat.pow_pos (Nat.mul_pos (microOutputs_pos n) (microPartitions_pos n))

theorem suffixBoxes_pos (n j : ℕ) : 0 < suffixBoxes n j :=
  Nat.choose_pos (by omega)

theorem prefixBoxes_pos (n j : ℕ) : 0 < prefixBoxes n j :=
  Nat.mul_pos (prefixChoices_pos n j) (suffixBoxes_pos n j)

noncomputable section

theorem microOutputs_log_bound {n : ℕ} (hmu : 0 < mu n) :
    Real.log (microOutputs n : ℝ) ≤ 2 * E * muZero n * Real.log 2 := by
  have hprod := hmu
  rw [actual_totalSize] at hprod
  have hm := Nat.pos_of_mul_pos_left hprod
  have hmR : (0 : ℝ) < muZero n := by exact_mod_cast hm
  have hb := (BinomialEntropy.fixed_ratio_bounds (c := 256) (r := 1)
    (by norm_num) (by norm_num) hm).2
  simp only [Nat.one_mul, Nat.cast_ofNat, Nat.cast_one] at hb
  have hc := (div_le_iff₀ hmR).mp hb
  change Real.log (((256 * muZero n).choose (muZero n) : ℕ) : ℝ) ≤ _
  have hid : 2 * E * (muZero n : ℝ) * Real.log 2 =
      256 * Real.binEntropy (1 / 256) * muZero n := by
    unfold E entropy
    field_simp
    <;> ring
  rw [hid]
  exact hc

theorem microPartitions_log_bound (n : ℕ) :
    Real.log (microPartitions n : ℝ) ≤ (muZero n : ℝ) * Real.log 2 := by
  have hp : (0 : ℝ) < microPartitions n := by exact_mod_cast microPartitions_pos n
  have hb : (microPartitions n : ℝ) ≤ (2 : ℝ) ^ muZero n := by
    exact_mod_cast Nat.choose_le_two_pow (muZero n) (muZero n / 2)
  simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hp hb

theorem prefixChoices_log_bound {n j : ℕ} (hmu : 0 < mu n) :
    Real.log (prefixChoices n j : ℝ) ≤
      (j : ℝ) * muZero n * Real.log 2 * (2 * E + 1) := by
  have hM : (microOutputs n : ℝ) ≠ 0 := by exact_mod_cast (microOutputs_pos n).ne'
  have hG : (microPartitions n : ℝ) ≠ 0 := by exact_mod_cast (microPartitions_pos n).ne'
  simp only [prefixChoices, Nat.cast_pow, Nat.cast_mul, Real.log_pow, Real.log_mul hM hG]
  have hsum := add_le_add (microOutputs_log_bound hmu) (microPartitions_log_bound n)
  have hmul := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (α := ℝ) j)
  nlinarith

theorem suffixBoxes_log_bound {n j : ℕ} (hmu : 0 < mu n)
    (hj : j ≤ terminalDepth n) :
    Real.log (suffixBoxes n j : ℝ) ≤
      (residualSize n j : ℝ) * Real.log 2 *
        (2 * E - gamma ((actualSwitch n j : ℝ) / residualSize n j)) := by
  have hr := actual_residual_pos hmu hj
  have hrR : (0 : ℝ) < residualSize n j := by exact_mod_cast hr
  have hprod := hmu
  rw [actual_totalSize] at hprod
  have hspec := switchIndex_spec (Nat.pos_of_mul_pos_right hprod)
    (actual_depth_condition hj) hr (actual_residual_even n j)
  have hq : actualSwitch n j ≤ residualSize n j := by
    unfold actualSwitch
    exact hspec.1.trans (Nat.div_le_self _ _)
  have hb := (BinomialEntropy.log_choose_entropy_bounds
    (show residualSize n j - actualSwitch n j ≤ 256 * residualSize n j by omega)).2
  have hratio : ((residualSize n j - actualSwitch n j : ℕ) : ℝ) /
      ((256 * residualSize n j : ℕ) : ℝ) =
        (1 - (actualSwitch n j : ℝ) / residualSize n j) / 256 := by
    rw [Nat.cast_sub hq, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
    <;> ring
  rw [hratio, Nat.cast_mul, Nat.cast_ofNat] at hb
  have hid : (residualSize n j : ℝ) * Real.log 2 *
      (2 * E - gamma ((actualSwitch n j : ℝ) / residualSize n j)) =
        256 * (residualSize n j : ℝ) *
          Real.binEntropy ((1 - (actualSwitch n j : ℝ) / residualSize n j) / 256) := by
    unfold E gamma entropy
    field_simp
    <;> ring
  rw [hid]
  exact hb

theorem prefixBoxes_log_bound {n j : ℕ} (hmu : 0 < mu n)
    (hj : j ≤ terminalDepth n) :
    Real.log (prefixBoxes n j : ℝ) ≤
      (mu n : ℝ) * Real.log 2 * (2 * E + 2 * bandShift - boxSaving) := by
  have hp : (prefixChoices n j : ℝ) ≠ 0 := by exact_mod_cast (prefixChoices_pos n j).ne'
  have hs : (suffixBoxes n j : ℝ) ≠ 0 := by exact_mod_cast (suffixBoxes_pos n j).ne'
  have hb := add_le_add (prefixChoices_log_bound (j := j) hmu) (suffixBoxes_log_bound hmu hj)
  have hc := (actual_switch_certified hmu hj).2.1
  have hn : (0 : ℝ) ≤ (mu n : ℝ) * Real.log 2 :=
    mul_nonneg (Nat.cast_nonneg _) log_two_pos.le
  have hmul := mul_le_mul_of_nonneg_left hc hn
  have hid := residual_real_identity hmu hj
  have hprod : (mu n : ℝ) = (blockCount (inputBits n) : ℝ) * muZero n := by
    exact_mod_cast actual_totalSize n
  have hpos := hmu
  rw [actual_totalSize] at hpos
  have hJ : (blockCount (inputBits n) : ℝ) ≠ 0 :=
    by exact_mod_cast (Nat.pos_of_mul_pos_right hpos).ne'
  have hjid : (j : ℝ) * muZero n =
      ((j : ℝ) / blockCount (inputBits n)) * mu n := by rw [hprod]; field_simp
  have hcombine : (j : ℝ) * muZero n * Real.log 2 * (2 * E + 1) +
      (residualSize n j : ℝ) * Real.log 2 *
        (2 * E - gamma ((actualSwitch n j : ℝ) / residualSize n j)) =
      (mu n : ℝ) * Real.log 2 *
        (2 * E + (j : ℝ) / blockCount (inputBits n) -
          (1 - (j : ℝ) / blockCount (inputBits n)) *
            gamma ((actualSwitch n j : ℝ) / residualSize n j)) := by
    rw [hjid, hid]
    ring
  rw [hcombine] at hb
  simp only [prefixBoxes, Nat.cast_mul, Real.log_mul hp hs]
  linear_combination hb + hmul

theorem queryTerms_pos {n j : ℕ} (hmu : 0 < mu n)
    (hj : j ≤ terminalDepth n) : 0 < queryTerms n j := by
  have hprod := hmu
  rw [actual_totalSize] at hprod
  have hq := (switchIndex_spec (Nat.pos_of_mul_pos_right hprod)
    (actual_depth_condition hj) (actual_residual_pos hmu hj) (actual_residual_even n j)).1
  exact Nat.choose_pos (hq.trans (Nat.div_le_self _ _))

theorem queryTerms_log_bound {n j : ℕ} (hmu : 0 < mu n)
    (hj : j ≤ terminalDepth n) :
    Real.log (queryTerms n j : ℝ) ≤
      (mu n : ℝ) * Real.log 2 * (entropyRatio * (1 + boxSaving - 2 * bandShift)) +
        9 * entropyRatio * Real.log 2 := by
  have hprod := hmu
  rw [actual_totalSize] at hprod
  have hr := actual_residual_pos hmu hj
  have hq := (switchIndex_spec (Nat.pos_of_mul_pos_right hprod)
    (actual_depth_condition hj) hr (actual_residual_even n j)).1
  have hb := (BinomialEntropy.log_choose_entropy_bounds
    (hq.trans (Nat.div_le_self _ _))).2
  have hc := (actual_switch_certified hmu hj).2.2
  have hmuR : (0 : ℝ) < mu n := by exact_mod_cast hmu
  have hmul := mul_lt_mul_of_pos_left hc (mul_pos hmuR log_two_pos)
  have hid : (residualSize n j : ℝ) *
      Real.binEntropy ((actualSwitch n j : ℝ) / residualSize n j) =
      (mu n : ℝ) * Real.log 2 *
        ((1 - (j : ℝ) / blockCount (inputBits n)) *
          entropy ((actualSwitch n j : ℝ) / residualSize n j)) := by
    rw [residual_real_identity hmu hj]
    unfold entropy
    field_simp
    <;> ring
  change Real.log (queryTerms n j : ℝ) ≤
    (residualSize n j : ℝ) * Real.binEntropy ((actualSwitch n j : ℝ) / residualSize n j) at hb
  rw [hid] at hb
  have hround : (mu n : ℝ) * Real.log 2 *
      (entropyRatio * (1 + boxSaving - 2 * bandShift) + 9 * entropyRatio / mu n) =
      (mu n : ℝ) * Real.log 2 * (entropyRatio * (1 + boxSaving - 2 * bandShift)) +
        9 * entropyRatio * Real.log 2 := by field_simp
  rw [hround] at hmul
  exact hb.trans hmul.le

end
end ThreeSum.CostLedger
