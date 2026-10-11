import Submission.ThreeSum.TrimScales

/-!
# The executable band size and its exact exponent

The band numerator is the integer ceiling of the square root of the actual
typed output count. The denominator is `2^(mu/20)`. Since the block schedule
has `20 ∣ mu`, the denominator exponent has no divisibility error.
-/

namespace ThreeSum.BandScales

open Filter Real ThreeSum.Scales
open scoped Topology

def bandRoot (n : ℕ) : ℕ := LocalCoverBounds.rootCeiling (typedOutputs n)

def bandDivisor (n : ℕ) : ℕ := 2 ^ (mu n / 20)

def bandSize (n : ℕ) : ℕ := bandRoot n ⌈/⌉ bandDivisor n

theorem mu_multiple_twenty (n : ℕ) : 20 ∣ mu n := by
  unfold mu totalSize blockCount
  exact ⟨(inputBits n / (100 * microSize (inputBits n))) * microSize (inputBits n), by ring⟩

theorem typedOutputs_pos (n : ℕ) : 0 < typedOutputs n := by
  unfold typedOutputs
  exact Nat.pow_pos (Nat.choose_pos (by omega))

theorem bandRoot_pos (n : ℕ) : 0 < bandRoot n := LocalCoverBounds.rootCeiling_pos _

theorem bandDivisor_pos (n : ℕ) : 0 < bandDivisor n := by
  unfold bandDivisor
  positivity

theorem bandSize_mul_bounds (n : ℕ) :
    bandRoot n ≤ bandDivisor n * bandSize n ∧
      bandDivisor n * bandSize n < bandRoot n + bandDivisor n := by
  constructor
  · exact (ceilDiv_le_iff_le_mul (a := bandDivisor n) (b := bandRoot n)
      (c := bandSize n) (bandDivisor_pos n)).mp le_rfl
  · have h := Nat.div_mul_le_self (bandRoot n + bandDivisor n - 1) (bandDivisor n)
    simp only [bandSize, Nat.ceilDiv_eq_add_pred_div]
    rw [Nat.mul_comm (bandDivisor n)]
    have hpos := bandDivisor_pos n
    omega

theorem bandSize_pos (n : ℕ) : 0 < bandSize n := by
  have hl := (bandSize_mul_bounds n).1
  have hp := bandRoot_pos n
  by_contra h
  have hb : bandSize n = 0 := by omega
  rw [hb, Nat.mul_zero] at hl
  omega

noncomputable section

def unroundedBand (n : ℕ) : ℝ := (bandRoot n : ℝ) / bandDivisor n

theorem bandRoot_log_interval (n : ℕ) :
    Real.log (typedOutputs n : ℝ) ≤ 2 * Real.log (bandRoot n : ℝ) ∧
      2 * Real.log (bandRoot n : ℝ) ≤ Real.log 4 + Real.log (typedOutputs n : ℝ) := by
  have hM : (0 : ℝ) < typedOutputs n := by exact_mod_cast typedOutputs_pos n
  have hr : (0 : ℝ) < bandRoot n := by exact_mod_cast bandRoot_pos n
  have hlo : (typedOutputs n : ℝ) ≤ (bandRoot n : ℝ) ^ 2 := by
    exact_mod_cast LocalCoverBounds.le_rootCeiling_sq (typedOutputs n)
  have hup : (bandRoot n : ℝ) ^ 2 ≤ 4 * (typedOutputs n : ℝ) := by
    exact_mod_cast LocalCoverBounds.rootCeiling_sq_le_four (typedOutputs_pos n)
  constructor
  · simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hM hlo
  · simpa only [Real.log_pow, Nat.cast_ofNat,
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hM.ne'] using
      Real.log_le_log (by positivity : (0 : ℝ) < (bandRoot n : ℝ) ^ 2) hup

theorem bandRoot_log_rate :
    Tendsto (fun n : ℕ => Real.log (bandRoot n : ℝ) / Real.log n) atTop
      (𝓝 (Parameters.E / 5)) := by
  have hl := typedOutputs_log_ratio_tendsto.div_const 2
  have heq : 2 * Parameters.E / 5 / 2 = Parameters.E / 5 := by ring
  rw [heq] at hl
  have herr := Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul (Real.log 4 / 2)
  have hu := hl.add herr
  simp only [mul_zero, add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hp : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hb := (bandRoot_log_interval n).1
    apply (le_div_iff₀ hp).mpr
    have he : (Real.log (typedOutputs n : ℝ) / Real.log n / 2) * Real.log n =
        Real.log (typedOutputs n : ℝ) / 2 := by field_simp
    rw [he]
    linarith
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hp : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hb := (bandRoot_log_interval n).2
    apply (div_le_iff₀ hp).mpr
    simp only [Pi.inv_apply]
    have he : (Real.log (typedOutputs n : ℝ) / Real.log n / 2 +
        (Real.log 4 / 2) * (Real.log n)⁻¹) * Real.log n =
        (Real.log (typedOutputs n : ℝ) + Real.log 4) / 2 := by field_simp
    rw [he]
    linarith

theorem mu_div_twenty_real (n : ℕ) : (mu n / 20 : ℕ) = (mu n : ℝ) / 20 := by
  have h := Nat.div_mul_cancel (mu_multiple_twenty n)
  have hr : ((mu n / 20 : ℕ) : ℝ) * 20 = mu n := by exact_mod_cast h
  linarith

theorem bandDivisor_log_rate :
    Tendsto (fun n : ℕ => Real.log (bandDivisor n : ℝ) / Real.log n) atTop (𝓝 (1 / 100)) := by
  have h := mu_log_ratio_tendsto.const_mul (Real.log 2 / 20)
  have heq : (Real.log 2 / 20) * (1 / (5 * Real.log 2)) = (1 / 100 : ℝ) := by field_simp; norm_num
  rw [heq] at h
  convert h using 1
  funext n
  simp only [bandDivisor, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, mu_div_twenty_real]
  ring

theorem unroundedBand_pos (n : ℕ) : 0 < unroundedBand n := by
  have hR : (0 : ℝ) < bandRoot n := by exact_mod_cast bandRoot_pos n
  have hD : (0 : ℝ) < bandDivisor n := by exact_mod_cast bandDivisor_pos n
  exact div_pos hR hD

theorem unroundedBand_log_rate :
    Tendsto (fun n : ℕ => Real.log (unroundedBand n) / Real.log n) atTop
      (𝓝 ((Parameters.E - 1 / 20) / 5)) := by
  have h := bandRoot_log_rate.sub bandDivisor_log_rate
  have heq : Parameters.E / 5 - 1 / 100 = (Parameters.E - 1 / 20) / 5 := by ring
  rw [heq] at h
  apply h.congr'
  filter_upwards [] with n
  have hR : (0 : ℝ) < bandRoot n := by exact_mod_cast bandRoot_pos n
  have hD : (0 : ℝ) < bandDivisor n := by exact_mod_cast bandDivisor_pos n
  rw [unroundedBand, Real.log_div hR.ne' hD.ne', sub_div]

theorem unroundedBand_eventually_ge_one : ∀ᶠ n : ℕ in atTop, 1 ≤ unroundedBand n := by
  have hpos : (0 : ℝ) < (Parameters.E - 1 / 20) / 5 := by have := Parameters.E_bounds.1; linarith
  have hs := unroundedBand_log_rate.eventually (lt_mem_nhds hpos)
  filter_upwards [hs, eventually_ge_atTop (2 : ℕ)] with n hn hge
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hb : 0 < Real.log (unroundedBand n) := (div_pos_iff.mp hn).elim
    (fun h => h.1) (fun h => False.elim (not_lt_of_ge hlog.le h.2))
  exact ((Real.log_pos_iff (unroundedBand_pos n).le).mp hb).le

theorem bandSize_ge_unrounded (n : ℕ) : unroundedBand n ≤ (bandSize n : ℝ) := by
  have hD : (0 : ℝ) < bandDivisor n := by exact_mod_cast bandDivisor_pos n
  have hl : (bandRoot n : ℝ) ≤ (bandDivisor n : ℝ) * bandSize n := by
    exact_mod_cast (bandSize_mul_bounds n).1
  rw [unroundedBand, div_le_iff₀ hD]
  simpa only [mul_comm] using hl

theorem bandSize_eventually_le_twice_unrounded :
    ∀ᶠ n : ℕ in atTop, (bandSize n : ℝ) ≤ 2 * unroundedBand n := by
  filter_upwards [unroundedBand_eventually_ge_one] with n hn
  have hD : (0 : ℝ) < bandDivisor n := by exact_mod_cast bandDivisor_pos n
  have hu : (bandDivisor n : ℝ) * bandSize n < bandRoot n + bandDivisor n := by
    exact_mod_cast (bandSize_mul_bounds n).2
  have hb : (bandSize n : ℝ) < unroundedBand n + 1 := by
    rw [unroundedBand]
    have heq : ((bandRoot n : ℝ) + bandDivisor n) / bandDivisor n =
        (bandRoot n : ℝ) / bandDivisor n + 1 := by field_simp
    rw [← heq]
    apply (lt_div_iff₀ hD).mpr
    simpa only [mul_comm] using hu
  linarith

theorem bandSize_log_rate :
    Tendsto (fun n : ℕ => Real.log (bandSize n : ℝ) / Real.log n) atTop
      (𝓝 ((Parameters.E - 1 / 20) / 5)) := by
  have herr := Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul (Real.log 2)
  have hu := unroundedBand_log_rate.add herr
  simp only [mul_zero, add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' unroundedBand_log_rate hu
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (unroundedBand_pos n) (bandSize_ge_unrounded n))
      (Real.log_nonneg (by exact_mod_cast hn))
  · filter_upwards [bandSize_eventually_le_twice_unrounded, eventually_ge_atTop (1 : ℕ)] with n hn hge
    have hpos : (0 : ℝ) < bandSize n := by exact_mod_cast bandSize_pos n
    have hlog := Real.log_le_log hpos hn
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (unroundedBand_pos n).ne'] at hlog
    have hd := div_le_div_of_nonneg_right hlog
      (show 0 ≤ Real.log (n : ℝ) from Real.log_nonneg (by exact_mod_cast hge))
    simpa only [add_div, Pi.inv_apply, div_eq_mul_inv, add_mul, add_comm] using hd

end

end ThreeSum.BandScales
