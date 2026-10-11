import Submission.ThreeSum.Parameters
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Monotone.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A finite entropy certificate for every binomial coefficient

The proof uses the mode of the exact binomial expansion with integral weights `k`
and `n-k`. It does not invoke Stirling's formula or introduce an asymptotic assumption.
-/

noncomputable section

namespace ThreeSum.BinomialEntropy

open Finset Real Set Filter
open scoped Topology

set_option maxRecDepth 10000

def weight (n k j : ℕ) : ℝ :=
  (n.choose j : ℝ) * (k : ℝ) ^ j * ((n - k : ℕ) : ℝ) ^ (n - j)

theorem weight_nonneg (n k j : ℕ) : 0 ≤ weight n k j := by
  unfold weight
  positivity

theorem weight_recurrence {n k j : ℕ} (hj : j < n) :
    weight n k (j + 1) * ((j + 1 : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) =
      weight n k j * ((n - j : ℕ) : ℝ) * (k : ℝ) := by
  have hc : (n.choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) =
      (n.choose j : ℝ) * ((n - j : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq n j
  have hp : ((n - k : ℕ) : ℝ) ^ (n - j) =
      ((n - k : ℕ) : ℝ) ^ (n - (j + 1)) * ((n - k : ℕ) : ℝ) := by
    rw [show n - j = n - (j + 1) + 1 by omega, pow_succ]
  unfold weight
  rw [pow_succ, hp]
  calc
    _ = ((n.choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ)) *
        (k : ℝ) ^ j * ((n - k : ℕ) : ℝ) ^ (n - (j + 1)) * k * (n - k : ℕ) := by ring
    _ = ((n.choose j : ℝ) * ((n - j : ℕ) : ℝ)) *
        (k : ℝ) ^ j * ((n - k : ℕ) : ℝ) ^ (n - (j + 1)) * k * (n - k : ℕ) := by rw [hc]
    _ = _ := by ring

theorem weight_step_up {n k j : ℕ} (hk : k < n) (hj : j < k) :
    weight n k j ≤ weight n k (j + 1) := by
  have hrec := weight_recurrence (k := k) (lt_trans hj hk)
  have hsub : 0 < n - k := Nat.sub_pos_of_lt hk
  have hcpos : 0 < ((j + 1 : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) := by positivity
  have hfactor : ((j + 1 : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) ≤
      ((n - j : ℕ) : ℝ) * (k : ℝ) := by
    rw [Nat.cast_sub hk.le, Nat.cast_sub (lt_trans hj hk).le, Nat.cast_add, Nat.cast_one]
    have hkj : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
    have hn : 0 ≤ (n : ℝ) := by positivity
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hkj)]
  have hmul := mul_le_mul_of_nonneg_left hfactor (weight_nonneg n k j)
  apply (mul_le_mul_iff_of_pos_right hcpos).mp
  nlinarith

theorem weight_step_down {n k j : ℕ} (hk : k < n) (hj : k ≤ j) :
    weight n k (j + 1) ≤ weight n k j := by
  by_cases hjn : j < n
  · have hrec := weight_recurrence (k := k) hjn
    have hsub : 0 < n - k := Nat.sub_pos_of_lt hk
    have hcpos : 0 < ((j + 1 : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) := by positivity
    have hfactor : ((n - j : ℕ) : ℝ) * (k : ℝ) ≤
        ((j + 1 : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) := by
      rw [Nat.cast_sub hk.le, Nat.cast_sub hjn.le, Nat.cast_add, Nat.cast_one]
      have hkj : (k : ℝ) ≤ j := by exact_mod_cast hj
      have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk.le
      have hn : 0 ≤ (n : ℝ) := by positivity
      nlinarith [mul_nonneg hn (sub_nonneg.mpr hkj)]
    have hmul := mul_le_mul_of_nonneg_left hfactor (weight_nonneg n k j)
    apply (mul_le_mul_iff_of_pos_right hcpos).mp
    nlinarith
  · have hz : weight n k (j + 1) = 0 := by
      simp [weight, Nat.choose_eq_zero_of_lt (by omega : n < j + 1)]
    rw [hz]
    exact weight_nonneg n k j

theorem weight_mode {n k j : ℕ} (hk : k < n) : weight n k j ≤ weight n k k := by
  by_cases hj : j ≤ k
  · have hu : ∀ {a b : ℕ}, a ≤ b → b ≤ k → weight n k a ≤ weight n k b := by
      intro a b hab
      induction hab with
      | refl => intro _; exact le_rfl
      | @step b hab ih =>
          intro hbk
          exact (ih (by omega)).trans (weight_step_up hk (by omega))
    exact hu hj le_rfl
  · have hd : AntitoneOn (weight n k) {i | k ≤ i} :=
      antitoneOn_nat_Ici_of_succ_le (fun i hi => weight_step_down hk hi)
    have hkj : k ≤ j := by omega
    exact hd (a := k) (by simp) (b := j) hkj hkj

theorem sum_weight {n k : ℕ} (hk : k ≤ n) :
    ∑ j ∈ range (n + 1), weight n k j = (n : ℝ) ^ n := by
  have h := add_pow (k : ℝ) ((n - k : ℕ) : ℝ) n
  rw [← Nat.cast_add, Nat.add_sub_of_le hk] at h
  rw [h]
  apply sum_congr rfl
  intro j _
  unfold weight
  ring

theorem weight_bounds {n k : ℕ} (hk : k < n) :
    weight n k k ≤ (n : ℝ) ^ n ∧
      (n : ℝ) ^ n ≤ (n + 1 : ℝ) * weight n k k := by
  constructor
  · rw [← sum_weight hk.le]
    exact single_le_sum (fun j _ => weight_nonneg n k j) (mem_range.mpr (by omega))
  · rw [← sum_weight hk.le]
    calc
      _ ≤ ∑ _j ∈ range (n + 1), weight n k k := sum_le_sum (fun _ _ => weight_mode hk)
      _ = _ := by simp

theorem weight_positive {n k : ℕ} (hk0 : 0 < k) (hk : k < n) :
    0 < weight n k k := by
  have hc : 0 < n.choose k := Nat.choose_pos hk.le
  have hsub : 0 < n - k := Nat.sub_pos_of_lt hk
  unfold weight
  positivity

theorem log_weight {n k : ℕ} (hk0 : 0 < k) (hk : k < n) :
    Real.log (weight n k k) = Real.log (n.choose k : ℝ) +
      (k : ℝ) * Real.log k + ((n - k : ℕ) : ℝ) * Real.log (n - k : ℕ) := by
  have hc : 0 < n.choose k := Nat.choose_pos hk.le
  have hsub : 0 < n - k := Nat.sub_pos_of_lt hk
  unfold weight
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]

theorem entropy_numerator {n k : ℕ} (hk0 : 0 < k) (hk : k < n) :
    (n : ℝ) * Real.binEntropy ((k : ℝ) / n) = (n : ℝ) * Real.log n -
      (k : ℝ) * Real.log k - ((n - k : ℕ) : ℝ) * Real.log (n - k : ℕ) := by
  have hn : (n : ℝ) ≠ 0 := by have : 0 < n := lt_trans hk0 hk; positivity
  have hk' : (k : ℝ) ≠ 0 := by positivity
  have hsub : 0 < n - k := Nat.sub_pos_of_lt hk
  have hsub' : ((n - k : ℕ) : ℝ) ≠ 0 := by positivity
  have hcomp : (1 : ℝ) - (k : ℝ) / n = ((n - k : ℕ) : ℝ) / n := by
    rw [Nat.cast_sub hk.le]
    field_simp
  unfold Real.binEntropy
  simp only [Real.log_inv]
  rw [hcomp, Real.log_div hk' hn, Real.log_div hsub' hn]
  rw [Nat.cast_sub hk.le]
  field_simp
  ring

theorem log_choose_entropy_bounds_interior {n k : ℕ} (hk0 : 0 < k) (hk : k < n) :
    (n : ℝ) * Real.binEntropy ((k : ℝ) / n) - Real.log (n + 1 : ℝ) ≤
        Real.log (n.choose k : ℝ) ∧
      Real.log (n.choose k : ℝ) ≤ (n : ℝ) * Real.binEntropy ((k : ℝ) / n) := by
  have hn : 0 < n := lt_trans hk0 hk
  have hw := weight_bounds hk
  have hup := Real.log_le_log (weight_positive hk0 hk) hw.1
  have hlo := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) ^ n) hw.2
  rw [Real.log_pow, log_weight hk0 hk] at hup
  rw [Real.log_pow, Real.log_mul (by positivity : (n + 1 : ℝ) ≠ 0)
    (weight_positive hk0 hk).ne', log_weight hk0 hk] at hlo
  rw [entropy_numerator hk0 hk]
  constructor <;> linarith

/-- Finite entropy bounds, including zero and full layers. -/
theorem log_choose_entropy_bounds {n k : ℕ} (hk : k ≤ n) :
    (n : ℝ) * Real.binEntropy ((k : ℝ) / n) - Real.log (n + 1 : ℝ) ≤
        Real.log (n.choose k : ℝ) ∧
      Real.log (n.choose k : ℝ) ≤ (n : ℝ) * Real.binEntropy ((k : ℝ) / n) := by
  have hl : 0 ≤ Real.log (n + 1 : ℝ) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  by_cases hk0 : k = 0
  · subst k
    simp only [Nat.choose_zero_right, Nat.cast_zero, zero_div, Real.binEntropy_zero,
      mul_zero, Nat.cast_one, Real.log_one, zero_sub]
    exact ⟨by linarith, le_rfl⟩
  by_cases hkn : k = n
  · subst k
    have hn : (n : ℝ) ≠ 0 := by exact_mod_cast hk0
    simp only [Nat.choose_self, div_self hn, Real.binEntropy_one, mul_zero,
      Nat.cast_one, Real.log_one, zero_sub]
    exact ⟨by linarith, le_rfl⟩
  exact log_choose_entropy_bounds_interior (Nat.pos_of_ne_zero hk0) (lt_of_le_of_ne hk hkn)

/-- Exact finite error on an integer multiple of a rational-proportion layer. -/
theorem fixed_ratio_bounds {c r m : ℕ} (hc : 0 < c) (hr : r ≤ c) (hm : 0 < m) :
    (c : ℝ) * Real.binEntropy ((r : ℝ) / c) - Real.log (c * m + 1 : ℝ) / m ≤
        Real.log ((c * m).choose (r * m) : ℝ) / m ∧
      Real.log ((c * m).choose (r * m) : ℝ) / m ≤
        (c : ℝ) * Real.binEntropy ((r : ℝ) / c) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have h := log_choose_entropy_bounds (Nat.mul_le_mul_right m hr)
  have hp : (((r * m : ℕ) : ℝ) / ((c * m : ℕ) : ℝ)) = (r : ℝ) / c := by
    push_cast
    field_simp
  rw [hp, Nat.cast_mul] at h
  constructor
  · apply (le_div_iff₀ hm').mpr
    have heq : ((c : ℝ) * Real.binEntropy ((r : ℝ) / c) -
        Real.log (c * m + 1 : ℝ) / m) * m =
        (c : ℝ) * m * Real.binEntropy ((r : ℝ) / c) - Real.log (c * m + 1 : ℝ) := by
      field_simp
    rw [heq]
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using h.1
  · apply (div_le_iff₀ hm').mpr
    nlinarith [h.2]

theorem logarithmic_error_tendsto_zero {c : ℕ} (hc : 0 < c) :
    Tendsto (fun m : ℕ => Real.log (c * m + 1 : ℝ) / m) atTop (𝓝 0) := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hn : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have harg : Tendsto (fun m : ℕ => (c : ℝ) * m + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (hn.const_mul_atTop hc')
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp harg
  have hi := hn.inv_tendsto_atTop
  have hprod := hl.mul ((tendsto_const_nhds (x := (c : ℝ))).add hi)
  have heq : (fun m : ℕ => Real.log (c * m + 1 : ℝ) / m) =ᶠ[atTop]
      (fun m : ℕ => (Real.log (c * m + 1 : ℝ) / (c * m + 1)) * ((c : ℝ) + (m : ℝ)⁻¹)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hm)
    field_simp
  apply Tendsto.congr' heq.symm
  simpa only [Function.comp_apply, id_eq, zero_mul, Pi.inv_apply] using hprod

/-- The entropy rate follows from the explicit logarithmic finite error. -/
theorem fixed_ratio_tendsto {c r : ℕ} (hc : 0 < c) (hr : r ≤ c) :
    Tendsto (fun m : ℕ => Real.log ((c * m).choose (r * m) : ℝ) / m) atTop
      (𝓝 ((c : ℝ) * Real.binEntropy ((r : ℝ) / c))) := by
  have herr := logarithmic_error_tendsto_zero hc
  have hlo := (tendsto_const_nhds (x := (c : ℝ) * Real.binEntropy ((r : ℝ) / c))).sub herr
  have hbounds : ∀ᶠ m : ℕ in atTop,
      (c : ℝ) * Real.binEntropy ((r : ℝ) / c) - Real.log (c * m + 1 : ℝ) / m ≤
          Real.log ((c * m).choose (r * m) : ℝ) / m ∧
        Real.log ((c * m).choose (r * m) : ℝ) / m ≤
          (c : ℝ) * Real.binEntropy ((r : ℝ) / c) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    exact fixed_ratio_bounds hc hr (by omega)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using hlo) tendsto_const_nhds (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)

theorem fixed_ratio_bits_tendsto {c r : ℕ} (hc : 0 < c) (hr : r ≤ c) :
    Tendsto (fun m : ℕ => Real.log ((c * m).choose (r * m) : ℝ) / ((m : ℝ) * Real.log 2))
      atTop (𝓝 ((c : ℝ) * ThreeSum.Parameters.entropy ((r : ℝ) / c))) := by
  have h := (fixed_ratio_tendsto hc hr).div_const (Real.log 2)
  simpa [div_div, ThreeSum.Parameters.entropy, mul_div_assoc] using h

/-- The actual local output count has exponent `2 E` relative to `D=2^mu`. -/
theorem output_table_rate :
    Tendsto (fun m : ℕ => Real.log ((256 * m).choose m : ℝ) / ((m : ℝ) * Real.log 2))
      atTop (𝓝 (2 * ThreeSum.Parameters.E)) := by
  have h := fixed_ratio_bits_tendsto (c := 256) (r := 1) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num [ThreeSum.Parameters.E] <;> ring

/-- The actual local vertex count, with `mu=2h`, has the multiplicity rate used by the cover. -/
theorem vertex_table_rate :
    Tendsto (fun h : ℕ => Real.log ((512 * h).choose h : ℝ) / ((2 * h : ℝ) * Real.log 2))
      atTop (𝓝 (ThreeSum.Parameters.E + 1 / 2 + ThreeSum.Parameters.kappa / 2)) := by
  have h := (fixed_ratio_bits_tendsto (c := 512) (r := 1) (by norm_num) (by norm_num)).div_const 2
  convert h using 1
  · funext m
    simp only [Nat.one_mul, div_div]
    congr 1
    ring
  · norm_num [ThreeSum.Parameters.E, ThreeSum.Parameters.kappa]
    ring

/-- The maximum degree layer of the balanced microblock graph. -/
theorem degree_table_rate :
    Tendsto (fun h : ℕ => Real.log ((511 * h).choose h : ℝ) / ((2 * h : ℝ) * Real.log 2))
      atTop (𝓝 ((511 / 2 : ℝ) * ThreeSum.Parameters.entropy (1 / 511))) := by
  have h := (fixed_ratio_bits_tendsto (c := 511) (r := 1) (by norm_num) (by norm_num)).div_const 2
  convert h using 1
  · funext m
    simp only [Nat.one_mul, div_div]
    congr 1
    ring
  · norm_num
    ring

end ThreeSum.BinomialEntropy
