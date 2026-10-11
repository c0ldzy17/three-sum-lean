import Submission.ThreeSum.BinomialEntropy
import Submission.ThreeSum.Asymptotics
import Mathlib.NumberTheory.Chebyshev

/-!
# A proved supply of candidates for the deterministic modulus chain

The candidate interval is `(y, 4*y]`, a subset of `[y, 4*y]`. This is an explicit
revision from the preliminary `[y,2*y]` interval: Mathlib's elementary Chebyshev
constants give a positive difference on the fourfold interval. Multiplying the
window width by this fixed constant changes none of the target exponents.

The final theorem proves a concrete lower bound `y / (4 log y)` on the cardinality,
for every sufficiently large integer `y`. The set is an explicitly computable finset.
-/

namespace ThreeSum.PrimeDensity

open Real Filter Finset
open scoped Topology

def candidates (y : ℕ) : Finset ℕ := Nat.primesLE (4 * y) \ Nat.primesLE y

noncomputable section

theorem mem_candidates {p y : ℕ} :
    p ∈ candidates y ↔ Nat.Prime p ∧ y < p ∧ p ≤ 4 * y := by
  unfold candidates
  rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hp4, hp⟩, hn⟩
    refine ⟨hp, ?_, hp4⟩
    by_contra h
    exact hn ⟨by omega, hp⟩
  · rintro ⟨hp, hyp, hp4⟩
    exact ⟨⟨hp4, hp⟩, fun h => (not_le_of_gt hyp) h.1⟩

theorem candidate_card_add (y : ℕ) :
    (candidates y).card + Nat.primeCounting y = Nat.primeCounting (4 * y) := by
  have hsub : Nat.primesLE y ⊆ Nat.primesLE (4 * y) := Nat.primesLE_mono (by omega)
  simpa only [candidates, Nat.primesLE_card_eq_primeCounting] using card_sdiff_add_card_eq_card hsub

def lowerScaled (y : ℕ) : ℝ :=
  (4 * Real.log 2 - Real.log (4 * y + 1 : ℝ) / y) /
    (1 + Real.log 4 / Real.log y)

theorem lowerScaled_tendsto : Tendsto lowerScaled atTop (𝓝 (4 * Real.log 2)) := by
  have herr := ThreeSum.BinomialEntropy.logarithmic_error_tendsto_zero (c := 4) (by norm_num)
  have hinv := ThreeSum.Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop
  have hnum := (tendsto_const_nhds (x := 4 * Real.log 2)).sub herr
  have hsmall := hinv.const_mul (Real.log 4)
  have hden := (tendsto_const_nhds (x := (1 : ℝ))).add hsmall
  have h := hnum.div hden (by norm_num : (1 + Real.log 4 * 0 : ℝ) ≠ 0)
  unfold lowerScaled
  simpa [Pi.div_def, Pi.mul_def, div_eq_mul_inv, Pi.inv_apply] using h

theorem lowerScaled_identity {y : ℕ} (hy : 1 < y) :
    lowerScaled y * ((y : ℝ) / Real.log y) =
      ((4 * y : ℝ) * Real.log 2 - Real.log (4 * y + 1 : ℝ)) / Real.log (4 * y : ℝ) := by
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (lt_trans Nat.zero_lt_one hy)
  have hlog : (0 : ℝ) < Real.log y := Real.log_pos (by exact_mod_cast hy)
  have hlog4y : Real.log (4 * y : ℝ) = Real.log 4 + Real.log y :=
    Real.log_mul (by norm_num) hy0.ne'
  have hsum : Real.log 4 + Real.log y ≠ 0 := by
    have h4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
    linarith
  unfold lowerScaled
  rw [hlog4y]
  field_simp
  ring

theorem eventually_lower_count :
    ∀ᶠ y : ℕ in atTop, (2 : ℝ) * ((y : ℝ) / Real.log y) ≤ Nat.primeCounting (4 * y) := by
  have htwo : (2 : ℝ) < 4 * Real.log 2 := by linarith [ThreeSum.Parameters.log_two_lower]
  have hs := lowerScaled_tendsto.eventually (lt_mem_nhds htwo)
  filter_upwards [hs, eventually_ge_atTop (2 : ℕ)] with y hs hy
  have hy1 : 1 < y := by omega
  have hratio : 0 ≤ (y : ℝ) / Real.log y := by
    apply div_nonneg (Nat.cast_nonneg y)
    exact (Real.log_pos (by exact_mod_cast hy1)).le
  have hmul := mul_le_mul_of_nonneg_right hs.le hratio
  rw [lowerScaled_identity hy1] at hmul
  have hpi := Chebyshev.pi_ge (4 * y)
  push_cast at hpi
  exact hmul.trans hpi

theorem eventually_upper_count :
    ∀ᶠ y : ℕ in atTop, (Nat.primeCounting y : ℝ) ≤ (7 / 4 : ℝ) * ((y : ℝ) / Real.log y) := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Chebyshev.eventually_primeCounting_le (ε := (1 / 4 : ℝ)) (by norm_num))
  have hcoef : Real.log 4 + (1 / 4 : ℝ) < 7 / 4 := by
    have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith [ThreeSum.Parameters.log_two_upper]
  filter_upwards [h, eventually_ge_atTop (2 : ℕ)] with y hy hge
  have hy1 : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hratio : 0 ≤ (y : ℝ) / Real.log y :=
    div_nonneg (Nat.cast_nonneg y) (Real.log_pos hy1).le
  have hbound : (Nat.primeCounting y : ℝ) ≤
      (Real.log 4 + 1 / 4) * ((y : ℝ) / Real.log y) := by simpa only [Nat.floor_natCast, mul_div_assoc] using hy
  exact hbound.trans (mul_le_mul_of_nonneg_right hcoef.le hratio)

/-- A concrete elementary density theorem for the executable candidate finset. -/
theorem eventually_candidate_density :
    ∀ᶠ y : ℕ in atTop, (y : ℝ) / (4 * Real.log y) ≤ ((candidates y).card : ℝ) := by
  filter_upwards [eventually_lower_count, eventually_upper_count] with y hlo hhi
  have hcard : ((candidates y).card : ℝ) + (Nat.primeCounting y : ℝ) =
      (Nat.primeCounting (4 * y) : ℝ) := by exact_mod_cast candidate_card_add y
  have hid : (y : ℝ) / (4 * Real.log y) = (1 / 4 : ℝ) * ((y : ℝ) / Real.log y) := by ring
  rw [hid]
  linarith

theorem eventually_candidates_nonempty :
    ∀ᶠ y : ℕ in atTop, (candidates y).Nonempty := by
  filter_upwards [eventually_candidate_density, eventually_ge_atTop (2 : ℕ)] with y hy hge
  have hy1 : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hpos : (0 : ℝ) < (y : ℝ) / (4 * Real.log y) := by
    apply div_pos (by linarith)
    exact mul_pos (by norm_num) (Real.log_pos hy1)
  apply card_pos.mp
  exact_mod_cast lt_of_lt_of_le hpos hy

end

end ThreeSum.PrimeDensity
