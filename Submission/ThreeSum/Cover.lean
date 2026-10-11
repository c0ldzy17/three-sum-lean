import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-!
# Finite cover bounds

Finite, exact lemmas for the second-moment argument, deterministic averaging,
and composition used in the proposed construction.  A hypothesis about a
particular local hash family is a mathematical obligation, not an asserted
implementation or running-time theorem.
-/

namespace ThreeSum.Cover

open Finset
open scoped BigOperators

/-- Cauchy--Schwarz with the cardinality of the actual support. -/
theorem support_cauchy {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) :
    (∑ ω, f ω) ^ 2 ≤
      ((univ.filter fun ω => f ω ≠ 0).card : ℝ) * ∑ ω, (f ω) ^ 2 := by
  classical
  let s := univ.filter fun ω => f ω ≠ 0
  have hsum : ∑ ω ∈ s, f ω = ∑ ω, f ω := by
    simp only [s, sum_filter]
    apply sum_congr rfl
    intro ω _
    split_ifs with h
    · rfl
    · simp_all
  have hsq : ∑ ω ∈ s, (f ω) ^ 2 = ∑ ω, (f ω) ^ 2 := by
    simp only [s, sum_filter]
    apply sum_congr rfl
    intro ω _
    split_ifs with h
    · rfl
    · simp_all
  have h := sq_sum_le_card_mul_sum_sq (s := s) (f := f)
  rw [hsum, hsq] at h
  exact h

/-- The trimmed second-moment estimate, without division or probabilities.
If the first moment is at least lambda/2 and the second at most 5 lambda,
at least a lambda/20 fraction of the finite sample space is nonzero. -/
theorem trimmed_support_lower {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (hfirst : lam * Fintype.card Ω / 2 ≤ ∑ ω, f ω)
    (hsecond : (∑ ω, (f ω) ^ 2) ≤ 5 * lam * Fintype.card Ω) :
    lam * Fintype.card Ω ≤
      20 * ((univ.filter fun ω => f ω ≠ 0).card : ℝ) := by
  classical
  have hN : (0 : ℝ) < Fintype.card Ω := by
    exact_mod_cast Fintype.card_pos
  have hL : 0 < lam * Fintype.card Ω := mul_pos hlam hN
  have hc : (0 : ℝ) ≤ (univ.filter fun ω => f ω ≠ 0).card := by positivity
  have hS : 0 ≤ ∑ ω, f ω := le_trans (by positivity) hfirst
  have hsq := support_cauchy f
  have hup := mul_le_mul_of_nonneg_left hsecond hc
  have hlo : (lam * Fintype.card Ω) ^ 2 ≤ 4 * (∑ ω, f ω) ^ 2 := by
    nlinarith
  nlinarith

/-- The explicit 1/(320(mu+1)) support fraction used for a microblock. -/
theorem trimmed_support_fraction {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (mu : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (hlower : 1 ≤ 16 * (mu + 1 : ℝ) * lam)
    (hfirst : lam * Fintype.card Ω / 2 ≤ ∑ ω, f ω)
    (hsecond : (∑ ω, (f ω) ^ 2) ≤ 5 * lam * Fintype.card Ω) :
    (Fintype.card Ω : ℝ) ≤
      320 * (mu + 1 : ℝ) * ((univ.filter fun ω => f ω ≠ 0).card : ℝ) := by
  classical
  have h := trimmed_support_lower f hlam hfirst hsecond
  have h₁ := mul_le_mul_of_nonneg_right hlower
    (show (0 : ℝ) ≤ Fintype.card Ω by positivity)
  have h₂ := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ 16 * (mu + 1 : ℝ) by positivity)
  nlinarith

/-- Exact double counting of the incidence relation. -/
theorem incidence_card_sum {Ω U : Type*} [Fintype Ω] [DecidableEq U]
    (targets : Finset U) (covers : Ω → U → Prop)
    [DecidableRel covers] :
    (∑ ω, (targets.filter (covers ω)).card) =
      ∑ u ∈ targets, (univ.filter fun ω => covers ω u).card := by
  simp_rw [card_eq_sum_ones, sum_filter]
  rw [sum_comm]

/-- A finite positive average produces a deterministic good choice. -/
theorem exists_good_cover {Ω U : Type*} [Fintype Ω] [Nonempty Ω]
    [DecidableEq U] (targets : Finset U) (covers : Ω → U → Prop)
    [DecidableRel covers] (a : ℕ)
    (hfrequency : ∀ u ∈ targets,
      Fintype.card Ω ≤ a * (univ.filter fun ω => covers ω u).card) :
    ∃ ω, targets.card ≤ a * (targets.filter (covers ω)).card := by
  by_contra! hnone
  have hlow := sum_le_sum hfrequency
  have hhigh : (∑ ω, a * (targets.filter (covers ω)).card) <
      ∑ _ω : Ω, targets.card := by
    exact sum_lt_sum_of_nonempty (by simp) (by simpa using hnone)
  simp only [sum_const, nsmul_eq_mul, card_univ, ← mul_sum] at hlow hhigh
  rw [incidence_card_sum targets covers] at hhigh
  nlinarith

/-- An exact survivor recurrence after choosing a good map. -/
theorem survivor_step {U : Type*} [DecidableEq U]
    (targets : Finset U) (covers : U → Prop) [DecidablePred covers]
    (a : ℕ) (ha : 0 < a)
    (hgood : targets.card ≤ a * (targets.filter covers).card) :
    a * (targets.filter fun u => ¬ covers u).card ≤ (a - 1) * targets.card := by
  have hc := card_filter_add_card_filter_not (s := targets) (p := covers)
  have ha' : a - 1 + 1 = a := by omega
  nlinarith

end ThreeSum.Cover
