import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic

/-! # Conjunction represented by the product of independently computed flags -/

namespace ThreeSum.SourceFlagProduct

open Finset
open scoped BigOperators

def product (flag : ℕ → ℕ) (n : ℕ) : ℕ := ∏ i ∈ range n, flag i

@[simp] theorem product_zero (flag : ℕ → ℕ) : product flag 0=1 := by simp [product]

theorem product_succ (flag : ℕ → ℕ) (n : ℕ) :
    product flag (n+1)=product flag n*flag n := Finset.prod_range_succ _ _

theorem product_le {n j : ℕ} (flag : ℕ → ℕ)
    (hflag : ∀ i < n, flag i ≤ 1) (hj : j ≤ n) : product flag j ≤ 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [product_succ]
    exact (Nat.mul_le_mul (ih (by omega)) (hflag j (by omega))).trans (by decide)

theorem product_eq_one_iff (flag : ℕ → ℕ) (n : ℕ) :
    product flag n=1 ↔ ∀ i < n, flag i=1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [product_succ,mul_eq_one,ih]
    constructor
    · rintro ⟨hprev,hn⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact hprev i hi
      · exact hn
    · intro hall
      exact ⟨fun i hi => hall i (by omega),hall n (by omega)⟩

theorem product_eq_indicator (flag : ℕ → ℕ) (n : ℕ) (p : Prop) [Decidable p]
    (hflag : ∀ i < n, flag i ≤ 1) (hp : (∀ i < n, flag i=1) ↔ p) :
    product flag n = if p then 1 else 0 := by
  have he := (product_eq_one_iff flag n).trans hp
  have hle := product_le flag hflag le_rfl
  by_cases hh : p
  · simp only [hh,ite_true]
    exact he.mpr hh
  · simp only [hh,ite_false]
    have hn : product flag n≠1 := fun h => hh (he.mp h)
    omega

end ThreeSum.SourceFlagProduct
