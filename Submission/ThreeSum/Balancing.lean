import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith

/-! # An exact global offset chosen by a cyclic correlation -/

namespace ThreeSum.Balancing

open Finset
open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

def correlation (F H : G → ℕ) (d : G) : ℕ := ∑ k, F k * H (k - d)

theorem sum_correlation (F H : G → ℕ) :
    (∑ d, correlation F H d) = (∑ k, F k) * (∑ k, H k) := by
  unfold correlation
  rw [sum_comm]
  simp only [← mul_sum]
  have hshift (k : G) : (∑ d, H (k - d)) = ∑ d, H d := by
    exact Equiv.sum_comp (Equiv.subLeft k) H
  simp_rw [hshift]
  exact (sum_mul ..).symm

/-- The mean is exact for every table, with no hash-uniformity assumption. -/
theorem exists_balanced_offset (F H : G → ℕ) :
    ∃ d, Fintype.card G * correlation F H d ≤ (∑ k, F k) * (∑ k, H k) := by
  by_contra! h
  have hs : (∑ _d : G, (∑ k, F k) * (∑ k, H k)) <
      ∑ d, Fintype.card G * correlation F H d := by
    exact sum_lt_sum_of_nonempty (by simp) (by simpa using h)
  simp only [sum_const, nsmul_eq_mul, card_univ, ← mul_sum, sum_correlation] at hs
  exact (lt_irrefl _ hs)

/-- An actual finite minimum search, using the supplied order for ties. -/
def chooseOffset [Inhabited G] (keys : List G) (F H : G → ℕ) : G :=
  (keys.argmin (correlation F H)).getD default

theorem chooseOffset_le [Inhabited G] (keys : List G) (F H : G → ℕ)
    {d : G} (hd : d ∈ keys) :
    correlation F H (chooseOffset keys F H) ≤ correlation F H d := by
  unfold chooseOffset
  cases h : keys.argmin (correlation F H) with
  | none => have := List.argmin_eq_none.mp h; simp_all
  | some v =>
    simp only [Option.getD_some]
    exact List.le_of_mem_argmin (f := correlation F H) hd
      (by simpa only [Option.mem_def] using h)

theorem chooseOffset_balanced [Inhabited G] (keys : List G) (hall : ∀ d, d ∈ keys)
    (F H : G → ℕ) :
    Fintype.card G * correlation F H (chooseOffset keys F H) ≤
      (∑ k, F k) * (∑ k, H k) := by
  obtain ⟨d, hd⟩ := exists_balanced_offset F H
  exact (Nat.mul_le_mul_left _ (chooseOffset_le keys F H (hall d))).trans hd

end ThreeSum.Balancing
