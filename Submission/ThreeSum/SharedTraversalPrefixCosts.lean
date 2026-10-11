import Submission.ThreeSum.SharedTraversalCosts

/-!
# Summing the actual dense-guard branches in physical slot order

The counter at slot i is the mass of slots before i. The expensive branch
is charged only when adding the current mass still fits the threshold.
These charges sum to at most that threshold, including when a later slot
crosses it. No bound on the mass of the crossing slot is required.
-/

namespace ThreeSum.SharedTraversalCosts

open Finset
open scoped BigOperators

def prefixMass (mass : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ range n, mass i

def guardedMass (mass : ℕ → ℕ) (threshold n : ℕ) : ℕ :=
  ∑ i ∈ range n, if threshold < prefixMass mass i+mass i then 0 else mass i

theorem prefixMass_zero (mass : ℕ → ℕ) : prefixMass mass 0=0 := by simp [prefixMass]

theorem prefixMass_succ (mass : ℕ → ℕ) (n : ℕ) :
    prefixMass mass (n+1)=prefixMass mass n+mass n := by
  simp only [prefixMass,sum_range_succ]

theorem guardedMass_le_prefix (mass : ℕ → ℕ) (threshold n : ℕ) :
    guardedMass mass threshold n ≤ prefixMass mass n := by
  unfold guardedMass prefixMass
  exact sum_le_sum (fun i _ => by split <;> omega)

theorem guardedMass_le_threshold (mass : ℕ → ℕ) (threshold n : ℕ) :
    guardedMass mass threshold n ≤ threshold := by
  induction n with
  | zero => simp [guardedMass]
  | succ n ih =>
      have hp := guardedMass_le_prefix mass threshold n
      simp only [guardedMass,sum_range_succ] at ih ⊢
      by_cases hg : threshold < prefixMass mass n+mass n
      · simp only [if_pos hg,add_zero]
        exact ih
      · simp only [if_neg hg]
        change guardedMass mass threshold n+mass n ≤ threshold
        omega

def guardedBudget (mass : ℕ → ℕ) (threshold initial work n : ℕ) : ℕ :=
  ∑ i ∈ range n, (initial+
    if threshold < prefixMass mass i+mass i then 0 else mass i*work)

theorem guardedBudget_eq (mass : ℕ → ℕ) (threshold initial work n : ℕ) :
    guardedBudget mass threshold initial work n =
      n*initial+guardedMass mass threshold n*work := by
  unfold guardedBudget guardedMass
  rw [sum_add_distrib,sum_mul]
  simp only [sum_const,card_range,smul_eq_mul]
  congr 1
  apply sum_congr rfl
  intro i hi
  split <;> simp

theorem guardedBudget_le (mass : ℕ → ℕ) (threshold initial work n : ℕ) :
    guardedBudget mass threshold initial work n ≤ n*initial+threshold*work := by
  rw [guardedBudget_eq]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right work
    (guardedMass_le_threshold mass threshold n)) _

/-- A direct interface for the recursive ascending-slot machine counter. -/
theorem prefix_time_le {time mass : ℕ → ℕ} {threshold initial work : ℕ}
    (hzero : time 0 ≤ 30)
    (hstep : ∀ i, time (i+1) ≤ time i+initial+
      if threshold < prefixMass mass i+mass i then 0 else mass i*work) (n : ℕ) :
    time n ≤ 30+n*initial+threshold*work := by
  have hsum : ∀ n, time n ≤ 30+guardedBudget mass threshold initial work n := by
    intro k
    induction k with
    | zero => simpa [guardedBudget] using hzero
    | succ k ih =>
        have hs := hstep k
        simp only [guardedBudget,sum_range_succ] at ih ⊢
        omega
  have hh := guardedBudget_le mass threshold initial work n
  have hs := hsum n
  omega

end ThreeSum.SharedTraversalCosts
