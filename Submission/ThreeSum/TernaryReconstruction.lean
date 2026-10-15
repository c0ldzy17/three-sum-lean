import Submission.ThreeSum.TernaryEuler

/-!
# Exact terminating reconstruction and frozen-coordinate query oracle

`recover` is a finite evaluator using integer division of the homogeneous
Euler numerator. `firstCross` branches a coordinate once to its complete lower
value, then freezes it. The bank oracle supplies the corresponding remaining
inverse stage. These are semantic evaluators; memory access and RAM running
time are separate interfaces.
-/

namespace ThreeSum.TernaryReconstruction

open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryQuery ThreeSum.TernaryEuler

def recover {N : ℕ} (seed : TritWord N → ℤ) (h T : ℕ) :
    ℕ → TritWord N → ℤ
  | 0, R => seed R
  | k + 1, R =>
      if rank R ≤ T then seed R else
        (∑ i : Fin N, if (R i).val = 0 then 0 else
          (R i).val * recover seed h T k (predecessor R i)) /
          ((rank R : ℤ) - (h : ℤ))

theorem recover_eq {N h T : ℕ} (hcut : h ≤ T) (seed F : TritWord N → ℤ)
    (hbank : ∀ R ∈ bank N T, seed R = F R)
    (hEuler : ∀ R, (∑ i : Fin N, (R i).val * F (predecessor R i)) =
      ((rank R : ℤ) - (h : ℤ)) * F R)
    (fuel : ℕ) (R : TritWord N) (hbound : rank R ≤ T + fuel) :
    recover seed h T fuel R = F R := by
  induction fuel generalizing R with
  | zero =>
      exact hbank R (mem_bank.mpr (by simpa using hbound))
  | succ k ih =>
      simp only [recover]
      by_cases hlow : rank R ≤ T
      · simp [hlow, hbank R (mem_bank.mpr hlow)]
      · simp only [hlow, ↓reduceIte]
        have hsum : (∑ i : Fin N, if (R i).val = 0 then 0 else
              (R i).val * recover seed h T k (predecessor R i)) =
            ∑ i : Fin N, (R i).val * F (predecessor R i) := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hz : (R i).val = 0
          · simp [hz]
          · have hr := predecessor_rank_lt R i (Nat.pos_of_ne_zero hz)
            simp only [hz, ↓reduceIte]
            rw [ih (predecessor R i) (by omega)]
        rw [hsum, hEuler]
        have hn : ((rank R : ℤ) - (h : ℤ)) ≠ 0 := by
          have : h < rank R := by omega
          omega
        exact Int.mul_ediv_cancel_left _ hn

theorem recover_binomialZeta {N h T : ℕ} (hcut : h ≤ T)
    (f seed : TritWord N → ℤ) (hf : ∀ A, f A ≠ 0 → rank A = h)
    (hbank : ∀ R ∈ bank N T, seed R = binomialZeta f R) (R : TritWord N) :
    recover seed h T (rank R - T) R = binomialZeta f R := by
  apply recover_eq hcut seed (binomialZeta f) hbank (binomialZeta_euler f h hf)
  omega

def frozenInverse {N : ℕ} : List (Fin N) → (TritWord N → ℤ) → TritWord N → ℤ
  | [], H, R => H R
  | i :: rest, H, R =>
      inverseDigit (fun d => frozenInverse rest H (Function.update R i d)) (R i)

def firstCross {N : ℕ} (T : ℕ) (H : TritWord N → ℤ) :
    List (Fin N) → TritWord N → ℤ
  | [], R => H R
  | i :: rest, R =>
      if rank R ≤ T then frozenInverse (i :: rest) H R else
        inverseDigit (fun d => firstCross T H rest (Function.update R i d)) (R i)

theorem firstCross_eq_frozenInverse {N : ℕ} (T : ℕ) (H : TritWord N → ℤ)
    (coords : List (Fin N)) (R : TritWord N) :
    firstCross T H coords R = frozenInverse coords H R := by
  induction coords generalizing R with
  | nil => rfl
  | cons i rest ih =>
      simp only [firstCross]
      split_ifs with h
      · rfl
      · simp only [frozenInverse, ih]

def inverseCoefficient (q r : Fin 3) : ℤ :=
  if r ≤ q then (-1 : ℤ) ^ (q.val - r.val) * Nat.choose q.val r.val else 0

theorem inverseDigit_eq_sum (f : Fin 3 → ℤ) (q : Fin 3) :
    inverseDigit f q = ∑ r : Fin 3, inverseCoefficient q r * f r := by
  fin_cases q <;>
    norm_num [inverseDigit, inverseCoefficient, Fin.sum_univ_succ,
      Fin.le_def, Nat.choose, show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide] <;> ring

/-- The coefficient is attached to a complete lower digit, once per coordinate. -/
theorem frozenInverse_cons {N : ℕ} (i : Fin N) (rest : List (Fin N))
    (H : TritWord N → ℤ) (R : TritWord N) :
    frozenInverse (i :: rest) H R = ∑ d : Fin 3, inverseCoefficient (R i) d *
      frozenInverse rest H (Function.update R i d) :=
  inverseDigit_eq_sum _ _

end ThreeSum.TernaryReconstruction
