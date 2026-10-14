import Submission.ThreeSum.TernaryQuery

/-!
# Homogeneous reconstruction above the ternary bank

This is an exact integer identity for the binomial transform. It applies to
every source word of a fixed rank, including source/query states outside the
stored rank bank.
-/

noncomputable section
namespace ThreeSum.TernaryEuler

open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank

def predDigit (d : Fin 3) : Fin 3 := ⟨d.val - 1, by omega⟩

def predecessor {N : ℕ} (R : TritWord N) (i : Fin N) : TritWord N :=
  Function.update R i (predDigit (R i))

def digitChoose (r a : Fin 3) : ℤ := Nat.choose r.val a.val

def weight {N : ℕ} (R A : TritWord N) : ℤ := ∏ i, digitChoose (R i) (A i)

def binomialZeta {N : ℕ} (f : TritWord N → ℤ) (R : TritWord N) : ℤ :=
  ∑ A, weight R A * f A

theorem digit_euler (r a : Fin 3) :
    (r.val : ℤ) * digitChoose (predDigit r) a =
      ((r.val : ℤ) - (a.val : ℤ)) * digitChoose r a := by
  fin_cases r <;> fin_cases a <;> norm_num [digitChoose, predDigit, Nat.choose]

theorem weight_split {N : ℕ} (R A : TritWord N) (i : Fin N) :
    weight R A = digitChoose (R i) (A i) *
      ∏ j ∈ (univ : Finset (Fin N)).erase i, digitChoose (R j) (A j) := by
  exact (Finset.mul_prod_erase univ _ (mem_univ i)).symm

theorem predecessor_weight {N : ℕ} (R A : TritWord N) (i : Fin N) :
    weight (predecessor R i) A = digitChoose (predDigit (R i)) (A i) *
      ∏ j ∈ (univ : Finset (Fin N)).erase i, digitChoose (R j) (A j) := by
  rw [weight_split _ _ i]
  simp only [predecessor, Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp [Function.update_of_ne (mem_erase.mp hj).1]

theorem coordinate_weight_euler {N : ℕ} (R A : TritWord N) (i : Fin N) :
    (R i).val * weight (predecessor R i) A =
      ((R i).val - (A i).val : ℤ) * weight R A := by
  rw [predecessor_weight, weight_split R A i, ← mul_assoc, digit_euler]
  ring

theorem weight_euler {N : ℕ} (R A : TritWord N) :
    (∑ i : Fin N, (R i).val * weight (predecessor R i) A) =
      ((rank R : ℤ) - (rank A : ℤ)) * weight R A := by
  simp only [coordinate_weight_euler, ← Finset.sum_mul, Finset.sum_sub_distrib]
  simp [rank]

theorem binomialZeta_euler_general {N : ℕ} (f : TritWord N → ℤ) (R : TritWord N) :
    (∑ i : Fin N, (R i).val * binomialZeta f (predecessor R i)) =
      ∑ A : TritWord N, ((rank R : ℤ) - (rank A : ℤ)) * weight R A * f A := by
  unfold binomialZeta
  simp only [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  rw [← Finset.sum_mul, weight_euler]

/-- The Euler denominator uses the source rank, not the output rank. -/
theorem binomialZeta_euler {N : ℕ} (f : TritWord N → ℤ) (h : ℕ)
    (hf : ∀ A, f A ≠ 0 → rank A = h) (R : TritWord N) :
    (∑ i : Fin N, (R i).val * binomialZeta f (predecessor R i)) =
      ((rank R : ℤ) - (h : ℤ)) * binomialZeta f R := by
  rw [binomialZeta_euler_general]
  unfold binomialZeta
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hzero : f A = 0
  · simp [hzero]
  · rw [hf A hzero]
    ring

theorem predecessor_rank_lt {N : ℕ} (R : TritWord N) (i : Fin N)
    (hi : 0 < (R i).val) : rank (predecessor R i) < rank R := by
  unfold rank predecessor
  rw [← Finset.add_sum_erase univ (fun j => (R j).val) (mem_univ i),
    ← Finset.add_sum_erase univ
      (fun j => (Function.update R i (predDigit (R i)) j).val) (mem_univ i)]
  have hrest :
      (∑ j ∈ (univ : Finset (Fin N)).erase i,
        (Function.update R i (predDigit (R i)) j).val) =
      ∑ j ∈ (univ : Finset (Fin N)).erase i, (R j).val := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [Function.update_of_ne (mem_erase.mp hj).1]
  rw [hrest]
  simp only [Function.update_self, predDigit]
  omega

theorem predecessor_below {N : ℕ} (R : TritWord N) (i : Fin N) :
    Below (predecessor R i) R := by
  apply ThreeSum.TernaryQuery.update_below
  change (R i).val - 1 ≤ (R i).val
  omega

/-- All positive-coefficient predecessor reads are either bank reads or remain
in the same bounded-deficit query neighborhood. -/
theorem predecessor_bank_or_near {N T : ℕ} {R Q : TritWord N}
    (hRQ : Below R Q) (i : Fin N) :
    predecessor R i ∈ bank N T ∨
      predecessor R i ∈ nearWords Q (rank Q - (T+1)) := by
  by_cases hlow : rank (predecessor R i) ≤ T
  · exact Or.inl (mem_bank.mpr hlow)
  · apply Or.inr
    apply mem_nearWords.mpr
    have hbelow : Below (predecessor R i) Q := fun j =>
      (predecessor_below R i j).trans (hRQ j)
    refine ⟨hbelow, ?_⟩
    have hsum := rank_add_deficit hbelow
    omega

/-- Values on the rank bank uniquely determine a homogeneous binomial transform. -/
theorem euler_unique_from_bank {N h T : ℕ} (hcut : h ≤ T)
    (F G : TritWord N → ℤ)
    (hF : ∀ R, (∑ i : Fin N, (R i).val * F (predecessor R i)) =
      ((rank R : ℤ) - (h : ℤ)) * F R)
    (hG : ∀ R, (∑ i : Fin N, (R i).val * G (predecessor R i)) =
      ((rank R : ℤ) - (h : ℤ)) * G R)
    (hbank : ∀ R ∈ bank N T, F R = G R) : F = G := by
  funext R
  have hall : ∀ k, ∀ R : TritWord N, rank R = k → F R = G R := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro R hR
      by_cases hlow : rank R ≤ T
      · exact hbank R (mem_bank.mpr hlow)
      · have hsum : (∑ i : Fin N, (R i).val * F (predecessor R i)) =
            ∑ i : Fin N, (R i).val * G (predecessor R i) := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hz : (R i).val = 0
          · simp [hz]
          · have hr := predecessor_rank_lt R i (Nat.pos_of_ne_zero hz)
            rw [ih (rank (predecessor R i)) (by omega) (predecessor R i) rfl]
        rw [hF R, hG R] at hsum
        have hn : ((rank R : ℤ) - (h : ℤ)) ≠ 0 := by
          have : h < rank R := by omega
          omega
        exact mul_left_cancel₀ hn hsum
  exact hall (rank R) R rfl

end ThreeSum.TernaryEuler
