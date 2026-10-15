import Submission.ThreeSum.TernaryTransform

/-! Euler reconstruction for a source transform with an actual frozen prefix. -/

noncomputable section
namespace ThreeSum.TernaryPartialEuler

open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryTransform

set_option maxHeartbeats 2000000

theorem kernel_split {N : ℕ} (S : Finset (Fin N)) (R A : TritWord N)
    (i : Fin N) (hi : i∈S) :
    kernel S R A=digitChoose (R i) (A i)*
      ∏ j∈(univ : Finset (Fin N)).erase i,
        if j∈S then digitChoose (R j) (A j) else if A j=R j then 1 else 0 := by
  unfold kernel
  rw [← Finset.mul_prod_erase univ _ (mem_univ i)]
  simp [hi]

theorem predecessor_kernel {N : ℕ} (S : Finset (Fin N)) (R A : TritWord N)
    (i : Fin N) (hi : i∈S) :
    kernel S (predecessor R i) A=digitChoose (predDigit (R i)) (A i)*
      ∏ j∈(univ : Finset (Fin N)).erase i,
        if j∈S then digitChoose (R j) (A j) else if A j=R j then 1 else 0 := by
  rw [kernel_split S _ A i hi]
  simp only [predecessor,Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp [Function.update_of_ne (mem_erase.mp hj).1]

theorem coordinate_kernel_euler {N : ℕ} (S : Finset (Fin N)) (R A : TritWord N)
    (i : Fin N) (hi : i∈S) :
    (R i).val*kernel S (predecessor R i) A=
      ((R i).val-(A i).val : ℤ)*kernel S R A := by
  rw [predecessor_kernel S R A i hi,kernel_split S R A i hi,←mul_assoc,digit_euler]
  ring

theorem outside_difference_zero {N : ℕ} (S : Finset (Fin N)) (R A : TritWord N)
    (i : Fin N) (hi : i∉S) :
    ((R i).val-(A i).val : ℤ)*kernel S R A=0 := by
  by_cases he : A i=R i
  · simp [he]
  · have hz : kernel S R A=0 := by
      unfold kernel
      exact Finset.prod_eq_zero (mem_univ i) (by simp [hi,he])
    simp [hz]

theorem kernel_euler {N : ℕ} (S : Finset (Fin N)) (R A : TritWord N) :
    (∑ i∈S, (R i).val*kernel S (predecessor R i) A)=
      ((rank R : ℤ)-(rank A : ℤ))*kernel S R A := by
  calc
    (∑ i∈S, (R i).val*kernel S (predecessor R i) A) =
        ∑ i∈S, ((R i).val-(A i).val : ℤ)*kernel S R A := by
      apply Finset.sum_congr rfl
      intro i hi
      exact coordinate_kernel_euler S R A i hi
    _ = ∑ i : Fin N, ((R i).val-(A i).val : ℤ)*kernel S R A := by
      apply Finset.sum_subset (subset_univ S)
      intro i hi hnot
      exact outside_difference_zero S R A i hnot
    _ = ((rank R : ℤ)-(rank A : ℤ))*kernel S R A := by
      rw [←Finset.sum_mul,Finset.sum_sub_distrib]
      simp [rank]

theorem stageSum_euler_general {N : ℕ} (S : Finset (Fin N))
    (f : TritWord N→ℤ) (R : TritWord N) :
    (∑ i∈S, (R i).val*stageSum S f (predecessor R i))=
      ∑ A : TritWord N, ((rank R : ℤ)-(rank A : ℤ))*kernel S R A*f A := by
  unfold stageSum
  simp only [Finset.mul_sum,←mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  rw [←Finset.sum_mul,kernel_euler]

/-- Only the coordinates still transformed participate in the Euler numerator.
The denominator retains the rank of the complete word, including frozen coordinates. -/
theorem stageSum_euler {N h : ℕ} (S : Finset (Fin N)) (f : TritWord N→ℤ)
    (hf : ∀ A, f A≠0 → rank A=h) (R : TritWord N) :
    (∑ i∈S, (R i).val*stageSum S f (predecessor R i))=
      ((rank R : ℤ)-(h : ℤ))*stageSum S f R := by
  rw [stageSum_euler_general]
  unfold stageSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hz : f A=0
  · simp [hz]
  · rw [hf A hz]
    ring

def restrictedWeight {N : ℕ} (S : Finset (Fin N)) (R : TritWord N) (i : Fin N) : ℤ :=
  if i∈S then (R i).val else 0

def safePredecessor {N : ℕ} (S : Finset (Fin N)) (R dummy : TritWord N)
    (i : Fin N) : TritWord N :=
  if i∈S ∧ 0<(R i).val then predecessor R i else dummy

theorem safe_sum_eq {N : ℕ} (S : Finset (Fin N)) (R dummy : TritWord N)
    (F : TritWord N→ℤ) :
    (∑ i : Fin N, restrictedWeight S R i*F (safePredecessor S R dummy i))=
      ∑ i∈S, (R i).val*F (predecessor R i) := by
  have he : (∑ i : Fin N, restrictedWeight S R i*F (safePredecessor S R dummy i))=
      ∑ i : Fin N, if i∈S then (R i).val*F (predecessor R i) else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hs : i∈S
    · by_cases hz : (R i).val=0
      · simp [restrictedWeight,safePredecessor,hs,hz]
      · have hp : 0<(R i).val := Nat.pos_of_ne_zero hz
        simp [restrictedWeight,safePredecessor,hs,hp]
    · simp [restrictedWeight,hs]
  rw [he,←Finset.sum_filter]
  simp

/-- Zero-weight coordinates may use an arbitrary safe bank address. -/
theorem stageSum_euler_safe {N h : ℕ} (S : Finset (Fin N)) (f : TritWord N→ℤ)
    (hf : ∀ A, f A≠0 → rank A=h) (R dummy : TritWord N) :
    (∑ i : Fin N, restrictedWeight S R i*
        stageSum S f (safePredecessor S R dummy i))=
      ((rank R : ℤ)-(h : ℤ))*stageSum S f R := by
  rw [safe_sum_eq]
  exact stageSum_euler S f hf R

theorem restrictedWeight_nonneg {N : ℕ} (S : Finset (Fin N)) (R : TritWord N)
    (i : Fin N) : 0≤restrictedWeight S R i := by
  unfold restrictedWeight
  split <;> positivity

theorem restrictedWeight_le_two {N : ℕ} (S : Finset (Fin N)) (R : TritWord N)
    (i : Fin N) : restrictedWeight S R i≤2 := by
  have hi := (R i).isLt
  unfold restrictedWeight
  split <;> omega

end ThreeSum.TernaryPartialEuler
