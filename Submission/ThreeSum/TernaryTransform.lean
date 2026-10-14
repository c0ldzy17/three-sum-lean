import Submission.ThreeSum.TernaryEuler

/-! # The compressed coordinate stages compute the binomial source transform -/

noncomputable section
namespace ThreeSum.TernaryTransform

open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryQuery ThreeSum.TernaryEuler

def kernel {N : ℕ} (s : Finset (Fin N)) (R A : TritWord N) : ℤ :=
  ∏ i, if i ∈ s then digitChoose (R i) (A i) else if A i = R i then 1 else 0

def stageSum {N : ℕ} (s : Finset (Fin N)) (f : TritWord N → ℤ) (R : TritWord N) : ℤ :=
  ∑ A, kernel s R A * f A

theorem kernel_empty {N : ℕ} (R A : TritWord N) :
    kernel ∅ R A = if A = R then 1 else 0 := by
  by_cases h : A = R
  · subst A
    simp [kernel]
  · simp only [kernel, notMem_empty, ↓reduceIte, h]
    obtain ⟨i, hi⟩ : ∃ i, A i ≠ R i := by
      by_contra hn
      apply h
      funext i
      exact not_not.mp (not_exists.mp hn i)
    exact Finset.prod_eq_zero (mem_univ i) (by simp [hi])

theorem partial_empty {N : ℕ} (f : TritWord N → ℤ) : stageSum ∅ f = f := by
  funext R
  simp [stageSum, kernel_empty]

theorem partial_univ {N : ℕ} (f : TritWord N → ℤ) :
    stageSum univ f = binomialZeta f := by
  funext R
  simp [stageSum, kernel, binomialZeta, weight]

private theorem zeta_delta (q a : Fin 3) (C : ℤ) :
    zetaDigit (fun d => (if a = d then 1 else 0) * C) q = digitChoose q a * C := by
  fin_cases q <;> fin_cases a <;>
    norm_num [zetaDigit, digitChoose, Nat.choose, Fin.ext_iff] <;> ring

theorem coordinateZeta_sum {N : ℕ} {α : Type*} [Fintype α]
    (i : Fin N) (H : α → TritWord N → ℤ) (R : TritWord N) :
    coordinateZeta i (fun Q => ∑ A, H A Q) R = ∑ A, coordinateZeta i (H A) R := by
  generalize hd : R i = d
  fin_cases d <;>
    simp [coordinateZeta, zetaDigit, hd, Fin.ext_iff,
      Finset.sum_add_distrib, Finset.mul_sum]

theorem coordinateZeta_kernel {N : ℕ} (s : Finset (Fin N)) (i : Fin N)
    (hi : i ∉ s) (A R : TritWord N) (C : ℤ) :
    coordinateZeta i (fun Q => kernel s Q A * C) R = kernel (insert i s) R A * C := by
  let other : ℤ := ∏ j ∈ (univ : Finset (Fin N)).erase i,
    if j ∈ s then digitChoose (R j) (A j) else if A j = R j then 1 else 0
  have hu (d : Fin 3) : kernel s (Function.update R i d) A =
      (if A i = d then 1 else 0) * other := by
    unfold kernel
    rw [← Finset.mul_prod_erase univ _ (mem_univ i)]
    simp only [hi, ↓reduceIte, Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    simp [Function.update_of_ne (mem_erase.mp hj).1]
  have hv : kernel (insert i s) R A = digitChoose (R i) (A i) * other := by
    unfold kernel
    rw [← Finset.mul_prod_erase univ _ (mem_univ i)]
    simp only [mem_insert_self, ↓reduceIte]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    have hji := (mem_erase.mp hj).1
    simp [hji]
  unfold coordinateZeta
  simp_rw [hu, mul_assoc]
  rw [zeta_delta, hv]
  ring

theorem coordinateZeta_partial {N : ℕ} (s : Finset (Fin N)) (i : Fin N)
    (hi : i ∉ s) (f : TritWord N → ℤ) :
    coordinateZeta i (stageSum s f) = stageSum (insert i s) f := by
  funext R
  unfold stageSum
  rw [coordinateZeta_sum]
  apply Finset.sum_congr rfl
  intro A hA
  exact coordinateZeta_kernel s i hi A R (f A)

theorem runZeta_eq_partial {N : ℕ} (coords : List (Fin N)) (h : coords.Nodup)
    (f : TritWord N → ℤ) : runZeta coords f = stageSum coords.toFinset f := by
  induction coords with
  | nil => simpa [runZeta] using (partial_empty f).symm
  | cons i rest ih =>
      obtain ⟨hi, hn⟩ := List.nodup_cons.mp h
      rw [runZeta, ih hn, List.toFinset_cons]
      exact coordinateZeta_partial rest.toFinset i (by simpa using hi) f

theorem runZeta_eq_binomialZeta {N : ℕ} (coords : List (Fin N))
    (h : coords.Nodup) (hall : coords.toFinset = univ) (f : TritWord N → ℤ) :
    runZeta coords f = binomialZeta f := by
  rw [runZeta_eq_partial coords h, hall, partial_univ]

end ThreeSum.TernaryTransform
