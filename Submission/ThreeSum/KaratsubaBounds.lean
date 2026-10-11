import Submission.ThreeSum.Karatsuba
import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Coefficient and intermediate-value bounds for the array realization -/

namespace ThreeSum.Karatsuba

open Polynomial
open scoped BigOperators

@[simp] theorem asPolynomial_coeff (as : List ℤ) (j : ℕ) :
    (asPolynomial as).coeff j = as.getD j 0 := by
  induction as generalizing j with
  | nil => simp [asPolynomial]
  | cons a as ih =>
    cases j with
    | zero => simp [asPolynomial]
    | succ j =>
      rw [asPolynomial, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_mul, ih]
      simp

@[simp] theorem plus_getD (as bs : List ℤ) (j : ℕ) :
    (plus as bs).getD j 0 = as.getD j 0 + bs.getD j 0 := by
  simpa only [asPolynomial_coeff, Polynomial.coeff_add] using
    congrArg (fun p : Polynomial ℤ => p.coeff j) (asPolynomial_plus as bs)

@[simp] theorem minus_getD (as bs : List ℤ) (j : ℕ) :
    (minus as bs).getD j 0 = as.getD j 0 - bs.getD j 0 := by
  simpa only [asPolynomial_coeff, Polynomial.coeff_sub] using
    congrArg (fun p : Polynomial ℤ => p.coeff j) (asPolynomial_minus as bs)

def CoeffBound (as : List ℤ) (U : ℤ) : Prop := ∀ j, |as.getD j 0| ≤ U

theorem coeffBound_nonneg {as : List ℤ} {U : ℤ} (h : CoeffBound as U) : 0 ≤ U :=
  (abs_nonneg _).trans (h 0)

theorem CoeffBound.of_mem {as : List ℤ} {U : ℤ} (hU : 0 ≤ U)
    (hm : ∀ x ∈ as, |x| ≤ U) : CoeffBound as U := by
  intro j
  by_cases hj : j < as.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact hm _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega), abs_zero]
    exact hU

theorem CoeffBound.mem {as : List ℤ} {U x : ℤ} (h : CoeffBound as U)
    (hx : x ∈ as) : |x| ≤ U := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  simpa only [List.getD_eq_getElem _ _ hj] using h j

theorem CoeffBound.take {as : List ℤ} {U : ℤ} (h : CoeffBound as U) (n : ℕ) :
    CoeffBound (as.take n) U :=
  .of_mem (coeffBound_nonneg h) (fun x hx => h.mem (List.mem_of_mem_take hx))

theorem CoeffBound.drop {as : List ℤ} {U : ℤ} (h : CoeffBound as U) (n : ℕ) :
    CoeffBound (as.drop n) U :=
  .of_mem (coeffBound_nonneg h) (fun x hx => h.mem (List.mem_of_mem_drop hx))

theorem CoeffBound.plus {as bs : List ℤ} {U V : ℤ}
    (ha : CoeffBound as U) (hb : CoeffBound bs V) : CoeffBound (plus as bs) (U + V) := by
  intro j
  rw [plus_getD]
  exact (abs_add_le _ _).trans (add_le_add (ha j) (hb j))

theorem CoeffBound.minus {as bs : List ℤ} {U V : ℤ}
    (ha : CoeffBound as U) (hb : CoeffBound bs V) : CoeffBound (minus as bs) (U + V) := by
  intro j
  rw [minus_getD]
  exact (abs_sub _ _).trans (add_le_add (ha j) (hb j))

theorem product_coeff_zero {as bs : List ℤ} {n j : ℕ}
    (ha : as.length ≤ n) (hb : bs.length ≤ n) (hj : 2 * n ≤ j) :
    (asPolynomial as * asPolynomial bs).coeff j = 0 := by
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have hp' := Finset.mem_antidiagonal.mp hp
  by_cases hpa : n ≤ p.1
  · rw [asPolynomial_coeff, List.getD_eq_default _ _ (ha.trans hpa), zero_mul]
  · have hpb : n ≤ p.2 := by omega
    rw [asPolynomial_coeff bs, List.getD_eq_default _ _ (hb.trans hpb), mul_zero]

/-- All true product coefficients have a polynomial value bound, including
the implicit zeros outside the stored output. -/
theorem product_coeff_bound {as bs : List ℤ} {n : ℕ} {U : ℤ}
    (ha : as.length ≤ n) (hb : bs.length ≤ n)
    (hA : CoeffBound as U) (hB : CoeffBound bs U) (j : ℕ) :
    |(asPolynomial as * asPolynomial bs).coeff j| ≤ 2 * (n : ℤ) * U ^ 2 := by
  have hU : 0 ≤ U := coeffBound_nonneg hA
  by_cases hj : 2 * n ≤ j
  · rw [product_coeff_zero ha hb hj, abs_zero]
    positivity
  · have hj' : j + 1 ≤ 2 * n := by omega
    rw [Polynomial.coeff_mul]
    calc
      _ ≤ ∑ p ∈ Finset.antidiagonal j,
          |(asPolynomial as).coeff p.1 * (asPolynomial bs).coeff p.2| :=
        Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑ _p ∈ Finset.antidiagonal j, U ^ 2 := by
        apply Finset.sum_le_sum
        intro p hp
        rw [abs_mul, asPolynomial_coeff, asPolynomial_coeff, pow_two]
        exact mul_le_mul (hA p.1) (hB p.2) (abs_nonneg _) hU
      _ = (j + 1 : ℕ) * U ^ 2 := by simp
      _ ≤ 2 * (n : ℤ) * U ^ 2 := by
        have hjR : (j + 1 : ℕ) ≤ (2 * (n : ℤ)) := by exact_mod_cast hj'
        exact mul_le_mul_of_nonneg_right hjR (sq_nonneg U)

theorem multiply_coeffBound {as bs : List ℤ} {k : ℕ} {U : ℤ}
    (ha : as.length ≤ 2 ^ k) (hb : bs.length ≤ 2 ^ k)
    (hA : CoeffBound as U) (hB : CoeffBound bs U) :
    CoeffBound (multiply k as bs) (2 * (2 ^ k : ℕ) * U ^ 2) := by
  intro j
  rw [← asPolynomial_coeff, multiply_correct k as bs ha hb]
  exact product_coeff_bound ha hb hA hB j

end ThreeSum.Karatsuba
