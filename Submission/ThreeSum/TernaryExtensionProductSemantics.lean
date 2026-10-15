import Submission.ThreeSum.TernaryExtensionDecoded
import Submission.ThreeSum.LightPolynomialProductCheck

/-! The physical modular coefficient loop computes genuine Fp polynomial products. -/

noncomputable section
namespace ThreeSum.TernaryExtensionEncoding

open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

def arrayPolynomial (n : ℕ) (a : ℕ → ℕ) : (ZMod p)[X] :=
  ∑ i ∈ range n, monomial i (a i : ZMod p)

theorem arrayPolynomial_coeff (n k : ℕ) (a : ℕ → ℕ) :
    (arrayPolynomial (p := p) n a).coeff k=if k<n then (a k : ZMod p) else 0 := by
  simp [arrayPolynomial,finsetSum_coeff,coeff_monomial]

theorem arrayPolynomial_product_coeff (n m k : ℕ) (a b : ℕ → ℕ) :
    (arrayPolynomial (p := p) n a*arrayPolynomial m b).coeff k=
      (LightPolynomialCoefficient.coefficient p a b n m k : ZMod p) := by
  simp only [arrayPolynomial,Finset.sum_mul,Finset.mul_sum,finsetSum_coeff,
    monomial_mul_monomial,coeff_monomial]
  simp only [LightPolynomialCoefficient.coefficient,ZMod.natCast_mod,
    LightPolynomialCoefficient.rawCoefficient,Nat.cast_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro i hi
  simp only [LightPolynomialCoefficient.term,Nat.cast_ite,Nat.cast_mul,Nat.cast_zero]
  by_cases h : i≤k ∧ k-i<m
  · rw [if_pos h]
    rw [sum_eq_single (k-i)]
    · simp [show i+(k-i)=k by omega]
    · intro j hj hne
      simp [show i+j≠k by omega]
    · intro hn
      exact False.elim (hn (mem_range.mpr h.2))
  · rw [if_neg h]
    apply sum_eq_zero
    intro j hj
    have hjm := mem_range.mp hj
    simp [show i+j≠k by omega]

theorem arrayPolynomial_eq_vector {d : ℕ} (a : Fin d → ZMod p) :
    arrayPolynomial d (fun i => if h : i<d then (a ⟨i,h⟩).val else 0)=
      vectorPolynomial a := by
  unfold arrayPolynomial vectorPolynomial
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i hi
  simp [i.isLt]

theorem product_valid_coefficients (a b expected : ℕ → ℕ) (n m len : ℕ)
    (h : LightPolynomialProductCheck.Valid p a b expected n m len) :
    ∀ k<len, (arrayPolynomial (p := p) n a*arrayPolynomial m b).coeff k=
      (expected k : ZMod p) := by
  intro k hk
  rw [arrayPolynomial_product_coeff]
  have hh := h k hk
  change expected k=LightPolynomialCoefficient.coefficient p a b n m k at hh
  exact congrArg (fun z : ℕ => (z : ZMod p)) hh.symm

end ThreeSum.TernaryExtensionEncoding
