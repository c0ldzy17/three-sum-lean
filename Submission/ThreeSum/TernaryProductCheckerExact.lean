import Submission.ThreeSum.TernaryMonicCodes
import Submission.ThreeSum.LightPolynomialQuotientCheck

noncomputable section
namespace ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

theorem arrayPolynomial_degree_lt (n : ℕ) (a : ℕ → ℕ) :
    (arrayPolynomial (p := p) n a).degree < n := by
  rw [degree_lt_iff_coeff_zero]
  intro k hk
  simp [arrayPolynomial_coeff,show ¬k<n by omega]

theorem arrayPolynomial_product_zero (n m k : ℕ) (a b : ℕ → ℕ)
    (hk : n+m-1≤k) :
    (arrayPolynomial (p := p) n a*arrayPolynomial m b).coeff k=0 := by
  rw [arrayPolynomial_product_coeff]
  unfold LightPolynomialCoefficient.coefficient LightPolynomialCoefficient.rawCoefficient
  have hz : (∑ i ∈ range n, LightPolynomialCoefficient.term a b m k i)=0 := by
    apply sum_eq_zero
    intro i hi
    have hin := mem_range.mp hi
    unfold LightPolynomialCoefficient.term
    split_ifs with h
    · omega
    · rfl
  rw [hz]
  simp

theorem product_valid_iff_polynomial (a b expected : ℕ → ℕ) (n m len : ℕ)
    (hlen : n+m-1≤len) (hb : ∀ k<len, expected k<p) :
    LightPolynomialProductCheck.Valid p a b expected n m len ↔
      arrayPolynomial n a*arrayPolynomial m b=arrayPolynomial (p := p) len expected := by
  constructor
  · intro h
    ext k
    by_cases hk : k<len
    · rw [arrayPolynomial_coeff,if_pos hk]
      exact product_valid_coefficients a b expected n m len h k hk
    · rw [arrayPolynomial_product_zero n m k a b (by omega),arrayPolynomial_coeff,if_neg hk]
  · intro h k hk
    have hc := congrArg (fun f : (ZMod p)[X] => f.coeff k) h
    rw [arrayPolynomial_product_coeff,arrayPolynomial_coeff,if_pos hk] at hc
    have hv := congrArg ZMod.val hc
    simpa [LightPolynomialCoefficient.coefficient,ZMod.val_natCast,
      Nat.mod_eq_of_lt (hb k hk)] using hv.symm

theorem arrayPolynomial_extend (n len : ℕ) (a : ℕ → ℕ) (hn : n≤len)
    (hz : ∀ k, n≤k → a k=0) :
    arrayPolynomial (p := p) len a=arrayPolynomial n a := by
  ext k
  simp only [arrayPolynomial_coeff]
  by_cases hk : k<n
  · simp [hk,show k<len by omega]
  · by_cases hkl : k<len
    · simp [hk,hkl,hz k (by omega)]
    · simp [hk,hkl]

theorem arrayPolynomial_expected (d : ℕ) (h f r : ℕ → ℕ)
    (hr : ∀ k, d≤k → r k=0) :
    arrayPolynomial (p := p) (2*d) (LightPolynomialQuotientCheck.expected p d h f r)=
      arrayPolynomial d h*arrayPolynomial (d+1) f+arrayPolynomial d r := by
  ext k
  by_cases hk : k<2*d
  · rw [arrayPolynomial_coeff,if_pos hk,coeff_add,arrayPolynomial_product_coeff,
      arrayPolynomial_coeff]
    simp only [LightPolynomialQuotientCheck.expected,ZMod.natCast_mod,Nat.cast_add]
    by_cases hkd : k<d
    · simp [hkd]
    · simp [hkd,hr k (by omega)]
  · rw [arrayPolynomial_coeff,if_neg hk,coeff_add,
      arrayPolynomial_product_zero d (d+1) k h f (by omega),arrayPolynomial_coeff,
      if_neg (by omega : ¬k<d)]
    simp

end ThreeSum.TernaryExtensionEncoding
