import Submission.ThreeSum.TernaryProductCheckerExact
import Submission.ThreeSum.LightExtensionQuotientPredicate
import Submission.ThreeSum.LightExtensionFactorPredicate

noncomputable section
namespace ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

def codeDigits (code k : ℕ) : ℕ := code/p^k%p

theorem codeDigits_lt (code k : ℕ) : codeDigits (p := p) code k<p :=
  Nat.mod_lt _ (Fact.out : p.Prime).pos

theorem arrayPolynomial_digits (d code : ℕ) :
    arrayPolynomial (p := p) d (codeDigits (p := p) code)=vectorPolynomial (coefficientVector d code) := by
  rw [arrayPolynomial_as_vector]
  rfl

theorem monic_code_lt {d code : ℕ} (hc : code<p^d) : code+p^d<p^(d+1) := by
  rw [pow_succ]
  have hp := (Fact.out : p.Prime).one_lt
  have hpos := pow_pos (Fact.out : p.Prime).pos d
  nlinarith

theorem actual_monic_polynomial_padded {d code : ℕ} (hd : 0<d) (hc : code<p^d) :
    arrayPolynomial (p := p) (2*d) (codeDigits (p := p) (code+p^d))=monicOfCode d code := by
  rw [arrayPolynomial_extend (d+1) (2*d) _ (by omega)]
  · exact actual_monic_polynomial hc
  · intro k hk
    exact code_high_digit_zero (monic_code_lt hc) hk

theorem quotient_check_iff {d c h r : ℕ} (hc : c<p^d) (hr : r<p^d)
    (x y : ℕ → ℕ) :
    LightPolynomialProductCheck.Valid p x y
      (LightPolynomialQuotientCheck.expected p d (codeDigits (p := p) h)
        (codeDigits (p := p) (c+p^d)) (codeDigits (p := p) r)) d d (2*d) ↔
    arrayPolynomial d x*arrayPolynomial (p := p) d y=
      vectorPolynomial (coefficientVector d h)*monicOfCode d c+
        vectorPolynomial (coefficientVector d r) := by
  have hb : ∀ k<2*d, LightPolynomialQuotientCheck.expected p d (codeDigits (p := p) h)
      (codeDigits (p := p) (c+p^d)) (codeDigits (p := p) r) k<p := by
    intro k hk
    exact Nat.mod_lt _ (Fact.out : p.Prime).pos
  rw [product_valid_iff_polynomial x y _ d d (2*d) (by omega) hb]
  have hz : ∀ k, d≤k → codeDigits (p := p) r k=0 := fun k hk => code_high_digit_zero hr hk
  have hm : arrayPolynomial (p := p) (d+1) (codeDigits (p := p) (c+p^d))=monicOfCode d c :=
    actual_monic_polynomial hc
  rw [arrayPolynomial_expected (p := p) d (codeDigits (p := p) h) (codeDigits (p := p) (c+p^d)) (codeDigits (p := p) r) hz,
    arrayPolynomial_digits,hm,arrayPolynomial_digits]

theorem factor_check_iff {d e c u v : ℕ} (hd : 0<d) (he : e<d)
    (hc : c<p^d) (hu : u<p^e) (hv : v<p^(d-e)) :
    LightPolynomialProductCheck.Valid p (codeDigits (p := p) (u+p^e))
      (codeDigits (p := p) (v+p^(d-e))) (codeDigits (p := p) (c+p^d)) (e+1) (d-e+1) (2*d) ↔
    monicOfCode (p := p) e u*monicOfCode (d-e) v=monicOfCode d c := by
  have hmu : arrayPolynomial (p := p) (e+1) (codeDigits (p := p) (u+p^e))=monicOfCode e u :=
    actual_monic_polynomial hu
  have hmv : arrayPolynomial (p := p) (d-e+1) (codeDigits (p := p) (v+p^(d-e)))=monicOfCode (d-e) v :=
    actual_monic_polynomial hv
  rw [product_valid_iff_polynomial _ _ _ (e+1) (d-e+1) (2*d) (by omega)
    (fun k hk => codeDigits_lt _ _),hmu,hmv,actual_monic_polynomial_padded hd hc]

theorem irreducible_code_iff {d c : ℕ} (hd : 0<d) :
    Irreducible (monicOfCode (p := p) d c) ↔
    ∀ e, 0<e → e<d → ∀ u<p^e, ∀ v<p^(d-e),
      monicOfCode (p := p) e u*monicOfCode (d-e) v≠monicOfCode d c := by
  rw [irreducible_iff_no_monic_factors (show (monicOfCode (p := p) d c).Monic from monicCandidate_monic _)
    (show (monicOfCode (p := p) d c).natDegree=d from monicCandidate_degree _) hd]
  constructor
  · intro h e he hed u hu v hv
    exact h e he hed _ _
  · intro h e he hed a b
    have hh := h e he hed (coefficientCode a) (coefficientCode_lt a)
      (coefficientCode b) (coefficientCode_lt b)
    simpa only [monicOfCode,coefficientVector_code] using hh

end ThreeSum.TernaryExtensionEncoding
