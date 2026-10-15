import Submission.ThreeSum.TernaryExtensionCheckerSemantics
import Submission.ThreeSum.LightExtensionQuotientSearch
import Submission.ThreeSum.LightExtensionFactorSearch

noncomputable section
namespace ThreeSum.TernaryExtensionEncoding
open Polynomial
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

theorem quotient_code_exists {f : (ZMod p)[X]} (hf : f.Monic)
    (hd : 0<f.natDegree) {c : ℕ} (hc : c<p^f.natDegree)
    (hm : monicOfCode (p := p) f.natDegree c=f) (x y : ℕ) :
    ∃ h<p^f.natDegree, ∃ r<p^f.natDegree,
      LightPolynomialProductCheck.Valid p (codeDigits (p := p) x) (codeDigits (p := p) y)
        (LightPolynomialQuotientCheck.expected p f.natDegree (codeDigits (p := p) h)
          (codeDigits (p := p) (c+p^f.natDegree)) (codeDigits (p := p) r))
        f.natDegree f.natDegree (2*f.natDegree) := by
  obtain ⟨h,r,hr⟩ := remainderRelation_exists hf hd
    (coefficientVector f.natDegree x) (coefficientVector f.natDegree y)
  refine ⟨coefficientCode h,coefficientCode_lt h,coefficientCode r,coefficientCode_lt r,?_⟩
  apply (quotient_check_iff hc (coefficientCode_lt r) _ _).mpr
  rw [arrayPolynomial_digits,arrayPolynomial_digits,coefficientVector_code,
    coefficientVector_code,hm]
  exact hr

theorem quotient_code_correct {f : (ZMod p)[X]} (hf : f.Monic)
    {c x y h r : ℕ} (hc : c<p^f.natDegree) (hx : x<p^f.natDegree)
    (hy : y<p^f.natDegree) (hr : r<p^f.natDegree)
    (hm : monicOfCode (p := p) f.natDegree c=f)
    (hg : LightPolynomialProductCheck.Valid p (codeDigits (p := p) x) (codeDigits (p := p) y)
      (LightPolynomialQuotientCheck.expected p f.natDegree (codeDigits (p := p) h)
        (codeDigits (p := p) (c+p^f.natDegree)) (codeDigits (p := p) r))
      f.natDegree f.natDegree (2*f.natDegree)) :
    encode hf ((encodedEquiv hf).symm ⟨x,hx⟩*(encodedEquiv hf).symm ⟨y,hy⟩)=r := by
  have hg' := (quotient_check_iff hc hr _ _).mp hg
  rw [arrayPolynomial_digits,arrayPolynomial_digits,hm] at hg'
  have hrel : remainderRelation
      (coefficients hf ((encodedEquiv hf).symm ⟨x,hx⟩))
      (coefficients hf ((encodedEquiv hf).symm ⟨y,hy⟩))
      (coefficientVector f.natDegree h) (coefficientVector f.natDegree r) := by
    rw [decode_field_code,decode_field_code]
    exact hg'
  have hh := quotient_product_of_relation hf _ _ _ _ hrel
  have he := congrArg (coefficientCode (p := p)) hh
  rw [code_coefficientVector hr] at he
  exact he

theorem factor_nohit_iff {d e c : ℕ} (hd : 0<d) (he : 0<e) (hed : e<d)
    (hc : c<p^d) :
    (∀ u<p^e, ∀ v<p^(d-e),
      ¬LightPolynomialProductCheck.Valid p (codeDigits (p := p) (u+p^e))
        (codeDigits (p := p) (v+p^(d-e))) (codeDigits (p := p) (c+p^d))
        (e+1) (d-e+1) (2*d)) ↔
    ∀ (a : Fin e → ZMod p) (b : Fin (d-e) → ZMod p),
      monicCandidate a*monicCandidate b≠monicOfCode d c := by
  constructor
  · intro h a b
    have hh := h (coefficientCode a) (coefficientCode_lt a)
      (coefficientCode b) (coefficientCode_lt b)
    intro hab
    apply hh
    apply (factor_check_iff hd hed hc (coefficientCode_lt a) (coefficientCode_lt b)).mpr
    simpa only [monicOfCode,coefficientVector_code] using hab
  · intro h u hu v hv hg
    exact h _ _ ((factor_check_iff hd hed hc hu hv).mp hg)

end ThreeSum.TernaryExtensionEncoding
