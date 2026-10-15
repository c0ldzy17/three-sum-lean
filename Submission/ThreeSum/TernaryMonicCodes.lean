import Submission.ThreeSum.TernaryCoefficientCodes
import Submission.ThreeSum.TernaryExtensionProductSemantics

/-! The concrete monic code is exactly the low coefficient code plus p^degree. -/

noncomputable section
namespace ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]

def monicVector {d : ℕ} (a : Fin d → ZMod p) : Fin (d+1) → ZMod p :=
  Fin.lastCases 1 a

theorem monicVector_code {d : ℕ} (a : Fin d → ZMod p) :
    coefficientCode (monicVector a)=coefficientCode a+p^d := by
  unfold coefficientCode
  rw [List.ofFn_succ_last]
  simp [monicVector,Nat.ofDigits_append,ZMod.val_one,
    Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt]

theorem monicVector_polynomial {d : ℕ} (a : Fin d → ZMod p) :
    vectorPolynomial (monicVector a)=monicCandidate a := by
  unfold vectorPolynomial monicCandidate
  rw [Fin.sum_univ_castSucc]
  simp [monicVector,vectorPolynomial,monomial_one_right_eq_X_pow,add_comm]

theorem decode_monic_code {d code : ℕ} (hc : code<p^d) :
    coefficientVector (p := p) (d+1) (code+p^d)=monicVector (coefficientVector d code) := by
  have he : coefficientCode (monicVector (coefficientVector (p := p) d code))=code+p^d := by
    rw [monicVector_code,code_coefficientVector hc]
  rw [← he,coefficientVector_code]

theorem arrayPolynomial_as_vector (n : ℕ) (a : ℕ → ℕ) :
    arrayPolynomial (p := p) n a=vectorPolynomial (fun i : Fin n => (a i.val : ZMod p)) := by
  unfold arrayPolynomial vectorPolynomial
  rw [← Fin.sum_univ_eq_sum_range]

theorem actual_monic_polynomial {d code : ℕ} (hc : code<p^d) :
    arrayPolynomial (p := p) (d+1) (fun k => (code+p^d)/p^k%p)=monicOfCode d code := by
  rw [arrayPolynomial_as_vector]
  change vectorPolynomial (coefficientVector (d+1) (code+p^d))=monicOfCode d code
  rw [decode_monic_code hc,monicVector_polynomial]
  rfl

theorem decode_field_code {f : (ZMod p)[X]} (hf : f.Monic) (code : Fin (p^f.natDegree)) :
    coefficients hf ((encodedEquiv hf).symm code)=coefficientVector f.natDegree code.val := by
  have he : encode hf ((encodedEquiv hf).symm code)=code.val :=
    congrArg Fin.val ((encodedEquiv hf).apply_symm_apply code)
  have h := decode_encoded hf ((encodedEquiv hf).symm code)
  rw [he] at h
  exact h.symm

end ThreeSum.TernaryExtensionEncoding
