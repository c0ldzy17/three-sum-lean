import Submission.ThreeSum.LightExtensionMultiplyTable
import Submission.ThreeSum.TernaryExtensionSeedSemantics

noncomputable section
namespace ThreeSum.LightExtensionFieldMultiply
open Light TernaryExtensionEncoding
set_option maxHeartbeats 2000000
noncomputable local instance (Q : Prop) : Decidable Q := Classical.propDecidable Q
variable {p : ℕ} [Fact p.Prime] {f : Polynomial (ZMod p)}

theorem actual_quotient_spec (C : LightExtensionQuotientPredicate.Layout)
    (hCp : C.p=p) (hCd : C.dim=f.natDegree) (hf : f.Monic) (hd : 0 < f.natDegree)
    {c : ℕ} (hc : c < p^f.natDegree) (hm : monicOfCode (p := p) f.natDegree c=f) :
    ∀ a < p^f.natDegree, ∀ b < p^f.natDegree,
      let q := p^f.natDegree
      let z := LightPairSearch.first (LightPairSearch.goodCode q
        (LightExtensionQuotientSearch.good C (LightExtensionQuotientPredicate.digits C.p a)
          (LightExtensionQuotientPredicate.digits C.p b)
          (codeDigits (p := p) (c+p^f.natDegree)))) (q*q)
      0 < z ∧ z ≤ q*q ∧ (z-1)%q=encodedMul hf a b := by
  intro a ha b hb
  have hs := first_quotient_code hf hd hc ha hb hm
  dsimp only
  have he : LightExtensionQuotientSearch.good C (LightExtensionQuotientPredicate.digits C.p a)
      (LightExtensionQuotientPredicate.digits C.p b) (codeDigits (p := p) (c+p^f.natDegree))=
      quotientGood (p := p) f.natDegree c a b := by
    funext u v
    unfold LightExtensionQuotientSearch.good quotientGood
    simp only [hCp,hCd,
      LightExtensionQuotientPredicate.digits,LightCoefficientDecode.digit,codeDigits]
    rfl
  rw [he]
  exact ⟨hs.1,LightPairSearch.first_le _ _,hs.2⟩

end ThreeSum.LightExtensionFieldMultiply
