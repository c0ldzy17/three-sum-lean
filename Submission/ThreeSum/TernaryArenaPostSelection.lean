import Submission.ThreeSum.TernaryArenaNativeComplete
import Submission.ThreeSum.TernaryArenaCompactSupport
import Submission.ThreeSum.TernarySignedFeatureHash
import Submission.ThreeSum.TernaryArenaMomentResources
import Submission.ThreeSum.TernaryArenaSourceCountSeed
import Submission.ThreeSum.LightTernaryPreparedPostSelection

/-! The actual compact source model and final certificate of the selected
canonical row map. All compact positions come from executed singleton cleanup. -/
noncomputable section
namespace ThreeSum.TernaryArenaPostSelection
open Light LightOriginalSurvivors LightTernaryPostSelection
open TernaryArenaSourceSetup TernaryCoverGoodMaps TernarySignedReduction
open TernaryExtensionEncoding TernaryArenaLayout
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {p m F r J : ℕ} [Fact p.Prime]

def compactInput (I : Input) (keysB keysC : ℕ→ℕ) : Input :=
  { I with nB:=(indices keysB I.nB).length, nC:=(indices keysC I.nC).length }

def selectedInput (I : Input) (U radix nA : ℕ)
    (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ) : Input :=
  TernaryArenaNativeComplete.input (compactInput I keysB keysC) U radix nA H A
    (compact keysB B I.nB) (compact keysC C I.nC)

theorem selected_restrict (I : Input) (U radix nA : ℕ)
    (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ) :
    selectedInput I U radix nA H A B C keysB keysC =
      TernaryArenaPairRestriction.restrict
        (TernaryArenaNativeComplete.input I U radix nA H A B C)
        (indices keysB I.nB).length (indices keysC I.nC).length
        (index keysB I.nB) (index keysC I.nC) := by
  rfl

theorem native_complete (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (U radix nA : ℕ)
    (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ)
    (hcover : ∀a b : ZMod p, ∃i, TernaryCoverFrequency.Covers m p cap τ (maps i) (a,b))
    (hA : ∀i<nA, |A i|≤(U : ℤ)) (hB : ∀j<I.nB, |B j|≤(U : ℤ))
    (hC : ∀k<I.nC, |C k|≤(U : ℤ)) (hcap : 4*U<radix^J) :
    let I' := selectedInput I U radix nA H A B C keysB keysC
    let S := setup (r := r) maps τ cap Q I'
    (∃i<S.front.count, ∃pair : TernaryNativePairMoments.Pair S i,
      TernaryNativePairMoments.mode (compact keysB B I.nB) (compact keysC C I.nC) pair=
        A (TernaryArenaNativeComplete.originalPosition (r := r) maps τ I' i)) ↔
      ∃i<nA, ∃j<(indices keysB I.nB).length, ∃k<(indices keysC I.nC).length,
        compact keysC C I.nC k=A i+compact keysB B I.nB j := by
  exact TernaryArenaNativeComplete.complete maps τ cap Q (compactInput I keysB keysC)
    U radix nA H A (compact keysB B I.nB) (compact keysC C I.nC) hcover hA
    (TernaryArenaReporterBounds.compact_abs keysB B I.nB U hB)
    (TernaryArenaReporterBounds.compact_abs keysC C I.nC U hC) hcap

theorem support (maps : Fin F→Weight m p) (τ cap K U radix nA : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input)
    (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ)
    (hb : 1<radix) (hp : 2*radix<p)
    (hB : ∀j<I.nB, |B j|≤(U : ℤ)) (hC : ∀k<I.nC, |C k|≤(U : ℤ))
    (hcap : 4*U<radix^J)
    (hkB : ∀j<I.nB, keysB j=coefficientCode (TernaryNativeRequesterCoverage.sourceLeft H U radix (B j)))
    (hkC : ∀j<I.nC, keysC j=coefficientCode (TernaryNativeRequesterCoverage.sourceRight H U radix (C j)))
    (hzero : TernaryNativeTensorScore.pairedPotential
      (setup (r := r) maps τ cap Q (TernaryArenaNativeComplete.input I U radix nA H A B C)) K J
      (fun j i => TernarySignedLayout.feature (leftRaw U radix J (B j)) i)
      (fun j i => TernarySignedLayout.feature (rightRaw U radix J (C j)) i)=0) :
    let S := setup (r := r) maps τ cap Q (selectedInput I U radix nA H A B C keysB keysC)
    ∀i<S.front.count,
      (TernaryPairedSupport.physicalSupport
        (TernaryNativePairMoments.mode (compact keysB B I.nB) (compact keysC C I.nC)
          (S := S) (i := i))).card≤2*p^K := by
  let full := TernaryArenaNativeComplete.input I U radix nA H A B C
  have hs := TernaryArenaCompactSupport.support maps τ cap Q full
    (fun j i => TernarySignedLayout.feature (leftRaw U radix J (B j)) i)
    (fun j i => TernarySignedLayout.feature (rightRaw U radix J (C j)) i) B C
    (TernarySignedFeatureHash.hash H)
    (fun t => H (TernaryNativeRequesterCoverage.field
      (requesterRaw U radix J (A (TernaryNativeRequesterCoverage.position J t))
        (TernaryCarryCode.carryFromCode J (t%(2^J))))))
    keysB keysC ⟨J,by omega⟩ ⟨J+1,by omega⟩
    (by intro j hj; simp only [full,TernaryArenaNativeComplete.input,TernarySignedFeatureHash.left_hash])
    (by intro j hj; simp only [full,TernaryArenaNativeComplete.input,TernarySignedFeatureHash.right_hash])
    (by intro j hj; rfl)
    (by intro j hj; rw [TernarySignedFeatureHash.left_hash]; exact hkB j hj)
    (by intro j hj; rw [TernarySignedFeatureHash.right_hash]; exact hkC j hj)
    (by intro j hj; exact TernarySignedFeatureHash.left_tags U radix J (B j))
    (by intro j hj; exact TernarySignedFeatureHash.right_tags U radix J (C j))
    (by intro u hu v hv u' hu' v' hv' he
        exact TernarySignedFeatureHash.physical_sound hb hp (hB u hu) (hC v hv)
          (hB u' hu') (hC v' hv') hcap he)
    hzero
  dsimp only [selectedInput,compactInput,full,TernaryArenaNativeComplete.input,
    TernaryArenaPairRestriction.restrict,LightTernaryPostSelection.compact] at hs ⊢
  exact hs

theorem positions (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (U radix nA : ℕ)
    (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ) :
    let I' := selectedInput I U radix nA H A B C keysB keysC
    ∀i<(setup (r := r) maps τ cap Q I').front.count,
      TernaryArenaNativeComplete.originalPosition (r := r) maps τ I' i<nA := by
  dsimp only
  intro i hi
  apply TernaryArenaQueryModel.position_lt maps τ _ _ _ nA ?_ ⟨i,hi⟩
  intro t ht
  exact TernaryNativeRequesterCoverage.position_lt ht

end ThreeSum.TernaryArenaPostSelection
