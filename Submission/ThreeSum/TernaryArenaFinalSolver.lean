import Submission.ThreeSum.TernaryArenaPostCertificate

noncomputable section
namespace ThreeSum.TernaryArenaFinalSolver
open Light TernaryArenaLayout TernaryArenaSourceSetup TernaryArenaPostSelection
open LightOriginalSurvivors LightOriginalSurvivorPair TernaryExtensionEncoding
open TernaryCoverGoodMaps LightTernaryPostSelection TernaryArenaPostCertificate
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {p m F r J : ℕ} [Fact p.Prime]

/-- The closed actual final solver, including histogram construction, original
collision cleanup, real compaction, all signed channels and determinant detection.
No execution callback or semantic source/correctness certificate is an input. -/
theorem meets {lim : Limits} {d M n Hdet K : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (U radix nA aBase bBase cBase q L : ℕ)
    (H : (TernarySignedReduction.Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ) (μ : ℕ→ℤ)
    (G : Guards (r := r) maps τ cap Q (selectedInput I U radix nA H A B C keysB keysC)
      lim (d+1) M n U Hdet I.nB I.nC)
    (R : LightTernaryPreparedPostSelection.Inputs
      (TernaryArenaCleanupLayout.layout I.free I.capacity aBase nA bBase I.nB cBase I.nC q L)
      lim (d+2) U L μ A B C keysB keysC)
    (Meta : TernaryArenaPostMemory.Metadata (r := r) maps τ
      (selectedInput I U radix nA H A B C keysB keysC) μ)
    (hcover : ∀a b : ZMod p, ∃i, TernaryCoverFrequency.Covers m p cap τ (maps i) (a,b))
    (hA : ∀i<nA,|A i|≤(U : ℤ)) (hB : ∀j<I.nB,|B j|≤(U : ℤ))
    (hC : ∀j<I.nC,|C j|≤(U : ℤ))
    (hb : 1<radix) (hp : 2*radix<p) (hcap : 4*U<radix^J)
    (hkB : ∀j<I.nB,keysB j=coefficientCode (TernaryNativeRequesterCoverage.sourceLeft H U radix (B j)))
    (hkC : ∀j<I.nC,keysC j=coefficientCode (TernaryNativeRequesterCoverage.sourceRight H U radix (C j)))
    (hsupport : 2*p^K≤Hdet)
    (hzero : TernaryNativeTensorScore.pairedPotential
      (setup (r := r) maps τ cap Q (TernaryArenaNativeComplete.input I U radix nA H A B C)) K J
      (fun j i => TernarySignedLayout.feature (TernarySignedReduction.leftRaw U radix J (B j)) i)
      (fun j i => TernarySignedLayout.feature (TernarySignedReduction.rightRaw U radix J (C j)) i)=0) :
    let I' := selectedInput I U radix nA H A B C keysB keysC
    let S := setup (r := r) maps τ cap Q I'
    let c := TernaryArenaCleanupLayout.layout I.free I.capacity aBase nA bBase I.nB cBase I.nC q L
    Meets lim (LightTernaryPreparedPostSelection.program S Hdet)
      (LightTernaryPreparedPostSelection.libraries S Hdet).length d
      (LightTernaryPreparedPostSelection.args S c (addr I.free I.capacity 26) (addr I.free I.capacity 25)) μ
      (LightTernaryPreparedPostSelection.time S Hdet c keysB keysC)
      (fun ret ν => ret=(if ∃i<nA,∃j<I.nB,∃k<I.nC,C k=A i+B j then 1 else 0 : ℤ) ∧
        Kept μ ν (addr I.free I.capacity 6)) := by
  let I' := selectedInput I U radix nA H A B C keysB keysC
  let S := setup (r := r) maps τ cap Q I'
  let c := TernaryArenaCleanupLayout.layout I.free I.capacity aBase nA bBase I.nB cBase I.nC q L
  apply LightTernaryPreparedPostSelection.meets S c μ A B C keysB keysC
    (TernaryArenaNativeComplete.originalPosition (r := r) maps τ I') R
  intro ν hPowers hcB hcC hkeep hRest
  have hL : L+1≤I.capacity := by
    have hh := R.powerBeforeHist
    dsimp [TernaryArenaCleanupLayout.layout] at hh
    unfold addr at hh
    omega
  have hq : q≤I.capacity := by
    have hh := R.histBeforeHist
    dsimp [TernaryArenaCleanupLayout.layout] at hh
    unfold addr at hh
    omega
  have hlo : addr I.free I.capacity 9≤I'.prefixFree := by
    have hh := G.bankLo
    change addr I.free I.capacity 11≤I.prefixFree at hh
    change addr I.free I.capacity 9≤I.prefixFree
    unfold addr at *
    omega
  have Mν := Meta.after_preparation hL hq hlo hRest
  exact TernaryArenaPostCertificate.certificate maps τ cap Q I U radix nA aBase bBase cBase q L
    H A B C keysB keysC ν G Mν hcover hA hB hC hb hp hcap hkB hkC hsupport hzero

end ThreeSum.TernaryArenaFinalSolver
