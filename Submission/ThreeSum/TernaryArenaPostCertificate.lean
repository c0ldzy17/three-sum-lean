import Submission.ThreeSum.TernaryArenaPostResources

noncomputable section
namespace ThreeSum.TernaryArenaPostCertificate
open Light TernaryArenaLayout TernaryArenaSourceSetup TernaryArenaPostSelection
open LightOriginalSurvivors LightOriginalSurvivorPair TernaryExtensionEncoding
open TernaryCoverGoodMaps LightTernaryPostSelection
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {p m F r J : ℕ} [Fact p.Prime]

/-- Concrete scalar guards for final reporting. Every semantic fact (source
meaning, completeness, physical support, moments) is derived by `certificate`. -/
structure Guards (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (lim : Limits)
    (d M n U Hdet nB nC : ℕ) : Prop where
  hM : 1<M
  hr : r≤Nat.clog M (n^2)
  hF : 1<F
  hN : 0<N m r
  hnB : nB≤n
  hnC : nC≤n
  hw : (lim.space : ℤ)≤lim.word
  hd : d+5<lim.depth
  hend : finish I.free I.capacity≤lim.space
  counts : nB+3*nC+1≤I.capacity
  Ccount : nC+1≤I.capacity
  bankLo : addr I.free I.capacity 11≤I.prefixFree
  bankHi : I.prefixFree+nb m r≤addr I.free I.capacity 16
  powersHi : I.prefixFree+4^(N m r)+(2*N m r+1)≤addr I.free I.capacity 16
  records : 3*(entries (r := r) maps τ I).length≤I.capacity
  matrix : (2*Hdet+1)*(entries (r := r) maps τ I).length≤I.capacity
  terms : 2*Hdet+1≤I.capacity
  localPositive : ∀right,0<(TernaryNativeCompleteFrontend.localRecords maps cap right).length
  geometry : ∀right,TernaryArenaSourceLayout.Geometry (source (r := r) maps cap I right) lim.space
  controls : ∀right,TernaryArenaSourceControls.Controls (r := r) maps cap I right lim (d+6)
  countCapacity : TernaryArenaCountReady.Capacity (lim := lim) (d := d+6) (r := r) maps τ cap I
  weight : TernaryMomentWeightBounds.leftBound U (2*Hdet)≤I.weightCap
  channel : ((TernaryArenaMomentResources.channelNeed maps cap M Hdet n U).word : ℤ)≤lim.word
  detector : ((TernaryArenaMomentResources.detectorNeed maps cap M Hdet n U).word : ℤ)≤lim.word
  args : ∀z∈LightTernaryMomentChannelFactory.args (setup (r := r) maps τ cap Q I)
    (addr I.free I.capacity 10) (addr I.free I.capacity 16+nB+1+2*nC)
    (addr I.free I.capacity 25), |z|≤lim.word

theorem certificate {lim : Limits} {d M n Hdet K : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (U radix nA aBase bBase cBase q L : ℕ)
    (H : (TernarySignedReduction.Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ) (μ : ℕ→ℤ)
    (G : Guards (r := r) maps τ cap Q (selectedInput I U radix nA H A B C keysB keysC)
      lim d M n U Hdet I.nB I.nC)
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
    Certificate (setup (r := r) maps τ cap Q I')
      (TernaryArenaCleanupLayout.layout I.free I.capacity aBase nA bBase I.nB cBase I.nC q L)
      lim d Hdet (r*alphaRank m) (r*alphaRank m) U
      (TernaryMomentChannelResources.scoreBound (TernaryArenaPairMass.envelope maps cap M n) U (2*Hdet))
      (TernaryMomentDetectorResources.input (TernaryArenaPairMass.envelope maps cap M n) U Hdet)
      (addr I.free I.capacity 26) (addr I.free I.capacity 25)
      μ A B C keysB keysC (TernaryArenaNativeComplete.originalPosition (r := r) maps τ I') := by
  let I' := selectedInput I U radix nA H A B C keysB keysC
  let S := setup (r := r) maps τ cap Q I'
  let c := TernaryArenaCleanupLayout.layout I.free I.capacity aBase nA bBase I.nB cBase I.nC q L
  have hpair := TernaryArenaPairMass.pairMass_le maps τ cap Q I' M n G.hM G.hr
    ((length_le keysB I.nB).trans G.hnB) ((length_le keysC I.nC).trans G.hnC)
  have hCc := G.Ccount
  have hcounts := G.counts
  change I.nC+1≤I.capacity at hCc
  change I.nB+3*I.nC+1≤I.capacity at hcounts
  have hend := G.hend
  change finish I.free I.capacity≤lim.space at hend
  have hgeom := TernaryArenaReporterBounds.arena_geometry G.matrix G.terms
    ((length_le keysB I.nB).trans (by omega : I.nB≤I.capacity))
    ((length_le keysC I.nC).trans (by omega : I.nC≤I.capacity)) hend
  refine {
    leftCount:=rfl
    rightCount:=rfl
    leftSrc:=rfl
    rightSrc:=rfl
    beforeMatrix:=?_
    recordsApart:=Or.inr ?_
    matrixWindow:=hgeom.1
    scratchSpace:=hgeom.2.1
    positions:=TernaryArenaPostSelection.positions maps τ cap Q I U radix nA H A B C keysB keysC
    positionRead:=?_
    originalAbs:=fun i hi=>TernaryMomentDetectorResources.target_le_input _ U Hdet (A i) (hA i hi)
    detectorWord:=TernaryMomentDetectorResources.word_guard _ U Hdet lim G.detector
    resources:=?_
    support:=?_
    momentAbs:=?_
    nativeComplete:=TernaryArenaPostSelection.native_complete maps τ cap Q I U radix nA H A B C
      keysB keysC hcover hA hB hC hcap }
  · dsimp [c,TernaryArenaCleanupLayout.layout]
    unfold addr
    omega
  · change addr I.free I.capacity 17+I.nC<addr I.free I.capacity 19
    unfold addr
    omega
  · intro i hi
    exact (TernaryWantedBatchIndex.read_three _ Meta.wanted hi).1
  · intro ν hOutB hOutC hkeep hAbove hUnchanged
    exact TernaryArenaPostResources.resources maps τ cap Q I U radix nA aBase bBase cBase q L
      H A B C keysB keysC μ ν G.hM G.hr G.hF G.hN G.hnB G.hnC G.hw G.hd G.hend
      G.counts G.Ccount G.bankLo G.bankHi G.powersHi G.records G.matrix G.localPositive G.geometry
      G.controls G.countCapacity G.weight G.channel G.args hB hC Meta hUnchanged hOutB hOutC hkB hkC
  · intro i hi
    exact (TernaryArenaPostSelection.support maps τ cap K U radix nA Q I H A B C keysB keysC
      hb hp hB hC hcap hkB hkC hzero i hi).trans hsupport
  · intro i hi
    exact TernaryArenaReporterBounds.compact_moments S keysB keysC B C I.nB I.nC _ U Hdet
      rfl rfl hpair hB hC i

end ThreeSum.TernaryArenaPostCertificate
