import Submission.ThreeSum.TernaryArenaPairMass
import Submission.ThreeSum.TernaryArenaReporterBounds
import Submission.ThreeSum.TernaryArenaSourceCertificate
import Submission.ThreeSum.TernaryArenaQueryModel

/-! Reporting resources specialized to the actual canonical source setup.
The remaining seed input consists solely of source/count readiness guards;
the executed signed-channel initializers supply all weight-array reads. -/
noncomputable section
namespace ThreeSum.TernaryArenaMomentResources
open Light TernaryArenaLayout TernaryArenaSourceSetup TernaryArenaPairMass
open TernaryCoverGoodMaps TernaryLocalParameters TernaryNativeMomentBounds
open TernaryMomentWeightBounds
variable {p m F r : ℕ} [Fact p.Prime]

def detectorNeed (maps : Fin F→Weight m p) (cap M H n U : ℕ) : Need :=
  TernaryMomentDetectorResources.need (envelope maps cap M n) U H
def channelNeed (maps : Fin F→Weight m p) (cap M H n U : ℕ) : Need :=
  TernaryMomentChannelResources.need (envelope maps cap M n) U (2*H)

theorem detector_polyNeed (maps : Fin F→Weight m p) (cap M H : ℕ) :
    PolyNeed (detectorNeed maps cap M H) :=
  TernaryMomentDetectorResources.polyNeed (envelope_powerBound maps cap M) H

theorem channel_polyNeed (maps : Fin F→Weight m p) (cap M H : ℕ) :
    PolyNeed (channelNeed maps cap M H) :=
  TernaryMomentChannelResources.polyNeed (envelope_powerBound maps cap M) (2*H)

theorem source_homogeneous (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool) :
    ∀ pair∈(source (r := r) maps cap I right).records,
      TernaryBank.rank ((TernaryBankCanonical.enumeration (N m r) (cut m r)).word
        ((source (r := r) maps cap I right).key pair.2))=r*alphaRank m := by
  intro pair hp
  have hi := (TernarySourceHostModel.mem_records _ _ _ _ _ _).mp hp
  exact TernaryArenaSourceCertificate.source_rank maps cap I right pair.2 hi.2.1

theorem weight_bounds (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (B C : ℕ→ℤ) (U K : ℕ)
    (hB : ∀ i<I.nB, |B i|≤(U : ℤ)) (hC : ∀ i<I.nC, |C i|≤(U : ℤ))
    (hcap : leftBound U K≤I.weightCap) :
    ∀ k<K+1, ∀ j≤k,
      (∀ i<(setup (r := r) maps τ cap Q I).left.NL,
        |LightTernaryMomentChannelFactory.leftWeights k j B i|≤
          ((setup (r := r) maps τ cap Q I).left.weightU : ℤ)) ∧
      (∀ i<(setup (r := r) maps τ cap Q I).right.NL,
        |LightTernaryMomentChannelFactory.rightWeights k j C i|≤
          ((setup (r := r) maps τ cap Q I).right.weightU : ℤ)) := by
  intro k hk j hj
  have hright : rightBound U K≤I.weightCap := by
    apply le_trans _ hcap
    unfold leftBound rightBound
    exact Nat.le_mul_of_pos_left _ (by positivity)
  constructor
  · intro i hi
    exact (left_bound (B i) (hB i hi) (by omega) hj).trans (Int.ofNat_le.mpr hcap)
  · intro i hi
    exact (right_bound (C i) (hC i hi) (by omega)).trans (Int.ofNat_le.mpr hright)

theorem resources {lim : Limits} {d originalB originalC M n U H : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (μ : ℕ→ℤ) (B C : ℕ→ℤ)
    (hM : 1<M) (hr : r≤Nat.clog M (n^2)) (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hseed : ∀ k<2*H+1, ∀ j≤k,
      TernarySourceCountExecutionFactory.Seed (setup (r := r) maps τ cap Q I) lim (d+2)
        (addr I.free I.capacity 28) μ
        (LightTernaryMomentChannelFactory.leftWeights k j B)
        (LightTernaryMomentChannelFactory.rightWeights k j C))
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+2<lim.depth)
    (hend : finish I.free I.capacity≤lim.space)
    (hnBl : I.nB≤I.capacity) (hnCl : I.nC≤I.capacity)
    (hcount : (2*H+1)*(entries (r := r) maps τ I).length≤I.capacity)
    (hrecords : 3*(entries (r := r) maps τ I).length≤I.capacity)
    (hbank : I.prefixFree+nb m r≤addr I.free I.capacity 25)
    (hpowers : I.prefixFree+4^(N m r)+(2*N m r+1)≤addr I.free I.capacity 25)
    (hBspace : originalB+I.nB≤addr I.free I.capacity 25)
    (hCspace : originalC+I.nC≤addr I.free I.capacity 25)
    (hB : ∀ i<I.nB, μ (originalB+i)=B i)
    (hC : ∀ i<I.nC, μ (originalC+i)=C i)
    (hBabs : ∀ i<I.nB, |B i|≤(U : ℤ)) (hCabs : ∀ i<I.nC, |C i|≤(U : ℤ))
    (hchannelWord : ((channelNeed maps cap M H n U).word : ℤ)≤lim.word)
    (hargs : ∀ z∈LightTernaryMomentChannelFactory.args (setup (r := r) maps τ cap Q I)
      originalB originalC (addr I.free I.capacity 25), |z|≤lim.word) :
    LightTernaryCertifiedMomentDriver.Resources (setup (r := r) maps τ cap Q I) lim d
      originalB originalC (addr I.free I.capacity 25) (2*H+1)
      (r*alphaRank m) (r*alphaRank m) U
      (TernaryMomentChannelResources.scoreBound (envelope maps cap M n) U (2*H)) μ B C := by
  have hpair := pairMass_le maps τ cap Q I M n hM hr hnB hnC
  have hwords := TernaryArenaReporterBounds.channel_words lim (envelope maps cap M n) U (2*H) hchannelWord
  have hc : (entries (r := r) maps τ I).length≤I.capacity := by nlinarith only [hcount]
  refine {
    hseed:=hseed
    himmutable:=?_
    hw:=hw
    hd:=hd
    hBspace:=hBspace
    hCspace:=hCspace
    hwindow:=before (by decide) hcount
    hleft:=before (by decide) hnBl
    hright:=region_space (by decide) hnCl hend
    houtBefore:=before (len := 0) (by decide) (by omega)
    hout:=region_space (by decide) hc hend
    hleftSpace:=region_space (len := 0) (by decide) (by omega) hend
    hB:=hB
    hC:=hC
    hBabs:=hBabs
    hCabs:=hCabs
    hscore:=?_
    hleftWord:=hwords.1
    hrightWord:=hwords.2.1
    haddWord:=hwords.2.2.1
    htermsWord:=hwords.2.2.2
    hargsWord:=hargs
    hleftHom:=source_homogeneous maps cap I false
    hrightHom:=source_homogeneous maps cap I true
    hQ:=?_ }
  · exact {
      leftInput:=before (by decide) hnBl
      leftCodes:=hbank
      leftPowers:=hpowers
      rightInput:=before (by decide) hnCl
      rightCodes:=hbank
      rightPowers:=hpowers
      frontCodes:=hbank
      frontRecords:=before (by decide) hrecords }
  · intro k hk j hj i hi
    exact TernaryMomentChannelResources.score_abs_le _ B C hpair hBabs hCabs (by omega) hj i
  · intro i hi
    exact TernaryArenaQueryModel.setup_rank hi

end ThreeSum.TernaryArenaMomentResources
