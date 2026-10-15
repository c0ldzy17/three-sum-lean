import Submission.ThreeSum.TernaryColoredPostABI

noncomputable section
namespace ThreeSum.TernaryColoredFinalCall
open Light TernaryArenaLayout TernaryArenaSourceSetup TernaryArenaPostSelection
open LightOriginalSurvivors LightOriginalSurvivorPair TernaryExtensionEncoding
open TernaryCoverGoodMaps LightTernaryPostSelection TernaryArenaPostCertificate
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {p m F r J : ℕ} [Fact p.Prime]

theorem final_call {lim : Limits} {d M n Hdet K : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (U radix nA aBase bBase cBase q L : ℕ)
    (H : (TernarySignedReduction.Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ) (μ : ℕ→ℤ)
    (G : Guards (r := r) maps τ cap Q (selectedInput I U radix nA H A B C keysB keysC)
      lim (d+2) M n U Hdet I.nB I.nC)
    (R : LightTernaryPreparedPostSelection.Inputs
      (TernaryArenaCleanupLayout.layout I.free I.capacity aBase nA bBase I.nB cBase I.nC q L)
      lim (d+3) U L μ A B C keysB keysC)
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
      (fun j i => TernarySignedLayout.feature (TernarySignedReduction.rightRaw U radix J (C j)) i)=0)
    (pre suffix : Program) (loc : ℕ→ℤ) (header host : ℕ)
    (hloc5 : loc 5=(header : ℤ)) (hloc6 : loc 6=(I.free : ℤ))
    (hloc7 : loc 7=(I.capacity : ℤ)) (hloc10 : loc 10=(host : ℤ))
    (hloc12 : loc 12=(q : ℤ)) (hloc14 : loc 14=(L : ℤ))
    (hheader : Seg μ header [(aBase : ℤ),nA,bBase,I.nB,cBase,I.nC])
    (hheaderSpace : header+6≤lim.space) (hhostSpace : host+106≤lim.space)
    (hcapacity : 106≤I.capacity)
    (hhost : ∀i<106,i≠11→i≠34→μ (host+i)=
      (LightTernaryCompactReporter.zeroCounts (setup (r := r) maps τ cap Q
        (selectedInput I U radix nA H A B C keysB keysC))).argv.getD i 0) :
    let I' := selectedInput I U radix nA H A B C keysB keysC
    let S := setup (r := r) maps τ cap Q I'
    let c := TernaryArenaCleanupLayout.layout I.free I.capacity aBase nA bBase I.nB cBase I.nC q L
    let post := LightTernaryPreparedPostSelection.closedProgram
      S.left.xs S.left.ys S.left.zs S.right.xs S.right.ys S.right.zs Hdet
    Ends lim (ReportingHostRelocation.program pre post++suffix) d
      (.call (pre.length+(127*(TernaryMomentSchedule.channels (2*Hdet+1)).length+24))
        LightTernaryColoredSolver.postArgs 0) ⟨loc,μ⟩
      ((LightTernaryColoredSolver.postArgs.map Expr.cost).sum+2+
        LightTernaryPreparedPostSelection.time S Hdet c keysB keysC)
      (fun σ=>σ.loc 0=(if ∃i<nA,∃j<I.nB,∃k<I.nC,C k=A i+B j then 1 else 0 : ℤ) ∧
        Kept μ σ.mem (addr I.free I.capacity 6)) := by
  let I' := selectedInput I U radix nA H A B C keysB keysC
  let S := setup (r := r) maps τ cap Q I'
  let c := TernaryArenaCleanupLayout.layout I.free I.capacity aBase nA bBase I.nB cBase I.nC q L
  have hh := TernaryArenaFinalSolver.meets maps τ cap Q I U radix nA aBase bBase cBase q L H
    A B C keysB keysC μ G R Meta hcover hA hB hC hb hp hcap hkB hkC hsupport hzero
  dsimp only at hh
  rw [LightTernaryPreparedPostSelection.program_eq_closed] at hh
  have hrun := (ReportingHostRelocation.meets hh pre).append suffix
  have hvalues := TernaryColoredPostABI.post_values S loc μ header host I.free I.capacity
    aBase nA bBase I.nB cBase I.nC q L hloc5 hloc6 hloc7 hloc10 hloc12 hloc14 hheader hhost
    rfl rfl rfl rfl
  have hfinish := G.hend
  change finish I.free I.capacity≤lim.space at hfinish
  have hhA := R.beforeA
  have hhB := R.beforeB
  have hhC := R.beforeC
  have hhq := R.histBeforeHist
  have hhL := R.powerBeforeHist
  dsimp [TernaryArenaCleanupLayout.layout] at hhA hhB hhC hhq hhL
  have hbounds : aBase≤lim.space ∧ nA≤lim.space ∧ bBase≤lim.space ∧ cBase≤lim.space ∧
      q≤lim.space ∧ L≤lim.space := by
    simp only [finish,slots,addr] at hfinish hhA hhB hhC hhq hhL
    omega
  have hsafe := TernaryColoredPostABI.post_safe loc μ header host I.free I.capacity aBase nA
    bBase I.nB cBase I.nC q L hloc5 hloc6 hloc7 hloc10 hloc12 hloc14 hheader
    hheaderSpace hhostSpace hcapacity hfinish G.counts hbounds.1 hbounds.2.1 hbounds.2.2.1
    hbounds.2.2.2.1 hbounds.2.2.2.2.1 hbounds.2.2.2.2.2 G.hw
  simp only [LightTernaryPreparedPostSelection.libraries_length] at hrun
  apply Ends.callLast hrun (ha := ⟨hsafe,hvalues⟩) (hd := by have := R.hd; omega) (hT := le_rfl)
  intro ret ν hret
  exact ⟨by simpa using hret.1,hret.2⟩

end ThreeSum.TernaryColoredFinalCall
