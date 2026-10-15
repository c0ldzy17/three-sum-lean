import Submission.ThreeSum.TernaryArenaFinalBounds
import Submission.ThreeSum.TernaryArenaPostCertificate
import Submission.ThreeSum.TernaryArenaSourceArithmetic

noncomputable section
namespace ThreeSum.TernaryArenaFinalGuardAllocation
open Light TernaryArenaLayout TernaryArenaSourceSetup TernaryArenaPrefixFootprints
open TernaryCoverGoodMaps TernaryLocalParameters TernaryArenaAllocation
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
variable {p m F r : ℕ} [Fact p.Prime]

private theorem prefix_cells (maps : Fin F→Weight m p) (τ cap M b K H drift scale n U r : ℕ) :
    4^(N m r)+(2*N m r+1)≤(numbers maps τ cap M b K H drift scale n U r).prefixCells := by
  have hn : N m r=fixedLength m*r := by unfold N; ring
  rw [hn,pow_mul]
  dsimp only [numbers]
  omega

/-- All final scalar guards come from the actual fixed arena allocation.
Only the literal family cover and a charged query-time upper bound remain
as mathematical parameters; there is no execution or source-model oracle. -/
theorem guards {lim : Limits} {d M b K H drift scale n U nB nC : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : TernaryGoodOutputCatalog.Output m)
    (Alloc : Allocation maps τ cap M b K H drift scale) (I : Input)
    (hok : (TernaryArenaAllocationResources.need Alloc n U).Ok lim I.free d)
    (hcap : I.capacity=capacity Alloc.D Alloc.E (n+U))
    (hr : r≤Nat.clog M (n^2)) (hM : 1<M) (hF : 1<F) (hN : 0<N m r)
    (hnB : nB≤n) (hnC : nC≤n) (hIB : I.nB≤nB) (hIC : I.nC≤nC)
    (hO : I.requesterCount≤n*2^(LightTernaryDimensions.J M b n U))
    (hweight : I.weightCap=weight H (4^fixedLength m) U)
    (hprefix : I.prefixFree=addr I.free I.capacity 13)
    (hcover : ∀a b : ZMod p, ∃i, TernaryCoverFrequency.Covers m p cap τ (maps i) (a,b))
    (htime : TernaryArenaCountReady.queryTime (m := m) (r := r) I
      (valueCap (r := r) maps cap I)≤I.queryTime) :
    TernaryArenaPostCertificate.Guards (r := r) maps τ cap Q I lim d M n U H nB nC := by
  have HC : Fits I.capacity (numbers maps τ cap M b K H drift scale n U r) := by
    rw [hcap]
    exact Alloc.fits n U r hr
  obtain ⟨hend,hword,hdepth,hw⟩ := TernaryArenaAllocationResources.ok Alloc hok
  rw [←hcap] at hend hword hdepth
  have hB : I.nB≤n := hIB.trans hnB
  have hC : I.nC≤n := hIC.trans hnC
  have hCells := TernaryArenaFinalBounds.cells (r := r) maps τ cap M b K H drift scale I n U hO
  have hmatrix := hCells.1.trans HC.reporterCells
  have hterms := hCells.2.1.trans HC.reporterCells
  have hsize : 4*n+2≤I.capacity := hCells.2.2.1.trans HC.reporterCells
  have hcounts : nB+3*nC+1≤I.capacity := by omega
  have hCc : nC+1≤I.capacity := by omega
  have hweights : I.weightCap≤weight H (4^fixedLength m) U := hweight.le
  have hd6 : d+6+I.capacity≤lim.depth := by omega
  have CC := TernaryArenaFrontBounds.capacity maps τ cap M b K H drift scale I n U hB hC hO
    hweights HC hend hprefix hword hd6 htime
  have hpowerCells := (prefix_cells maps τ cap M b K H drift scale n U r).trans HC.prefixCells
  have hprefixEnd : I.prefixFree+4^(N m r)+(2*N m r+1)≤addr I.free I.capacity 16 := by
    rw [hprefix]
    simpa only [Nat.add_assoc] using (before (i := 13) (j := 16) (by decide) hpowerCells)
  have hbankEnd : I.prefixFree+nb m r≤addr I.free I.capacity 16 := by
    have hb := TernaryArenaSourceControlBudget.bank_le m r
    omega
  have hscalar : TernaryArenaArgumentWords.scalarControl m p F r (entries (r := r) maps τ I).length≤I.capacity := by
    exact (TernaryArenaFinalBounds.scalars maps τ cap M b K H drift scale I n U hO).trans
      (by rw [hcap]; exact Alloc.bound n U r hr)
  have hBcap : I.nB≤I.capacity := by omega
  have hCcap : I.nC≤I.capacity := by omega
  have hBspace : addr I.free I.capacity 10+I.nB≤lim.space := region_space (by decide) hBcap hend
  have hCspace : addr I.free I.capacity 16+nB+1+2*nC+I.nC≤lim.space := by
    have he : addr I.free I.capacity 17≤lim.space := region_space (len := 0) (by decide) (by omega) hend
    unfold addr at *
    omega
  have hArgs := TernaryArenaArgumentWords.args_word maps τ cap Q I hw hend hscalar hBcap hCcap
    (hprefixEnd.trans (region_space (len := 0) (by decide) (by omega) hend)) hBspace hCspace
  have hWords := TernaryArenaFinalBounds.words (r := r) maps τ cap M b K H drift scale n U
  have hdet := (Int.ofNat_le.mpr (hWords.1.trans HC.reporterWord)).trans hword
  have hchannel := (Int.ofNat_le.mpr (hWords.2.trans HC.reporterWord)).trans hword
  have hlocal := TernaryNativeCoverWitness.source_records_nonempty maps cap τ hcover
  refine {
    hM:=hM
    hr:=hr
    hF:=hF
    hN:=hN
    hnB:=hnB
    hnC:=hnC
    hw:=hw
    hd:=by omega
    hend:=hend
    counts:=hcounts
    Ccount:=hCc
    bankLo:=?_
    bankHi:=hbankEnd
    powersHi:=hprefixEnd
    records:=CC.records
    matrix:=hmatrix
    terms:=hterms
    localPositive:=?_
    geometry:=fun right=>TernaryArenaSourceArithmetic.geometry maps τ cap M b K H drift scale I n U hB hC HC hend right
    controls:=fun right=>TernaryArenaSourceArithmetic.controls maps τ cap M b K H drift scale I n U hB hC hweights HC hword hd6 right
    countCapacity:=CC
    weight:=?_
    channel:=hchannel
    detector:=hdet
    args:=hArgs }
  · rw [hprefix]
    unfold addr
    omega
  · intro right
    cases right
    · exact hlocal.1
    · exact hlocal.2
  · rw [hweight]
    unfold weight
    omega

end ThreeSum.TernaryArenaFinalGuardAllocation
