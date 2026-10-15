import Submission.ThreeSum.TernaryArenaAllocationResources
import Submission.ThreeSum.TernaryArenaSourceArithmetic
import Submission.ThreeSum.TernaryArenaTensorBounds
import Submission.ThreeSum.TernaryArenaPrimitiveBounds
import Submission.ThreeSum.TernaryArenaQueryTime
import Submission.ThreeSum.TernaryArenaCandidateGuard
import Submission.ThreeSum.TernaryPrefixPreparedHeader

noncomputable section
namespace ThreeSum.TernaryArenaTensorGuardAllocation
open Light TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps
open TernaryArenaSourceSetup TernaryNativeCompleteFrontend TernaryArenaLayout
open TernaryArenaPrefixFootprints TernaryArenaAllocation
open LightTernarySeedScoreFactory TernaryArenaSeedCandidate
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000

private theorem prefix_cells (maps : Fin F→Weight m p) (τ cap M b K H drift scale n U r : ℕ) :
    4^(N m r)+(2*N m r+1)≤(numbers maps τ cap M b K H drift scale n U r).prefixCells := by
  have hn : N m r=fixedLength m*r := by unfold N; ring
  rw [hn,pow_mul]
  dsimp only [numbers]
  generalize (4^fixedLength m)^r=q
  generalize (F+1)^r=f
  omega

/-- The actual emitted header supplies every immutable host field. Its one
varying count cell is written later by the real SeedScore program. -/
theorem header_read (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (seed : ℕ)
    (D : Data (config p r I A seed)) (μ : ℕ→ℤ) (ret : ℤ) (hr : 0<r)
    (hs : Seg μ (addr I.free I.capacity 1)
      (TernaryArenaHeaderAgreement.emittedHeader I p m F (r-1) Q ret)) :
    ∀i<106,i≠104→ μ (addr I.free I.capacity 1+i)=
      (setup (r := r) maps τ cap Q (sourceInput I A seed D)).argv.getD i 0 := by
  have hh := TernaryPrefixPreparedHeader.count_header (sourceInput I A seed D) (r-1) maps τ cap Q ret hs
  have he : r-1+1=r := by omega
  rw [he] at hh
  have hlen : (setup (r := r) maps τ cap Q (sourceInput I A seed D)).argv.length=106 := rfl
  intro i hi hne
  have hii : i<(setup (r := r) maps τ cap Q (sourceInput I A seed D)).argv.length := by simpa only [hlen] using hi
  have hc := hh i hii
  rw [Function.update_of_ne (by dsimp only [sourceInput]; omega)] at hc
  rw [List.getD_eq_getElem _ _ hii]
  exact hc

/-- A single fixed polynomial hardware need supplies all numeric fields
of the concrete tensor guard. The other inputs are literal physical reads
from the original-array/backend and prefix-preparation executions. -/
theorem tensor {lim : Limits} {depth K H M b drift scale n U seed tagBound : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : TernaryGoodOutputCatalog.Output m)
    (Alloc : Allocation maps τ cap M b K H drift scale)
    (I : Input) (A : Inputs) (D : Data (config p r I A seed)) (μ : ℕ→ℤ) (L R : ℕ→ℕ→ℤ)
    (hok : (TernaryArenaAllocationResources.need Alloc n U).Ok lim I.free depth)
    (hcap : I.capacity=capacity Alloc.D Alloc.E (n+U))
    (hr : r≤Nat.clog M (n^2)) (hJ : A.J=LightTernaryDimensions.J M b n U)
    (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightTernaryDimensions.J M b n U))
    (hweight : I.weightCap≤weight H (4^fixedLength m) U)
    (htag : tagBound≤2*(4^fixedLength m)+1) (hweightLower : tagBound^2≤I.weightCap)
    (hprefix : I.prefixFree=addr I.free I.capacity 13)
    (hfamily : 1<F) (hN : 0<N m r)
    (hlocal : ∀right, 0<(localRecords maps cap right).length)
    (htime : TernaryArenaCountReady.queryTime (m := m) (r := r) I (valueCap (r := r) maps cap I)≤I.queryTime)
    (hcodes : Seg μ I.prefixFree ((bankCodes m r).map (fun c => (c : ℤ))))
    (hpowers : LightSubsetAddress.Powers μ (I.prefixFree+4^(N m r)) (2*N m r))
    (ret : ℤ)
    (hheader : Seg μ (addr I.free I.capacity 1)
      (TernaryArenaHeaderAgreement.emittedHeader I p m F (r-1) Q ret))
    (leftEnd : A.leftTagged+I.nB*(A.J+2)≤addr I.free I.capacity 1)
    (rightEnd : A.rightTagged+I.nC*(A.J+2)≤addr I.free I.capacity 1)
    (leftRead : ∀i<I.nB,∀j<A.J+2, μ (A.leftTagged+i*(A.J+2)+TernarySignedLayout.offset A.J j)=L i j)
    (rightRead : ∀i<I.nC,∀j<A.J+2, μ (A.rightTagged+i*(A.J+2)+TernarySignedLayout.offset A.J j)=R i j)
    (leftBound : ∀i<I.nB,∀j<A.J+2, |L i j|≤(tagBound : ℤ))
    (rightBound : ∀i<I.nC,∀j<A.J+2, |R i j|≤(tagBound : ℤ)) :
    TernaryArenaSeedScoreReady.TensorGuard (lim := lim) (depth := depth) (K := K) (U := tagBound)
      maps τ cap Q I A D μ L R := by
  let I' := sourceInput I A seed D
  have HC : Fits I.capacity (numbers maps τ cap M b K H drift scale n U r) := by
    rw [hcap]
    exact Alloc.fits n U r hr
  obtain ⟨hend,hword,hdepth,hw⟩ := TernaryArenaAllocationResources.ok Alloc hok
  rw [←hcap] at hend hword hdepth
  have hd : depth+4+I.capacity≤lim.depth := by omega
  have hC := Alloc.constants n U
  rw [←hcap] at hC
  have hn : n≤I.capacity := by omega
  have hspace := TernaryArenaTensorBounds.spatial (r := r) maps τ cap M b K H drift scale I' n U hO HC
  have hcPrefix := (prefix_cells maps τ cap M b K H drift scale n U r).trans HC.prefixCells
  have hprefixEnd : I.prefixFree+4^(N m r)+(2*N m r+1)≤addr I.free I.capacity 16 := by
    rw [hprefix]
    simpa only [Nat.add_assoc] using (before (i := 13) (j := 16) (by decide) hcPrefix)
  have hheadPrefix : addr I.free I.capacity 1+106≤I.prefixFree := by
    rw [hprefix]
    exact before (by decide) hspace.1
  have hpositive : 0<r := by
    dsimp [N] at hN
    by_contra hn
    have hz : r=0 := by omega
    simpa only [hz,Nat.zero_mul,lt_self_iff_false] using hN
  have hwTensor := TernaryArenaTensorBounds.word_bound (r := r) maps τ cap M b K H drift scale
    Q I' n U tagBound hnB hnC hO hweight htag
  have hsum := (TernaryArenaTensorBounds.tensor_words_le_total maps τ cap M b K H drift scale n U r).trans
    (Alloc.total_le n U r hr)
  have wordTensor : (TernaryTensorWordResources.word K A.J
      (entries (r := r) maps τ I').length (TernaryNativeMomentBounds.scoreBound (setup (r := r) maps τ cap Q I')) tagBound : ℤ)≤lim.word := by
    rw [hJ]
    exact (Int.ofNat_le.mpr (hwTensor.trans (by simpa only [hcap] using hsum))).trans hword
  refine {
    family:=hfamily
    dimension:=hN
    wordSpace:=hw
    capacity:=TernaryArenaFrontBounds.capacity maps τ cap M b K H drift scale I' n U hnB hnC hO hweight HC hend hprefix hword hd htime
    nB:=hnB.trans hn
    nC:=hnC.trans hn
    prefixEnd:=hprefixEnd
    headerBeforePrefix:=hheadPrefix
    localNonempty:=hlocal
    geometry:=TernaryArenaSourceArithmetic.geometry maps τ cap M b K H drift scale I' n U hnB hnC HC hend
    controls:=TernaryArenaSourceArithmetic.controls maps τ cap M b K H drift scale I' n U hnB hnC hweight HC hword hd
    codes:=hcodes
    powers:=hpowers
    header:=header_read maps τ cap Q I A seed D μ ret hpositive hheader
    leftEnd:=leftEnd
    rightEnd:=rightEnd
    leftRead:=leftRead
    rightRead:=rightRead
    leftBound:=leftBound
    rightBound:=rightBound
    weightCap:=hweightLower
    headerCells:=hspace.1
    tensorCells:=by
      have hh := hspace.2.2.2.2
      change (entries (r := r) maps τ (sourceInput I A seed D)).length*
        (LightTernaryDimensions.J M b n U+2)^4≤I.capacity at hh
      rw [hJ]
      exact hh
    quadCells:=hspace.2.1
    powersCells:=hspace.2.2.1
    columnCells:=hspace.2.2.2.1
    tensorWord:=wordTensor }

/-- Numeric hardware form usable at nested controller depths inside the fixed reserve. -/
theorem tensor_hardware {lim : Limits} {depth K H M b drift scale n U seed tagBound : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : TernaryGoodOutputCatalog.Output m)
    (Alloc : Allocation maps τ cap M b K H drift scale)
    (I : Input) (A : Inputs) (D : Data (config p r I A seed)) (μ : ℕ→ℤ) (L R : ℕ→ℕ→ℤ)
    (hend : finish I.free I.capacity≤lim.space)
    (hword : (I.capacity : ℤ)≤lim.word)
    (hdepth : depth+4+I.capacity≤lim.depth) (hw : (lim.space : ℤ)≤lim.word)
    (hcap : I.capacity=capacity Alloc.D Alloc.E (n+U))
    (hr : r≤Nat.clog M (n^2)) (hJ : A.J=LightTernaryDimensions.J M b n U)
    (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightTernaryDimensions.J M b n U))
    (hweight : I.weightCap≤weight H (4^fixedLength m) U)
    (htag : tagBound≤2*(4^fixedLength m)+1) (hweightLower : tagBound^2≤I.weightCap)
    (hprefix : I.prefixFree=addr I.free I.capacity 13)
    (hfamily : 1<F) (hN : 0<N m r)
    (hlocal : ∀right, 0<(localRecords maps cap right).length)
    (htime : TernaryArenaCountReady.queryTime (m := m) (r := r) I (valueCap (r := r) maps cap I)≤I.queryTime)
    (hcodes : Seg μ I.prefixFree ((bankCodes m r).map (fun c => (c : ℤ))))
    (hpowers : LightSubsetAddress.Powers μ (I.prefixFree+4^(N m r)) (2*N m r))
    (ret : ℤ)
    (hheader : Seg μ (addr I.free I.capacity 1)
      (TernaryArenaHeaderAgreement.emittedHeader I p m F (r-1) Q ret))
    (leftEnd : A.leftTagged+I.nB*(A.J+2)≤addr I.free I.capacity 1)
    (rightEnd : A.rightTagged+I.nC*(A.J+2)≤addr I.free I.capacity 1)
    (leftRead : ∀i<I.nB,∀j<A.J+2, μ (A.leftTagged+i*(A.J+2)+TernarySignedLayout.offset A.J j)=L i j)
    (rightRead : ∀i<I.nC,∀j<A.J+2, μ (A.rightTagged+i*(A.J+2)+TernarySignedLayout.offset A.J j)=R i j)
    (leftBound : ∀i<I.nB,∀j<A.J+2, |L i j|≤(tagBound : ℤ))
    (rightBound : ∀i<I.nC,∀j<A.J+2, |R i j|≤(tagBound : ℤ)) :
    TernaryArenaSeedScoreReady.TensorGuard (lim := lim) (depth := depth) (K := K) (U := tagBound)
      maps τ cap Q I A D μ L R := by
  let I' := sourceInput I A seed D
  have HC : Fits I.capacity (numbers maps τ cap M b K H drift scale n U r) := by
    rw [hcap]
    exact Alloc.fits n U r hr
  have hd : depth+4+I.capacity≤lim.depth := hdepth
  have hC := Alloc.constants n U
  rw [←hcap] at hC
  have hn : n≤I.capacity := by omega
  have hspace := TernaryArenaTensorBounds.spatial (r := r) maps τ cap M b K H drift scale I' n U hO HC
  have hcPrefix := (prefix_cells maps τ cap M b K H drift scale n U r).trans HC.prefixCells
  have hprefixEnd : I.prefixFree+4^(N m r)+(2*N m r+1)≤addr I.free I.capacity 16 := by
    rw [hprefix]
    simpa only [Nat.add_assoc] using (before (i := 13) (j := 16) (by decide) hcPrefix)
  have hheadPrefix : addr I.free I.capacity 1+106≤I.prefixFree := by
    rw [hprefix]
    exact before (by decide) hspace.1
  have hpositive : 0<r := by
    dsimp [N] at hN
    by_contra hn
    have hz : r=0 := by omega
    simpa only [hz,Nat.zero_mul,lt_self_iff_false] using hN
  have hwTensor := TernaryArenaTensorBounds.word_bound (r := r) maps τ cap M b K H drift scale
    Q I' n U tagBound hnB hnC hO hweight htag
  have hsum := (TernaryArenaTensorBounds.tensor_words_le_total maps τ cap M b K H drift scale n U r).trans
    (Alloc.total_le n U r hr)
  have wordTensor : (TernaryTensorWordResources.word K A.J
      (entries (r := r) maps τ I').length (TernaryNativeMomentBounds.scoreBound (setup (r := r) maps τ cap Q I')) tagBound : ℤ)≤lim.word := by
    rw [hJ]
    exact (Int.ofNat_le.mpr (hwTensor.trans (by simpa only [hcap] using hsum))).trans hword
  refine {
    family:=hfamily
    dimension:=hN
    wordSpace:=hw
    capacity:=TernaryArenaFrontBounds.capacity maps τ cap M b K H drift scale I' n U hnB hnC hO hweight HC hend hprefix hword hd htime
    nB:=hnB.trans hn
    nC:=hnC.trans hn
    prefixEnd:=hprefixEnd
    headerBeforePrefix:=hheadPrefix
    localNonempty:=hlocal
    geometry:=TernaryArenaSourceArithmetic.geometry maps τ cap M b K H drift scale I' n U hnB hnC HC hend
    controls:=TernaryArenaSourceArithmetic.controls maps τ cap M b K H drift scale I' n U hnB hnC hweight HC hword hd
    codes:=hcodes
    powers:=hpowers
    header:=header_read maps τ cap Q I A seed D μ ret hpositive hheader
    leftEnd:=leftEnd
    rightEnd:=rightEnd
    leftRead:=leftRead
    rightRead:=rightRead
    leftBound:=leftBound
    rightBound:=rightBound
    weightCap:=hweightLower
    headerCells:=hspace.1
    tensorCells:=by
      have hh := hspace.2.2.2.2
      change (entries (r := r) maps τ (sourceInput I A seed D)).length*
        (LightTernaryDimensions.J M b n U+2)^4≤I.capacity at hh
      rw [hJ]
      exact hh
    quadCells:=hspace.2.1
    powersCells:=hspace.2.2.1
    columnCells:=hspace.2.2.2.1
    tensorWord:=wordTensor }

end ThreeSum.TernaryArenaTensorGuardAllocation
