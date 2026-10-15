import Submission.ThreeSum.TernaryArenaOriginalInputs
import Submission.ThreeSum.TernaryArenaPrefixState
import Submission.ThreeSum.TernaryArenaPreparedMemory
import Submission.ThreeSum.TernaryArenaSeedDataReads
import Submission.ThreeSum.TernaryArenaTensorGuardAllocation
import Submission.ThreeSum.TernaryArenaCandidateGuardAllocation
import Submission.ThreeSum.TernaryArenaCandidateScoreBounds

noncomputable section
namespace ThreeSum.TernaryArenaPrefixInputs
open Light TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps TernaryArenaLayout
open TernaryArenaSourceSetup TernaryArenaSeedCandidate TernaryArenaSeedData
open TernaryArenaSelectedBudgets TernaryArenaAllocation
open TernaryOriginalRowMenu TernaryNativeCompleteFrontend
open TernaryExtensionEncoding
open LightTernarySeedScoreFactory
variable {p m F : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000


private theorem cell_lt {base count width i k stop : ℕ}
    (hend : base+count*width≤stop) (hi : i<count) (hk : k<width) :
    base+i*width+k<stop := by nlinarith

/-- The retained prefix state supplies all old-key and span reads. Every
other read is transported from the actual immutable initialization. -/
theorem reads (I : Input) (A : Inputs) (j featureBound tagBound positionCap seedCount ordinal : ℕ)
    (ℓ : E→ₗ[ZMod p] ZMod p) (seeds : ℕ→E×E)
    (L R O : ℕ→ℕ→ℤ) (s : State (p := p) A) (catalog : ℕ→ℕ→ℕ) (initial μ : ℕ→ℤ)
    (h : Originals I A seedCount featureBound tagBound positionCap ℓ seeds L R O initial)
    (H : TernaryArenaPrefixState.Memory I A (fun i t => L i t.val) (fun i t => R i t.val)
      (fun i t => O i t.val) j s catalog initial μ)
    (hi : ordinal<seedCount) :
    TernaryArenaSeedPrimitiveGuards.Reads I A ordinal
      (data I A j featureBound ordinal ℓ (seeds ordinal) s.row
        (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) s.rows catalog) μ positionCap := by
  apply TernaryArenaSeedDataReads.reads I A j featureBound ordinal positionCap ℓ (seeds ordinal)
    s.row _ _ _ s.rows catalog μ h.BEnd h.CEnd h.OEnd ?_ h.positionEnd h.feature
    (fun i hi t => h.BBound i hi t.val t.isLt)
    (fun i hi t => h.CBound i hi t.val t.isLt)
    (fun i hi t => h.OBound i hi t.val t.isLt)
    ?_ ?_ ?_ ?_ H.B H.Cvalues H.Ovalues H.represents H.bounded H.read ?_ h.positionBound
  · have hh:=Nat.mul_le_mul_right (A.J+2) (show ordinal+1≤seedCount by omega)
    nlinarith [h.menuEnd]
  · intro i hi k hk
    exact (H.immutable _ (cell_lt h.BEnd hi hk)).trans (h.BRead i hi k hk)
  · intro i hi k hk
    exact (H.immutable _ (cell_lt h.CEnd hi hk)).trans (h.CRead i hi k hk)
  · intro i hi k hk
    exact (H.immutable _ (cell_lt h.OEnd hi hk)).trans (h.ORead i hi k hk)
  · intro k hk
    exact (H.immutable _ (cell_lt h.menuEnd hi hk)).trans (h.menuRead ordinal hi k hk)
  · intro i hi
    have hp:=h.positionEnd
    exact (H.immutable _ (by omega)).trans (h.positionRead i hi)

/-- Full concrete controller readiness from the real retained prefix memory,
the physically emitted host header and the enumerated bank. No kernel
execution, source model, per-candidate guard or score oracle is assumed. -/
theorem ready {lim : Limits} {depth K H M b drift scale n U seedCount featureBound tagBound positionCap j : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : TernaryGoodOutputCatalog.Output m)
    (Alloc : Allocation maps τ cap M b K H drift scale)
    (I : Input) (A : Inputs) (ℓ : E→ₗ[ZMod p] ZMod p) (seeds : ℕ→E×E)
    (L R O : ℕ→ℕ→ℤ) (s : State (p := p) A) (catalog : ℕ→ℕ→ℕ) (initial μ : ℕ→ℤ)
    (hok : (TernaryArenaAllocationResources.need Alloc n U).Ok lim I.free depth)
    (hcap : I.capacity=capacity Alloc.D Alloc.E (n+U))
    (hr : j+1≤Nat.clog M (n^2)) (hJ : A.J=LightTernaryDimensions.J M b n U)
    (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightTernaryDimensions.J M b n U))
    (hpos : positionCap≤n)
    (hseeds : seedCount≤(p^(LightTernaryDimensions.dim M b p K n U))^2)
    (hweight : I.weightCap≤TernaryArenaPrefixFootprints.weight H (4^fixedLength m) U)
    (htag : tagBound≤2*(4^fixedLength m)+1) (hweightLower : tagBound^2≤I.weightCap)
    (hprefix : I.prefixFree=addr I.free I.capacity 13)
    (hfamily : 1<F) (hN : 0<N m (j+1))
    (hlocal : ∀right,0<(localRecords maps cap right).length)
    (htime : TernaryArenaCountReady.queryTime (m := m) (r := j+1) I (valueCap (r := j+1) maps cap I)≤I.queryTime)
    (hcodes : Seg μ I.prefixFree ((bankCodes m (j+1)).map (fun c => (c : ℤ))))
    (hpowers : LightSubsetAddress.Powers μ (I.prefixFree+4^(N m (j+1))) (2*N m (j+1)))
    (ret : ℤ) (hheader : Seg μ (addr I.free I.capacity 1)
      (TernaryArenaHeaderAgreement.emittedHeader I p m F j Q ret))
    (h : Originals I A seedCount featureBound tagBound positionCap ℓ seeds L R O initial)
    (HM : TernaryArenaPrefixState.Memory I A (fun i t => L i t.val) (fun i t => R i t.val)
      (fun i t => O i t.val) j s catalog initial μ)
    (hτ : 0<τ) (hnonempty : 1≤(TernaryGoodOutputCatalog.raws maps τ).length) :
    TernaryArenaControllerCore.InputsReady (lim := lim) (depth := depth) (K := K)
      (U := tagBound) (n := seedCount) (positionCap := positionCap) maps τ cap Q I A
      (fun ordinal => data I A j featureBound ordinal ℓ (seeds ordinal) s.row
        (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) s.rows catalog) μ L R := by
  let D := fun ordinal => data I A j featureBound ordinal ℓ (seeds ordinal) s.row
    (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) s.rows catalog
  have leftRead (i : ℕ) (hi : i<I.nB) (t : ℕ) (ht : t<A.J+2) :
      μ (A.leftTagged+i*(A.J+2)+TernarySignedLayout.offset A.J t)=L i t :=
    (HM.immutable _ (cell_lt h.leftEnd hi (TernarySignedLayout.offset_lt ht))).trans (h.leftRead i hi t ht)
  have rightRead (i : ℕ) (hi : i<I.nC) (t : ℕ) (ht : t<A.J+2) :
      μ (A.rightTagged+i*(A.J+2)+TernarySignedLayout.offset A.J t)=R i t :=
    (HM.immutable _ (cell_lt h.rightEnd hi (TernarySignedLayout.offset_lt ht))).trans (h.rightRead i hi t ht)
  obtain ⟨hend,hword,hdepth,hspace⟩:=TernaryArenaAllocationResources.ok Alloc hok
  rw [←hcap] at hend hword hdepth
  have HC : TernaryArenaPrefixFootprints.Fits I.capacity
      (TernaryArenaPrefixFootprints.numbers maps τ cap M b K H drift scale n U (j+1)) := by
    rw [hcap]
    exact Alloc.fits n U (j+1) hr
  have hjC : j+1≤I.capacity := by
    have hh:=HC.depth
    dsimp only [TernaryArenaPrefixFootprints.numbers] at hh
    omega
  refine ⟨hprefix,hτ,hnonempty,?_,?_,?_,?_⟩
  · intro ordinal hi
    exact reads I A j featureBound tagBound positionCap seedCount ordinal ℓ seeds L R O s catalog initial μ h HM hi
  · intro ordinal hi
    exact TernaryArenaTensorGuardAllocation.tensor_hardware maps τ cap Q Alloc I A (D ordinal) μ L R
      hend hword (by omega) hspace hcap hr hJ hnB hnC hO hweight htag hweightLower hprefix hfamily hN hlocal htime hcodes hpowers ret
      (by simpa only [Nat.add_sub_cancel] using hheader)
      (h.leftEnd.trans (by unfold addr;omega)) (h.rightEnd.trans (by unfold addr;omega))
      leftRead rightRead h.leftBound h.rightBound
  · intro ordinal hi
    have rr:=TernaryArenaCandidateGuardAllocation.resources maps τ cap Alloc I A (D ordinal)
      hok hcap hr hJ hnB hnC hO hpos h.feature h.feature h.feature (hi.trans_le hseeds)
    exact { rr with depth := by omega }
  · intro ordinal hi
    have hh:=TernaryArenaCandidateScoreBounds.allocated maps τ cap M b K H drift scale tagBound
      Alloc Q I A ordinal n U (D ordinal) L R hok hcap hr hJ hnB hnC hO htag h.leftBound h.rightBound
    exact hh.2.2.1.trans hh.2.2.2

/-- The genuine preparation execution discharges every bank/header/read premise
of controller readiness, including preservation of the old selected span. -/
theorem prepared_ready {lim : Limits} {depth K H M b drift scale n U seedCount featureBound tagBound positionCap j : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : TernaryGoodOutputCatalog.Output m)
    (Alloc : Allocation maps τ cap M b K H drift scale)
    (I : Input) (A : Inputs) (ℓ : E→ₗ[ZMod p] ZMod p) (seeds : ℕ→E×E)
    (L R O : ℕ→ℕ→ℤ) (s : State (p := p) A) (catalog : ℕ→ℕ→ℕ) (initial μ ν : ℕ→ℤ)
    (hok : (TernaryArenaAllocationResources.need Alloc n U).Ok lim I.free depth)
    (hcap : I.capacity=capacity Alloc.D Alloc.E (n+U))
    (hr : j+1≤Nat.clog M (n^2)) (hJ : A.J=LightTernaryDimensions.J M b n U)
    (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightTernaryDimensions.J M b n U))
    (hpos : positionCap≤n)
    (hseeds : seedCount≤(p^(LightTernaryDimensions.dim M b p K n U))^2)
    (hweight : I.weightCap≤TernaryArenaPrefixFootprints.weight H (4^fixedLength m) U)
    (htag : tagBound≤2*(4^fixedLength m)+1) (hweightLower : tagBound^2≤I.weightCap)
    (hprefix : I.prefixFree=addr I.free I.capacity 13)
    (hfamily : 1<F) (hN : 0<N m (j+1))
    (hlocal : ∀right,0<(localRecords maps cap right).length)
    (htime : TernaryArenaCountReady.queryTime (m := m) (r := j+1) I (valueCap (r := j+1) maps cap I)≤I.queryTime)
    (h : Originals I A seedCount featureBound tagBound positionCap ℓ seeds L R O initial)
    (HM : TernaryArenaPrefixState.Memory I A (fun i t => L i t.val) (fun i t => R i t.val)
      (fun i t => O i t.val) j s catalog initial μ)
    (U0 alpha beta budgetScale : ℕ)
    (HP : LightTernaryPrefixStep.Prepared
      (TernaryArenaPrefixPrepare.inputs p m F j A.J n U0 alpha beta budgetScale I Q) μ ν)
    (hTemplate : Seg μ (addr I.free I.capacity 0) (TernaryArenaHeaderAgreement.templateValues I p m F))
    (hτ : 0<τ) (hnonempty : 1≤(TernaryGoodOutputCatalog.raws maps τ).length) :
    TernaryArenaControllerCore.InputsReady (lim := lim) (depth := depth) (K := K)
      (U := tagBound) (n := seedCount) (positionCap := positionCap) maps τ cap Q I A
      (fun ordinal => data I A j featureBound ordinal ℓ (seeds ordinal) s.row
        (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) s.rows catalog) ν L R := by
  have HC : TernaryArenaPrefixFootprints.Fits I.capacity
      (TernaryArenaPrefixFootprints.numbers maps τ cap M b K H drift scale n U (j+1)) := by
    rw [hcap]
    exact Alloc.fits n U (j+1) hr
  obtain ⟨hB,hC,hOut,_,hspan,_,_,_⟩:=TernaryArenaPrimitiveBounds.spatial (r := j+1)
    maps τ cap M b K H drift scale I A n U hJ hnB hnC hO HC
  have h106 : 106≤I.capacity := by
    have hh:=capacity_pos Alloc.D Alloc.E (n+U)
    rw [←hcap] at hh
    omega
  have hSpan : A.J*p^j≤I.capacity := by simpa only [Nat.add_sub_cancel] using hspan
  obtain ⟨HM',codes,powers,ret,header⟩:=TernaryArenaPreparedMemory.prepared I A j n U0 alpha beta
    budgetScale Q (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val)
    s catalog initial μ ν HP hprefix h106 hB hC hOut hSpan hTemplate HM
  exact ready maps τ cap Q Alloc I A ℓ seeds L R O s catalog initial ν hok hcap hr hJ
    hnB hnC hO hpos hseeds hweight htag hweightLower hprefix hfamily hN hlocal htime
    (by
      change Seg ν I.prefixFree (List.map id
        ((bankCodes m (j+1)).flatMap (fun (a : ℕ) => [(a : ℤ)])))
      simpa only [←List.map_eq_flatMap,List.map_id] using codes)
    powers ret header h HM' hτ hnonempty

end ThreeSum.TernaryArenaPrefixInputs
