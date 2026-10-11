import Submission.ThreeSum.LightReportingPositiveMasks

/-!
# Actual parent expansion returning compact positive-prefix mask arrays

All child construction, physical catalog lookup, exact querying, positive
selection, and aligned mask gathering are executed by this closed program.
Only the actual positive output intervals may change below child scratch.
-/

namespace ThreeSum.LightReportingPositiveExpand

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockIndex BlockMaskLayout BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
open ReportingHostMasks LightBlockChildrenIndexed ReportingHostPositive LightReportingPositiveMasks

set_option maxHeartbeats 2200000
set_option maxRecDepth 8000

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def body (pExpand pGather : ℕ) : Stmt :=
  .call pExpand [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,
    v 17,v 18,v 19,v 20,v 21,v 22,v 23,v 24,v 25] 28 ;;
  .call pGather [v 23,v 7,v 8,v 28,v 21,v 26,v 27] 29 ;;
  .set 0 (v 28)

def program : Program :=
  ReportingHostRelocation.program LightReportingCatalogExpand.program LightReportingGatherPair.program ++
    [body 46 48]

def time (h J k t : ℕ) : ℕ :=
  LightReportingCatalogExpand.time h J k t+LightReportingGatherPair.time (groupSize h)+120

abbrev KeptOutputs (μ ν : ℕ → ℤ) (bound outL outR n : ℕ) : Prop :=
  SameOn (fun i => i < bound ∧ Outside outL n i ∧ Outside outR n i) μ ν

theorem program_meets
    {μ : ℕ → ℤ} {h J k t baseL baseR boxCut boxBase indexBase ptrBase outL outR masks dstL dstR dst selected maskBase work depth : ℕ}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pre : List (Finset (Fin (512*h)))) (hk : k < J) (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1 % pMod+lift w.2.1*pMod+shift)-globalKey w.2.2)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdataL : baseL+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ outL)
    (hdataR : baseR+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ outL)
    (hindex : indexBase+count h (k+1) ≤ outL) (hptr : ptrBase+count h (k+1) ≤ outL)
    (hboxesEnd : boxBase+count h (k+1)*stride (suffixStage J (512*h) (k+1)) boxCut ≤ outL)
    (houtL : outL+groupSize h ≤ outR) (houtR : outR+groupSize h ≤ masks)
    (hmasks : masks+groupSize h ≤ dstL) (hleft : dstL+groupSize h ≤ dstR)
    (hright : dstR+groupSize h ≤ dst) (hdst : dst+groupSize h ≤ selected)
    (hselected : selected+groupSize h ≤ maskBase)
    (hqueryMasks : maskBase+LightSparseQuery.queryItems (residualSize h J (k+1)) t ≤ work)
    (hspace : work+1+tableSize (width h J)+(width h J+1) ≤ lim.space)
    (hpowSpace : work+(2*width h J+2) ≤ lim.space)
    (hemodSpace : work+(Nat.log 2 (LightReportingCatalogLookup.valueBound (width h J) (count h (k+1))+1)+2) ≤ lim.space)
    (hword : (((width h J+1)*2^(width h J+1) : ℕ) : ℤ) ≤ lim.word)
    (hlookupWord : (LightReportingCatalogLookup.word (width h J) (count h (k+1)) : ℤ) ≤ lim.word)
    (hvalueWord : (LightSparseQuery.magnitudeBound (suffixStage J (512*h) (k+1)) (suffixStage J (512*h) (k+1))
      (residualSize h J (k+1)) t B.card C.card : ℤ) ≤ lim.word)
    (ht : t ≤ residualSize h J (k+1)+1) (hboxCut : boxCut ≤ residualSize h J (k+1))
    (hflags : residualSize h J (k+1)-t ≤ boxCut)
    (hstoredL : LightZetaStages.StoredThrough μ baseL (sourceCut h J)
      (leftSource pMod B b w.2.2) (width h J))
    (hstoredR : LightZetaStages.StoredThrough μ baseR (sourceCut h J)
      (rightSource pMod shift C c w.2.2) (width h J))
    (hindexData : ∃ S : List ℤ, Seg μ indexBase S ∧
      S.Perm (ReportingHostPackedCatalog.codes (ReportingHostPackedCatalog.prefixKey h J (k+1)) (count h (k+1))) ∧
      S.Pairwise (· ≤ ·))
    (hptrs : SegN μ ptrBase (List.ofFn fun i : Fin (count h (k+1)) =>
      boxBase+i.val*stride (suffixStage J (512*h) (k+1)) boxCut))
    (hboxes : ∀ i < count h (k+1), LightBoxStages.StoredThrough μ
      (boxBase+i*stride (suffixStage J (512*h) (k+1)) boxCut) boxCut
      (leafWeight (block_fit (Nat.succ_le_of_lt hk)) (leftSource pMod B b w.2.2) (rightSource pMod shift C c w.2.2)
        (suffixStage J (512*h) (k+1)) (preL h J (k+1) i) (preR h J (k+1) i))
      (suffixStage J (512*h) (k+1)))
    (hd : depth+2*width h J+16 ≤ lim.depth) :
    Meets lim program 49 depth
      [width h J,h,rowMask (outputRows w.2.2) ⟨k,hk⟩,
        subsetMask (leftPrefix k (prefixRows (J := J) pre)),
        subsetMask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) pre)),
        subsetMask (querySet k (outputRows w.2.2)),masks,dstL,dstR,work,
        sourceCut h J,suffixStage J (512*h) (k+1),(k+1)*h,residualSize h J (k+1),
        t,baseL,baseR,boxCut,indexBase,ptrBase,count h (k+1),groupSize h,dst,selected,maskBase,(k+1)*(512*h),outL,outR]
      μ (time h J k t)
      (fun r ν =>
        let pos := positiveChildren (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w pre hk
        r = (pos.length : ℤ) ∧
        SegN ν outL (pos.map fun next => subsetMask (leftPrefix (k+1) (prefixRows (J := J) next))) ∧
        SegN ν outR (pos.map fun next =>
          subsetMask (rightPrefix (k+1) (outputRows w.2.2) (prefixRows (J := J) next))) ∧
        KeptOutputs μ ν masks outL outR pos.length) := by
  let I := rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c
  have hlen := LightReportingFilter.selected_length_le
    (fun i => prefixQuery I w (k+1) (childAt w.2.2 pre hk i)) (groupSize h)
  change (selectedIndices I w pre hk).length ≤ groupSize h at hlen
  have hposLen : (positiveChildren I w pre hk).length = (selectedIndices I w pre hk).length := by
    simp only [positiveChildren,selectedIndices,List.length_map]
  have hmaskWord : ((2^(width h J+1) : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.le_mul_of_pos_left _ (by omega))).trans hword
  apply Meets.of_body (p := 49) (by rfl : program[49]? = some (body 46 48))
  unfold body time
  have he := ((LightReportingCatalogExpand.program_meets (depth := depth+1) (μ := μ)
    pMod shift A B C a b c w pre hk hp hkey hw (by omega) (by omega) (by omega) (by omega)
    (by omega) hmasks hleft hright hdst hselected hqueryMasks hspace hpowSpace hemodSpace hword hlookupWord
    hvalueWord ht hboxCut hflags hstoredL hstoredR hindexData hptrs hboxes (by omega)).append
      (LightReportingGatherPair.program.map
        (ReportingHostRelocation.relocate LightReportingCatalogExpand.program.length))).append [body 46 48]
  light_call he using LightReportingCatalogExpand.time,LightReportingGatherPair.time
    with found μ₁ ⟨hfound,hindices,hcounts,hchildren,hchildL,hchildR,hkeepExpand⟩
  change found = ((selectedIndices I w pre hk).length : ℤ) at hfound
  have htime : LightReportingGatherPair.time (selectedIndices I w pre hk).length ≤
      LightReportingGatherPair.time (groupSize h) := by
    unfold LightReportingGatherPair.time LightReportingGather.time
    omega
  have hg := ((ReportingHostRelocation.meets
    (LightReportingPositiveMasks.program_meets (d := depth+1) (μ := μ₁)
      (indices := selected) (srcL := dstL) (srcR := dstR) (dstL := outL) (dstR := outR)
      I w pre hk hw (by omega) (by omega) (by omega) (by omega) (by omega)
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inr (by omega)) (Or.inl (by omega)) hindices hchildL hchildR hmaskWord (by omega))
    LightReportingCatalogExpand.program).append [body 46 48]).mono_time htime
  light_call hg using hfound,LightReportingCatalogExpand.time,LightReportingGatherPair.time
    with ret μ₂ ⟨hleftOut,hrightOut,hkeepGather⟩
  light_set ((selectedIndices I w pre hk).length : ℕ)
    using hfound,LightReportingCatalogExpand.time,LightReportingGatherPair.time
  refine ⟨by simp [I,positiveChildren,selectedIndices],hleftOut,hrightOut,?_⟩
  intro i hi
  rw [hposLen] at hi
  exact (hkeepGather i ⟨hi.2.1,hi.2.2⟩).trans (hkeepExpand i hi.1)

theorem time_bound {h J k t : ℕ} (hk : k < J) (ht : t ≤ residualSize h J (k+1)+1) :
    time h J k t ≤
      26000*(width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J (k+1)) t+1)*(groupSize h+1) := by
  have he := LightReportingCatalogExpand.time_bound hk ht
  have hg := LightReportingGatherPair.time_bound (groupSize h)
  have hp : 1 ≤ (width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J (k+1)) t+1) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hm := Nat.mul_le_mul_right (groupSize h+1) hp
  unfold time
  nlinarith

end ThreeSum.LightReportingPositiveExpand
