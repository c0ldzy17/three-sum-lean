import Submission.ThreeSum.LightReportingCatalogLevel
import Submission.ThreeSum.LightBlockChildrenIndexed

/-!
# Complete parent expansion through an actual shared shrinking-suffix catalog

This program constructs every ordered child mask pair, locates its own cached
box through the physical sorted index, runs the exact original raw-count
query, and stably compacts positive child positions. It requires no supplied
per-child box addresses and retains the complete source/catalog storage.
-/

namespace ThreeSum.LightReportingCatalogExpand

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockIndex BlockMaskLayout BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
open ReportingHostMasks LightBlockChildrenIndexed

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def body (pChildren pLevel : ℕ) : Stmt :=
  .call pChildren [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9] 26 ;;
  .call pLevel [v 0,v 10,v 11,v 12,v 12,v 11,v 25,v 13,v 26,v 14,v 15,v 16,v 17,
    v 18,v 19,v 20,v 7,v 8,v 21,v 22,v 24,v 9,v 23] 0

def program : Program :=
  ReportingHostRelocation.program LightBlockChildren.program LightReportingCatalogLevel.program ++
    [body 0 45]

def time (h J k t : ℕ) : ℕ :=
  LightBlockChildren.time (width h J) (2*h) h+
    LightReportingCatalogLevel.time h J (k+1) t (groupSize h)+150

theorem program_meets
    {μ : ℕ → ℤ} {h J k t baseL baseR boxCut boxBase indexBase ptrBase masks dstL dstR dst selected maskBase work depth : ℕ}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pre : List (Finset (Fin (512*h)))) (hk : k < J) (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1 % pMod+lift w.2.1*pMod+shift)-globalKey w.2.2)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdataL : baseL+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ masks)
    (hdataR : baseR+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ masks)
    (hindex : indexBase+count h (k+1) ≤ masks) (hptr : ptrBase+count h (k+1) ≤ masks)
    (hboxesEnd : boxBase+count h (k+1)*stride (suffixStage J (512*h) (k+1)) boxCut ≤ masks)
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
    (hd : depth+2*width h J+15 ≤ lim.depth) :
    Meets lim program 46 depth
      [width h J,h,rowMask (outputRows w.2.2) ⟨k,hk⟩,
        subsetMask (leftPrefix k (prefixRows (J := J) pre)),
        subsetMask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) pre)),
        subsetMask (querySet k (outputRows w.2.2)),masks,dstL,dstR,work,
        sourceCut h J,suffixStage J (512*h) (k+1),(k+1)*h,residualSize h J (k+1),
        t,baseL,baseR,boxCut,indexBase,ptrBase,count h (k+1),groupSize h,dst,selected,maskBase,(k+1)*(512*h)]
      μ (time h J k t)
      (fun r μ' =>
        let counts := fun i => prefixQuery (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c)
          w (k+1) (childAt w.2.2 pre hk i)
        r = ((LightReportingFilter.selected counts (groupSize h)).length : ℤ) ∧
        SegN μ' selected (LightReportingFilter.selected counts (groupSize h)) ∧
        SegN μ' dst (List.ofFn fun i : Fin (groupSize h) => counts i.val) ∧
        SegN μ' masks ((globalChildren ⟨k,hk⟩ (outputRows w.2.2 ⟨k,hk⟩) h).map subsetMask) ∧
        SegN μ' dstL ((childPrefixes w.2.2 pre hk).map fun next =>
          subsetMask (leftPrefix (k+1) (prefixRows (J := J) next))) ∧
        SegN μ' dstR ((childPrefixes w.2.2 pre hk).map fun next =>
          subsetMask (rightPrefix (k+1) (outputRows w.2.2) (prefixRows (J := J) next))) ∧
        Kept μ μ' masks) := by
  have hchildWord : ((2^(width h J+1) : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.le_mul_of_pos_left _ (by omega))).trans hword
  have hcRow : (outputRows w.2.2 ⟨k,hk⟩).card = 2*h :=
    LayerCounts.mem_vertices.mp (w.2.2 ⟨k,hk⟩).2.property
  have hc := ((LightBlockChildrenIndexed.program_meets (d := depth+1) (μ := μ)
    (masks := masks) (dstL := dstL) (dstR := dstR) (work := work)
    w.2.2 pre hp hk hw hmasks hleft (by omega) hpowSpace hchildWord
      (by change depth+1+width h J+3 ≤ lim.depth; omega)).append
      (LightReportingCatalogLevel.program.map
        (ReportingHostRelocation.relocate LightBlockChildren.program.length))).append [body 0 45]
  apply Meets.of_body (p := 46) (by rfl : program[46]? = some (body 0 45))
  unfold body time
  light_call hc using LightBlockChildren.time,LightReportingCatalogLevel.time
    with residual μ₁ ⟨hresidual,hchildMasks,hchildL,hchildR,hkeepChildren⟩
  have hsourceL := LightSignedLeafBatch.storedThrough_of_on hstoredL
    (by intro i _ hi; exact hkeepChildren i (hi.trans_le hdataL))
  have hsourceR := LightSignedLeafBatch.storedThrough_of_on hstoredR
    (by intro i _ hi; exact hkeepChildren i (hi.trans_le hdataR))
  have hindexData' : ∃ S : List ℤ, Seg μ₁ indexBase S ∧
      S.Perm (ReportingHostPackedCatalog.codes (ReportingHostPackedCatalog.prefixKey h J (k+1)) (count h (k+1))) ∧
      S.Pairwise (· ≤ ·) := by
    obtain ⟨S,hseg,hperm,hsorted⟩ := hindexData
    have hlen := hperm.length_eq.trans (ReportingHostPackedCatalog.codes_length _ _)
    refine ⟨S,?_,hperm,hsorted⟩
    intro i hi
    exact (hkeepChildren _ (by rw [hlen] at hi; omega)).trans (hseg i hi)
  have hptrs' : SegN μ₁ ptrBase (List.ofFn fun i : Fin (count h (k+1)) =>
      boxBase+i.val*stride (suffixStage J (512*h) (k+1)) boxCut) := by
    intro i hi
    have hi' : i < count h (k+1) := by simpa only [List.length_map,List.length_ofFn] using hi
    exact (hkeepChildren _ (by omega)).trans (hptrs i hi)
  have hboxes' (i : ℕ) (hi : i < count h (k+1)) :=
    ReportingHostQueryBounds.boxStored_of_on (hboxes i hi) (by
      intro j _ hj
      exact hkeepChildren j (hj.trans_le (ReportingHostCatalogSelection.selected_box_end hi hboxesEnd)))
  have hreadL (i : ℕ) (hi : i < groupSize h) : μ₁ (dstL+i) =
      (subsetMask (leftPrefix (k+1) (prefixRows (J := J) (childAt w.2.2 pre hk i))) : ℤ) := by
    rw [childAt_eq_get w.2.2 pre hk i hi]
    have hs := hchildL.getElem (i := i) (by simpa only [List.length_map,childPrefixes_length] using hi)
    simpa only [List.getElem_map] using hs
  have hreadR (i : ℕ) (hi : i < groupSize h) : μ₁ (dstR+i) =
      (subsetMask (rightPrefix (k+1) (outputRows w.2.2)
        (prefixRows (J := J) (childAt w.2.2 pre hk i))) : ℤ) := by
    rw [childAt_eq_get w.2.2 pre hk i hi]
    have hs := hchildR.getElem (i := i) (by simpa only [List.length_map,childPrefixes_length] using hi)
    simpa only [List.getElem_map] using hs
  have hl := (ReportingHostRelocation.meets
    (LightReportingCatalogLevel.program_meets (depth := depth+1) (μ := μ₁) (k := k+1)
      (inL := dstL) (inR := dstR) (n := groupSize h) (dst := dst) (selected := selected)
      (maskBase := maskBase) (work := work)
      pMod shift A B C a b c w (childAt w.2.2 pre hk) (Nat.succ_le_of_lt hk)
      (childAt_valid w.2.2 pre hp hk) hkey hw (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) hright hdst hselected hqueryMasks hspace hpowSpace hemodSpace
      hword hlookupWord hvalueWord ht hboxCut hflags hsourceL hsourceR hindexData' hptrs' hboxes'
      hreadL hreadR (by omega)) LightBlockChildren.program).append [body 0 45]
  light_call hl using LightBlockChildren.time,LightReportingCatalogLevel.time,hresidual
    with found μ₂ ⟨hfound,hselectedOut,hcounts,hkeepLevel⟩
  refine ⟨hfound,hselectedOut,hcounts,?_,?_,?_,?_⟩
  · intro i hi
    have hi' : i < groupSize h := by
      simpa only [List.length_map,globalChildren_length,hcRow,groupSize] using hi
    exact (hkeepLevel (masks+i) (by omega)).trans (hchildMasks i hi)
  · intro i hi
    have hi' : i < groupSize h := by simpa only [List.length_map,childPrefixes_length] using hi
    exact (hkeepLevel (dstL+i) (by omega)).trans (hchildL i hi)
  · intro i hi
    have hi' : i < groupSize h := by simpa only [List.length_map,childPrefixes_length] using hi
    exact (hkeepLevel (dstR+i) (by omega)).trans (hchildR i hi)
  · intro i hi
    exact (hkeepLevel i (by omega)).trans (hkeepChildren i hi)

theorem time_bound {h J k t : ℕ} (hk : k < J) (ht : t ≤ residualSize h J (k+1)+1) :
    time h J k t ≤
      25000*(width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J (k+1)) t+1)*(groupSize h+1) := by
  have hc := LightBlockChildrenIndexed.time_bound (h := h) hk
  have hl := LightReportingCatalogLevel.time_bound (n := groupSize h) (Nat.succ_le_of_lt hk) ht
  have hp : (width h J+1)^2 ≤ (width h J+1)^3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hm : (width h J+1)^2*(groupSize h+1) ≤
      (width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J (k+1)) t+1)*(groupSize h+1) := by
    nlinarith [Nat.mul_le_mul_right (groupSize h+1) hp]
  have hpos : 1 ≤ (width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J (k+1)) t+1)*(groupSize h+1) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  change LightBlockChildren.time (width h J) (2*h) h ≤ 1600*(width h J+1)^2*(groupSize h+1) at hc
  unfold time
  nlinarith

end ThreeSum.LightReportingCatalogExpand
