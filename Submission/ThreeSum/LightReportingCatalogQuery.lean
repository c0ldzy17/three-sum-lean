import Submission.ThreeSum.ReportingHostCatalogSelection
import Submission.ThreeSum.ReportingHostCatalogIndexCosts

/-!
# Actual indexed suffix-box query with exact original raw-count semantics

The machine recovers the complete-catalog index from the two physical prefix
masks, reads its stored box pointer, and executes the suffix-local sparse
query. The original prefix is used only to state and prove its specification;
neither a catalog position nor a table pointer is supplied to this machine.
-/

namespace ThreeSum.LightReportingCatalogQuery

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixCatalog ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostCatalogSelection

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def body (pLookup pQuery : ℕ) : Stmt :=
  .call pLookup [v 0,v 17,v 15,v 4,v 6,v 19] 20 ;;
  .set 21 (M (v 16 +' v 20)) ;;
  .call pQuery [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 21,v 18,v 19] 0

def program : Program :=
  ReportingHostRelocation.program LightReportingCatalogLookup.program LightReportingSuffixQueryHost.program ++
    [body 3 34]

def time (h J k t : ℕ) : ℕ :=
  LightReportingCatalogLookup.time (width h J) (count h k)+
    LightReportingSuffixQueryHost.time (width h J) (suffixStage J (512*h) k) (residualSize h J k) t+100

theorem program_meets
    {μ : ℕ → ℤ} {h J k t baseL baseR boxCut boxBase indexBase ptrBase maskBase work depth : ℕ}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pre : List (Finset (Fin (512*h)))) (hk : k ≤ J) (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1 % pMod+lift w.2.1*pMod+shift)-globalKey w.2.2)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdataL : baseL+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ maskBase)
    (hdataR : baseR+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ maskBase)
    (hindex : indexBase+count h k ≤ maskBase) (hptr : ptrBase+count h k ≤ maskBase)
    (hboxesEnd : boxBase+count h k*stride (suffixStage J (512*h) k) boxCut ≤ maskBase)
    (hmasks : maskBase+LightSparseQuery.queryItems (residualSize h J k) t ≤ work)
    (hspace : work+1+tableSize (width h J)+(width h J+1) ≤ lim.space)
    (hpowSpace : work+(2*width h J+2) ≤ lim.space)
    (hemodSpace : work+(Nat.log 2 (LightReportingCatalogLookup.valueBound (width h J) (count h k)+1)+2) ≤ lim.space)
    (hword : (((width h J+1)*2^(width h J+1) : ℕ) : ℤ) ≤ lim.word)
    (hlookupWord : (LightReportingCatalogLookup.word (width h J) (count h k) : ℤ) ≤ lim.word)
    (hvalueWord : (LightSparseQuery.magnitudeBound (suffixStage J (512*h) k) (suffixStage J (512*h) k)
      (residualSize h J k) t B.card C.card : ℤ) ≤ lim.word)
    (ht : t ≤ residualSize h J k+1) (hboxCut : boxCut ≤ residualSize h J k)
    (hflags : residualSize h J k-t ≤ boxCut)
    (hstoredL : LightZetaStages.StoredThrough μ baseL (sourceCut h J)
      (leftSource pMod B b w.2.2) (width h J))
    (hstoredR : LightZetaStages.StoredThrough μ baseR (sourceCut h J)
      (rightSource pMod shift C c w.2.2) (width h J))
    (hindexData : ∃ S : List ℤ, Seg μ indexBase S ∧
      S.Perm (ReportingHostPackedCatalog.codes (ReportingHostPackedCatalog.prefixKey h J k) (count h k)) ∧
      S.Pairwise (· ≤ ·))
    (hptrs : SegN μ ptrBase (List.ofFn fun i : Fin (count h k) =>
      boxBase+i.val*stride (suffixStage J (512*h) k) boxCut))
    (hboxes : ∀ i < count h k, LightBoxStages.StoredThrough μ
      (boxBase+i*stride (suffixStage J (512*h) k) boxCut) boxCut
      (leafWeight (block_fit hk) (leftSource pMod B b w.2.2) (rightSource pMod shift C c w.2.2)
        (suffixStage J (512*h) k) (preL h J k i) (preR h J k i))
      (suffixStage J (512*h) k))
    (hd : depth+2*width h J+12 ≤ lim.depth) :
    Meets lim program 35 depth
      [width h J,sourceCut h J,suffixStage J (512*h) k,k*h,
        subsetMask (leftPrefix k (prefixRows (J := J) pre)),k*h,
        subsetMask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) pre)),
        suffixStage J (512*h) k,k*(512*h),residualSize h J k,subsetMask (querySet k (outputRows w.2.2)),
        t,baseL,baseR,boxCut,indexBase,ptrBase,count h k,maskBase,work]
      μ (time h J k t)
      (fun r μ' =>
        r = (prefixQuery (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k pre : ℤ) ∧
        KeptBut μ μ' work maskBase (LightSparseQuery.queryItems (residualSize h J k) t)) := by
  obtain ⟨i,hi,hL,hR⟩ := original_index hk w.2.2 pre hp
  obtain ⟨S,hseg,hperm,hsorted⟩ := hindexData
  have hEnd := selected_box_end hi hboxesEnd
  have hstoredBox := selected_box hk pMod shift B C b c (outputOccurrences w.2.2) w.2.2 pre
    rfl hi hL hR hboxes
  have hreadPtr : μ (ptrBase+i) = (boxBase+i*stride (suffixStage J (512*h) k) boxCut : ℕ) := by
    have hp := hptrs.getElem (i := i) (by simpa only [List.length_ofFn] using hi)
    simpa only [List.getElem_ofFn,Nat.cast_add,Nat.cast_mul] using hp
  apply Meets.of_body (p := 35) (by rfl : program[35]? = some (body 3 34))
  unfold body time
  have hl := ((LightReportingCatalogLookup.program_meets (d := depth+1) (μ := μ)
    (fun j => subsetMask (preL h J k j)) (fun j => subsetMask (preR h J k j)) hi
    hw (hindex.trans (by omega)) hpowSpace hemodSpace hlookupWord
    (ReportingHostPackedCatalog.prefix_count_le_pow hk)
    (fun j _ => (subsetMask_isMask (preL h J k j)).1)
    (fun j _ => (subsetMask_isMask (preR h J k j)).1)
    (ReportingHostPackedCatalog.prefixKey_unique hk) hperm hsorted hseg (by omega)).append
      (LightReportingSuffixQueryHost.program.map
        (ReportingHostRelocation.relocate LightReportingCatalogLookup.program.length))).append [body 3 34]
  rw [hL,hR] at hl
  light_call hl using LightReportingCatalogLookup.time,LightReportingSuffixQueryHost.time
    with index μ₁ ⟨hfound,hkeepLookup⟩
  have hread : μ₁ (ptrBase+i) = (boxBase+i*stride (suffixStage J (512*h) k) boxCut : ℕ) :=
    (hkeepLookup _ (by omega)).trans hreadPtr
  light_set (boxBase+i*stride (suffixStage J (512*h) k) boxCut : ℕ)
    using hfound,hread,LightReportingCatalogLookup.time,LightReportingSuffixQueryHost.time
  have hsourceL := LightSignedLeafBatch.storedThrough_of_on hstoredL
    (by intro j _ hj; exact hkeepLookup j ((hj.trans_le hdataL).trans_le (by omega)))
  have hsourceR := LightSignedLeafBatch.storedThrough_of_on hstoredR
    (by intro j _ hj; exact hkeepLookup j ((hj.trans_le hdataR).trans_le (by omega)))
  have hlocalBox := ReportingHostQueryBounds.boxStored_of_on hstoredBox
    (by intro j _ hj; exact hkeepLookup j (by omega))
  have hq := (ReportingHostRelocation.meets
    (LightReportingSuffixQueryIndexed.program_meets (depth := depth+1) (μ := μ₁)
      pMod shift A B C a b c w pre hk hp hkey hw hdataL hdataR hEnd hmasks hspace
      hword hvalueWord ht hboxCut hflags hsourceL hsourceR hlocalBox (by omega))
    LightReportingCatalogLookup.program).append [body 3 34]
  light_call hq using LightReportingCatalogLookup.time,LightReportingSuffixQueryHost.time
    with result μ₂ ⟨hresult,hkeepQuery⟩
  refine ⟨hresult,?_⟩
  intro j hj
  exact (hkeepQuery j hj).trans (hkeepLookup j hj.1)

theorem time_bound {h J k t : ℕ} (hk : k ≤ J) (ht : t ≤ residualSize h J k+1) :
    time h J k t ≤
      20000*(width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J k) t+1) := by
  have hl := ReportingHostCatalogIndexCosts.prefix_lookup_time_le (h := h) hk
  have hq := LightReportingSuffixQueryIndexed.time_bound (h := h) (J := J) (k := k) ht
  have hbase : width h J+1 ≤ (width h J+1)^3 := Nat.le_self_pow (by omega) _
  have hm : (width h J+1)^3 ≤ (width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J k) t+1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hpos : 1 ≤ (width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J k) t+1) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  change LightReportingCatalogLookup.time (width h J) (count h k) ≤ 1000*(width h J+1) at hl
  unfold time
  nlinarith

end ThreeSum.LightReportingCatalogQuery
