import Submission.ThreeSum.LightReportingCatalogBatch
import Submission.ThreeSum.LightReportingFilter

/-! # Actual shared-catalog queries followed by stable positive compaction -/

namespace ThreeSum.LightReportingCatalogLevel

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def body (pBatch pFilter : ℕ) : Stmt :=
  .call pBatch [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,
    v 16,v 17,v 18,v 19,v 20,v 21] 23 ;;
  .call pFilter [v 18,v 19,v 22] 0

def suffix : Program := [LightReportingFilter.body,body 36 37]
def program : Program := LightReportingCatalogBatch.program ++ suffix

def time (h J k t n : ℕ) : ℕ := LightReportingCatalogBatch.time h J k t n+LightReportingFilter.time n+100

theorem program_meets
    {μ : ℕ → ℤ} {h J k t baseL baseR boxCut boxBase indexBase ptrBase inL inR n dst selected maskBase work depth : ℕ}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pres : ℕ → List (Finset (Fin (512*h)))) (hk : k ≤ J)
    (hp : ∀ i < n, ValidPrefix w.2.2 k (pres i))
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1 % pMod+lift w.2.1*pMod+shift)-globalKey w.2.2)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdataL : baseL+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ dst)
    (hdataR : baseR+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ dst)
    (hindex : indexBase+count h k ≤ dst) (hptr : ptrBase+count h k ≤ dst)
    (hboxesEnd : boxBase+count h k*stride (suffixStage J (512*h) k) boxCut ≤ dst)
    (hinL : inL+n ≤ dst) (hinR : inR+n ≤ dst)
    (hdst : dst+n ≤ selected) (hselected : selected+n ≤ maskBase)
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
    (hreadL : ∀ i < n, μ (inL+i) = (subsetMask (leftPrefix k (prefixRows (J := J) (pres i))) : ℤ))
    (hreadR : ∀ i < n, μ (inR+i) =
      (subsetMask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) (pres i))) : ℤ))
    (hd : depth+2*width h J+14 ≤ lim.depth) :
    Meets lim program 38 depth
      [width h J,sourceCut h J,suffixStage J (512*h) k,k*h,k*h,
        suffixStage J (512*h) k,k*(512*h),residualSize h J k,subsetMask (querySet k (outputRows w.2.2)),
        t,baseL,baseR,boxCut,indexBase,ptrBase,count h k,inL,inR,n,dst,maskBase,work,selected]
      μ (time h J k t n)
      (fun r μ' =>
        let counts := fun i => prefixQuery (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k (pres i)
        r = ((LightReportingFilter.selected counts n).length : ℤ) ∧
        SegN μ' selected (LightReportingFilter.selected counts n) ∧
        SegN μ' dst (List.ofFn fun i : Fin n => counts i.val) ∧ Kept μ μ' dst) := by
  let counts := fun i => prefixQuery (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k (pres i)
  have hcountWord (i : ℕ) (hi : i < n) : (counts i : ℤ) ≤ lim.word :=
    ReportingHostSuffixValueBounds.prefix_count_le_word pMod shift A B C a b c w (pres i)
      hk (hp i hi) hkey hvalueWord
  apply Meets.of_body (p := 38) (by rfl : program[38]? = some (body 36 37))
  unfold body time
  have hb := (LightReportingCatalogBatch.program_meets (depth := depth+1) (μ := μ)
    (inL := inL) (inR := inR) (n := n) (dst := dst) (maskBase := maskBase) (work := work)
    pMod shift A B C a b c w pres hk hp hkey hw hdataL hdataR hindex hptr hboxesEnd
    hinL hinR (by omega) hmasks hspace hpowSpace hemodSpace hword hlookupWord hvalueWord
    ht hboxCut hflags hstoredL hstoredR hindexData hptrs hboxes hreadL hreadR (by omega)).append suffix
  light_call hb using LightReportingCatalogBatch.time,LightReportingFilter.time
    with ret μ₁ ⟨hcounts,hkeepBatch⟩
  have hreads (i : ℕ) (hi : i < n) : μ₁ (dst+i) = (counts i : ℤ) := by
    have hs := hcounts.getElem (i := i) (by simpa only [List.length_ofFn] using hi)
    simpa only [List.getElem_ofFn] using hs
  have hf := LightReportingFilter.meets (P := program) (p := 37) (d := depth+1)
    (μ := μ₁) (src := dst) (dst := selected) (n := n) counts rfl hw (by omega) (by omega)
    (Or.inl hdst) hcountWord hreads
  light_call hf using LightReportingCatalogBatch.time,LightReportingFilter.time
    with found μ₂ ⟨hfound,hselectedOut,hkeepFilter⟩
  refine ⟨hfound,hselectedOut,?_,?_⟩
  · exact hcounts.of_sameOutside hkeepFilter (Or.inl (by simpa using hdst))
  · intro i hi
    exact (hkeepFilter i (Or.inl (by omega))).trans (hkeepBatch i ⟨by omega,Or.inl hi⟩)

theorem time_bound {h J k t n : ℕ} (hk : k ≤ J) (ht : t ≤ residualSize h J k+1) :
    time h J k t n ≤
      22000*(width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J k) t+1)*(n+1) := by
  have hq := LightReportingCatalogBatch.time_bound (n := n) hk ht
  have hp : 1 ≤ (width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J k) t+1) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold time LightReportingFilter.time
  nlinarith [Nat.mul_le_mul_right (n+1) hp]

end ThreeSum.LightReportingCatalogLevel
