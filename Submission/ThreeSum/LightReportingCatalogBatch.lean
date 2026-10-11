import Submission.ThreeSum.LightReportingCatalogQuery
import Submission.ThreeSum.ReportingHostSuffixValueBounds

/-!
# Actual raw-count batching through the physical suffix-box catalog

Each candidate supplies only its two constructed prefix masks. A real sorted
lookup chooses its cached suffix box, and the actual sparse query stores the
original raw prefix count. The catalog is shared and preserved by all calls.
-/

namespace ThreeSum.LightReportingCatalogBatch

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog

set_option maxHeartbeats 2200000
set_option maxRecDepth 8000

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def roundBody (pQuery : ℕ) : Stmt :=
  .set 23 (M (v 16 +' v 22)) ;;
  .set 24 (M (v 17 +' v 22)) ;;
  .call pQuery [v 0,v 1,v 2,v 3,v 23,v 4,v 24,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,
    v 13,v 14,v 15,v 20,v 21] 25 ;;
  .store (v 19 +' v 22) (v 25)

def body (pQuery : ℕ) : Stmt := .for 22 (v 18) (roundBody pQuery)

def program : Program := LightReportingCatalogQuery.program ++ [body 35]

def time (h J k t n : ℕ) : ℕ := n*(LightReportingCatalogQuery.time h J k t+180)+30

def Inv (μ : ℕ → ℤ) (counts : ℕ → ℕ)
    (h J k t Qmask baseL baseR boxCut indexBase ptrBase inL inR n dst maskBase work j : ℕ)
    (σ : State) : Prop :=
  ∃ (a b r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [width h J,sourceCut h J,suffixStage J (512*h) k,k*h,k*h,
      suffixStage J (512*h) k,k*(512*h),residualSize h J k,Qmask,t,baseL,baseR,
      boxCut,indexBase,ptrBase,count h k,inL,inR,n,dst,maskBase,work,j,a,b,r],μ'⟩ ∧
    (∀ i < j, μ' (dst+i) = (counts i : ℤ)) ∧ KeptBut μ μ' maskBase dst n

theorem program_meets
    {μ : ℕ → ℤ} {h J k t baseL baseR boxCut boxBase indexBase ptrBase inL inR n dst maskBase work depth : ℕ}
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
    (hinL : inL+n ≤ dst) (hinR : inR+n ≤ dst) (hdst : dst+n ≤ maskBase)
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
    (hd : depth+2*width h J+13 ≤ lim.depth) :
    Meets lim program 36 depth
      [width h J,sourceCut h J,suffixStage J (512*h) k,k*h,k*h,
        suffixStage J (512*h) k,k*(512*h),residualSize h J k,subsetMask (querySet k (outputRows w.2.2)),
        t,baseL,baseR,boxCut,indexBase,ptrBase,count h k,inL,inR,n,dst,maskBase,work]
      μ (time h J k t n)
      (fun _ μ' => SegN μ' dst (List.ofFn fun i : Fin n =>
          prefixQuery (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k (pres i.val)) ∧
        KeptBut μ μ' maskBase dst n) := by
  let counts := fun i => prefixQuery (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k (pres i)
  obtain ⟨S,hseg,hperm,hsorted⟩ := hindexData
  have hlen : S.length = count h k := hperm.length_eq.trans (ReportingHostPackedCatalog.codes_length _ _)
  have hmask (U : Finset (Fin (width h J))) : (subsetMask U : ℤ) ≤ lim.word := by
    have hpow : (2^(width h J) : ℕ) ≤ (width h J+1)*2^(width h J+1) :=
      (Nat.pow_le_pow_right (by decide) (by omega)).trans (Nat.le_mul_of_pos_left _ (by omega))
    exact (Int.ofNat_le.mpr ((subsetMask_isMask U).1.le.trans hpow)).trans hword
  apply Meets.of_body (p := 36) (by rfl : program[36]? = some (body 35))
  unfold body time
  refine Ends.for (lim := lim) (P := program) (d := depth) (i := 22) (hi := v 18) (body := roundBody 35)
    (Inv μ counts h J k t (subsetMask (querySet k (outputRows w.2.2)))
      baseL baseR boxCut indexBase ptrBase inL inR n dst maskBase work)
    n (LightReportingCatalogQuery.time h J k t+150) ?start ?round ?done ?bound (hT := by light_time)
  case start =>
    refine ⟨0,0,0,μ,?_,by simp,SameOn.refl⟩
    simp [update_frame_setLocal]
    change frame ([(width h J : ℤ),sourceCut h J,suffixStage J (512*h) k,k*h,k*h,
      suffixStage J (512*h) k,k*(512*h),residualSize h J k,subsetMask (querySet k (outputRows w.2.2)),
      t,baseL,baseR,boxCut,indexBase,ptrBase,count h k,inL,inR,n,dst,maskBase,work,0]) =
      frame ([(width h J : ℤ),sourceCut h J,suffixStage J (512*h) k,k*h,k*h,
        suffixStage J (512*h) k,k*(512*h),residualSize h J k,subsetMask (querySet k (outputRows w.2.2)),
        t,baseL,baseR,boxCut,indexBase,ptrBase,count h k,inL,inR,n,dst,maskBase,work,0] ++ [0,0,0])
    exact (frame_append_zeros _ 3).symm
  case round =>
    rintro j _ hj _ ⟨left,right,result,μ',rfl,hout,hkeep⟩
    have hkread (z : ℕ) (hz : z < dst) : μ' z = μ z := hkeep z ⟨by omega,Or.inl hz⟩
    have hlread := (hkread (inL+j) (by omega)).trans (hreadL j hj)
    have hrread := (hkread (inR+j) (by omega)).trans (hreadR j hj)
    have hlword := hmask (leftPrefix k (prefixRows (J := J) (pres j)))
    have hrword := hmask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) (pres j)))
    have hsourceL := LightSignedLeafBatch.storedThrough_of_on hstoredL
      (by intro z _ hz; exact hkread z (hz.trans_le hdataL))
    have hsourceR := LightSignedLeafBatch.storedThrough_of_on hstoredR
      (by intro z _ hz; exact hkread z (hz.trans_le hdataR))
    have hindexData' : ∃ S : List ℤ, Seg μ' indexBase S ∧
        S.Perm (ReportingHostPackedCatalog.codes (ReportingHostPackedCatalog.prefixKey h J k) (count h k)) ∧
        S.Pairwise (· ≤ ·) := by
      refine ⟨S,?_,hperm,hsorted⟩
      intro z hz
      exact (hkread _ (by rw [hlen] at hz; omega)).trans (hseg z hz)
    have hptrs' : SegN μ' ptrBase (List.ofFn fun i : Fin (count h k) =>
        boxBase+i.val*stride (suffixStage J (512*h) k) boxCut) := by
      intro z hz
      have hz' : z < count h k := by simpa only [List.length_map,List.length_ofFn] using hz
      exact (hkread _ (by omega)).trans (hptrs z hz)
    have hboxes' (z : ℕ) (hz : z < count h k) :=
      ReportingHostQueryBounds.boxStored_of_on (hboxes z hz) (by
        intro u _ hu
        exact hkread u (hu.trans_le (ReportingHostCatalogSelection.selected_box_end hz hboxesEnd)))
    have hv := ReportingHostSuffixValueBounds.prefix_count_le_word pMod shift A B C a b c w (pres j)
      hk (hp j hj) hkey hvalueWord
    change (counts j : ℤ) ≤ lim.word at hv
    unfold roundBody
    light_set (subsetMask (leftPrefix k (prefixRows (J := J) (pres j))) : ℕ)
      using hlread,LightReportingCatalogQuery.time
    light_set (subsetMask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) (pres j))) : ℕ)
      using hrread,LightReportingCatalogQuery.time
    have hquery := (LightReportingCatalogQuery.program_meets (depth := depth+1) (μ := μ')
      pMod shift A B C a b c w (pres j) hk (hp j hj) hkey hw
      (by omega) (by omega) (by omega) (by omega) (by omega) hmasks hspace hpowSpace hemodSpace
      hword hlookupWord hvalueWord ht hboxCut hflags hsourceL hsourceR hindexData' hptrs' hboxes'
      (by omega)).append [body 35]
    light_call hquery using LightReportingCatalogQuery.time with value ν ⟨hvalue,hkeepQ⟩
    change value = (counts j : ℤ) at hvalue
    light_store (dst+j) (counts j : ℤ) using hvalue,LightReportingCatalogQuery.time
    refine ⟨by simp,(subsetMask (leftPrefix k (prefixRows (J := J) (pres j))) : ℤ),
      (subsetMask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) (pres j))) : ℤ),value,
      Function.update ν (dst+j) (counts j : ℤ),?_,?_,?_⟩
    · simp [update_frame_setLocal]
    · intro z hz
      by_cases he : z = j
      · subst z; simp
      · have hzj : z < j := by omega
        rw [Function.update_of_ne (by omega),hkeepQ (dst+z) ⟨by omega,Or.inl (by omega)⟩]
        exact hout z hzj
    · intro z hz
      rw [Function.update_of_ne (by rcases hz.2 with h | h <;> omega)]
      exact (hkeepQ z ⟨by omega,Or.inl hz.1⟩).trans (hkeep z hz)
  case done =>
    rintro _ _ ⟨left,right,result,μ',rfl,hout,hkeep⟩
    refine ⟨?_,hkeep⟩
    intro j hj
    have hj' : j < n := by simpa only [List.length_map,List.length_ofFn] using hj
    have hh := hout j hj'
    simpa only [List.getElem_map,List.getElem_ofFn] using hh
  case bound =>
    rintro j _ hj _ ⟨left,right,result,μ',rfl,_,_⟩
    light_side

theorem time_bound {h J k t n : ℕ} (hk : k ≤ J) (ht : t ≤ residualSize h J k+1) :
    time h J k t n ≤
      21000*(width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J k) t+1)*(n+1) := by
  have hq := LightReportingCatalogQuery.time_bound hk ht
  have hp : 1 ≤ (width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J k) t+1) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold time
  nlinarith [Nat.mul_le_mul_left n hq]

end ThreeSum.LightReportingCatalogBatch
