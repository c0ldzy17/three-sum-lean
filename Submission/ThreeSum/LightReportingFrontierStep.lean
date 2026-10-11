import Submission.ThreeSum.LightReportingPositiveExpand
import Submission.ThreeSum.ReportingHostPositiveBatch

/-!
# Actual multi-parent reporting frontier step

The loop reads each stored parent mask pair, executes the complete positive
expansion, and appends only the returned positive masks to aligned output
arrays. The accumulated output is the literal ordered concatenation used by
the original raw-incidence reporting frontier.
-/

namespace ThreeSum.LightReportingFrontierStep

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockIndex BlockMaskLayout BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
open ReportingHostMasks LightBlockChildrenIndexed ReportingHostPositive ReportingHostPositiveBatch
open LightReportingPositiveExpand

set_option maxHeartbeats 3500000
set_option maxRecDepth 10000

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def roundBody (pExpand : ℕ) : Stmt :=
  .set 31 (M (v 24 +' v 30)) ;;
  .set 32 (M (v 25 +' v 30)) ;;
  .call pExpand [v 0,v 1,v 2,v 31,v 32,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,
    v 13,v 14,v 15,v 16,v 17,v 18,v 19,v 20,v 21,v 22,v 23,v 27 +' v 29,v 28 +' v 29] 33 ;;
  .set 29 (v 29 +' v 33)

def body (pExpand : ℕ) : Stmt :=
  .set 29 (k 0) ;; .for 30 (v 26) (roundBody pExpand) ;; .set 0 (v 29)

def program : Program := LightReportingPositiveExpand.program ++ [body 49]
def time (h J k t n : ℕ) : ℕ := n*(LightReportingPositiveExpand.time h J k t+200)+100

def Inv {h J k : ℕ} (μ : ℕ → ℤ) (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (pres : List (List (Finset (Fin (512*h))))) (hk : k < J)
    (t baseL baseR boxCut indexBase ptrBase inL inR outL outR masks dstL dstR dst selected maskBase work j : ℕ)
    (σ : State) : Prop :=
  ∃ (a b r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame (([width h J,h,rowMask (outputRows w.2.2) ⟨k,hk⟩,subsetMask (querySet k (outputRows w.2.2)),
      masks,dstL,dstR,work,sourceCut h J,suffixStage J (512*h) (k+1),(k+1)*h,residualSize h J (k+1),
      t,baseL,baseR,boxCut,indexBase,ptrBase,count h (k+1),groupSize h,dst,selected,maskBase,(k+1)*(512*h),
      inL,inR,pres.length,outL,outR,(through I w pres hk j).length,j] : List ℕ).map
      (fun n => (n : ℤ)) ++ [a,b,r]),ν⟩ ∧
    SegN ν outL ((through I w pres hk j).map fun pre => subsetMask (leftPrefix (k+1) (prefixRows (J := J) pre))) ∧
    SegN ν outR ((through I w pres hk j).map fun pre =>
      subsetMask (rightPrefix (k+1) (outputRows w.2.2) (prefixRows (J := J) pre))) ∧
    KeptOutputs μ ν masks outL outR (through I w pres hk j).length

theorem program_meets
    {μ : ℕ → ℤ} {h J k t baseL baseR boxCut boxBase indexBase ptrBase inL inR outL outR masks dstL dstR dst selected maskBase work depth : ℕ}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pres : List (List (Finset (Fin (512*h))))) (hk : k < J)
    (hp : ∀ pre ∈ pres, ValidPrefix w.2.2 k pre)
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1 % pMod+lift w.2.1*pMod+shift)-globalKey w.2.2)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdataL : baseL+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ outL)
    (hdataR : baseR+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ outL)
    (hindex : indexBase+count h (k+1) ≤ outL) (hptr : ptrBase+count h (k+1) ≤ outL)
    (hboxesEnd : boxBase+count h (k+1)*stride (suffixStage J (512*h) (k+1)) boxCut ≤ outL)
    (hinL : inL+pres.length ≤ outL) (hinR : inR+pres.length ≤ outL)
    (houtL : outL+pres.length*groupSize h ≤ outR) (houtR : outR+pres.length*groupSize h ≤ masks)
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
    (hparentsL : SegN μ inL (pres.map fun pre => subsetMask (leftPrefix k (prefixRows (J := J) pre))))
    (hparentsR : SegN μ inR (pres.map fun pre =>
      subsetMask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) pre))))
    (hd : depth+2*width h J+17 ≤ lim.depth) :
    Meets lim program 50 depth
      [width h J,h,rowMask (outputRows w.2.2) ⟨k,hk⟩,subsetMask (querySet k (outputRows w.2.2)),
        masks,dstL,dstR,work,sourceCut h J,suffixStage J (512*h) (k+1),(k+1)*h,residualSize h J (k+1),
        t,baseL,baseR,boxCut,indexBase,ptrBase,count h (k+1),groupSize h,dst,selected,maskBase,(k+1)*(512*h),
        inL,inR,pres.length,outL,outR]
      μ (time h J k t pres.length)
      (fun r ν =>
        let next := pres.flatMap (fun pre => positiveChildren (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w pre hk)
        r = (next.length : ℤ) ∧
        SegN ν outL (next.map fun pre => subsetMask (leftPrefix (k+1) (prefixRows (J := J) pre))) ∧
        SegN ν outR (next.map fun pre =>
          subsetMask (rightPrefix (k+1) (outputRows w.2.2) (prefixRows (J := J) pre))) ∧
        KeptOutputs μ ν masks outL outR next.length) := by
  let I := rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c
  obtain ⟨S,hseg,hperm,hsorted⟩ := hindexData
  have hlenS := hperm.length_eq.trans (ReportingHostPackedCatalog.codes_length _ _)
  have hGpos : 0 < groupSize h := Nat.choose_pos (by omega)
  have hNspace : pres.length ≤ lim.space :=
    (Nat.le_mul_of_pos_right _ hGpos).trans (by omega)
  have hmask (U : Finset (Fin (width h J))) : (subsetMask U : ℤ) ≤ lim.word := by
    have hpow : (2^(width h J) : ℕ) ≤ (width h J+1)*2^(width h J+1) :=
      (Nat.pow_le_pow_right (by decide) (by omega)).trans (Nat.le_mul_of_pos_left _ (by omega))
    exact (Int.ofNat_le.mpr ((subsetMask_isMask U).1.le.trans hpow)).trans hword
  apply Meets.of_body (p := 50) (by rfl : program[50]? = some (body 49))
  unfold body time
  light_set (0 : ℕ) using LightReportingPositiveExpand.time
  refine Ends.pieceThen (Ends.for (lim := lim) (P := program) (d := depth) (i := 30) (hi := v 26)
    (body := roundBody 49) (T := pres.length*(LightReportingPositiveExpand.time h J k t+180)+30)
    (Q := Inv μ I w pres hk t baseL baseR boxCut indexBase ptrBase inL inR outL outR masks dstL dstR dst selected maskBase work pres.length)
    (Inv μ I w pres hk t baseL baseR boxCut indexBase ptrBase inL inR outL outR masks dstL dstR dst selected maskBase work)
    pres.length (LightReportingPositiveExpand.time h J k t+160) ?start ?round ?done ?bound
    (hT := by light_time)) ?after
  case start =>
    refine ⟨0,0,0,μ,?_,?_,?_,SameOn.refl⟩
    · simp [update_frame_setLocal,through_zero]
      exact (frame_append_zeros _ 3).symm
    · simp [through_zero,SegN]
    · simp [through_zero,SegN]
  case round =>
    rintro j _ hj _ ⟨left,right,ret,ν,rfl,houtLeft,houtRight,hkeep⟩
    have hlen := through_length_le (j := j) I w pres hk
    have hmul := Nat.mul_le_mul_right (groupSize h) (show j+1 ≤ pres.length by omega)
    have hcap : (through I w pres hk j).length+groupSize h ≤ pres.length*groupSize h := by
      simp only [Nat.add_mul,Nat.one_mul] at hmul
      omega
    have hGcap : groupSize h ≤ pres.length*groupSize h :=
      Nat.le_mul_of_pos_left _ (by omega)
    have hreadBelow (i : ℕ) (hi : i < outL) : ν i = μ i :=
      hkeep i ⟨by omega,Or.inl hi,Or.inl (by omega)⟩
    have hreadL : ν (inL+j) = (subsetMask (leftPrefix k (prefixRows (J := J) (parentAt pres j))) : ℤ) := by
      rw [hreadBelow _ (by omega),parentAt_eq_get pres hj]
      have hh := hparentsL.getElem (i := j) (by simpa only [List.length_map] using hj)
      simpa only [List.getElem_map] using hh
    have hreadR : ν (inR+j) =
        (subsetMask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) (parentAt pres j))) : ℤ) := by
      rw [hreadBelow _ (by omega),parentAt_eq_get pres hj]
      have hh := hparentsR.getElem (i := j) (by simpa only [List.length_map] using hj)
      simpa only [List.getElem_map] using hh
    have hlword := hmask (leftPrefix k (prefixRows (J := J) (parentAt pres j)))
    have hrword := hmask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) (parentAt pres j)))
    have hsourceL := LightSignedLeafBatch.storedThrough_of_on hstoredL
      (by intro i _ hi; exact hreadBelow i (hi.trans_le hdataL))
    have hsourceR := LightSignedLeafBatch.storedThrough_of_on hstoredR
      (by intro i _ hi; exact hreadBelow i (hi.trans_le hdataR))
    have hindexData' : ∃ S : List ℤ, Seg ν indexBase S ∧
        S.Perm (ReportingHostPackedCatalog.codes (ReportingHostPackedCatalog.prefixKey h J (k+1)) (count h (k+1))) ∧
        S.Pairwise (· ≤ ·) := by
      refine ⟨S,?_,hperm,hsorted⟩
      intro i hi
      exact (hreadBelow _ (by rw [hlenS] at hi; omega)).trans (hseg i hi)
    have hptrs' : SegN ν ptrBase (List.ofFn fun i : Fin (count h (k+1)) =>
        boxBase+i.val*stride (suffixStage J (512*h) (k+1)) boxCut) := by
      intro i hi
      have hi' : i < count h (k+1) := by simpa only [List.length_map,List.length_ofFn] using hi
      exact (hreadBelow _ (by omega)).trans (hptrs i hi)
    have hboxes' (i : ℕ) (hi : i < count h (k+1)) :=
      ReportingHostQueryBounds.boxStored_of_on (hboxes i hi) (by
        intro u _ hu
        exact hreadBelow u (hu.trans_le (ReportingHostCatalogSelection.selected_box_end hi hboxesEnd)))
    unfold roundBody
    light_set (subsetMask (leftPrefix k (prefixRows (J := J) (parentAt pres j))) : ℕ)
      using hreadL,LightReportingPositiveExpand.time
    light_set (subsetMask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) (parentAt pres j))) : ℕ)
      using hreadR,LightReportingPositiveExpand.time
    have he := (LightReportingPositiveExpand.program_meets (depth := depth+1) (μ := ν) (k := k)
      (outL := outL+(through I w pres hk j).length) (outR := outR+(through I w pres hk j).length)
      pMod shift A B C a b c w (parentAt pres j) hk (parentAt_valid w.2.2 pres hp hj) hkey hw
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hmasks hleft hright hdst hselected hqueryMasks hspace hpowSpace hemodSpace hword hlookupWord
      hvalueWord ht hboxCut hflags hsourceL hsourceR hindexData' hptrs' hboxes' (by omega)).append [body 49]
    light_call he using LightReportingPositiveExpand.time with found ν₂ ⟨hfound,hnewLeft,hnewRight,hkeepNew⟩
    change found = ((positiveChildren I w (parentAt pres j) hk).length : ℤ) at hfound
    change KeptOutputs ν ν₂ masks (outL+(through I w pres hk j).length)
      (outR+(through I w pres hk j).length) (positiveChildren I w (parentAt pres j) hk).length at hkeepNew
    have hstep := through_succ I w pres hk hj
    have hnextLen : (through I w pres hk (j+1)).length =
        (through I w pres hk j).length+(positiveChildren I w (parentAt pres j) hk).length := by
      rw [hstep,List.length_append]
    have hnextCap : (through I w pres hk (j+1)).length ≤ pres.length*groupSize h :=
      (through_length_le I w pres hk).trans hmul
    light_set ((through I w pres hk (j+1)).length : ℕ)
      using hfound,hnextLen,LightReportingPositiveExpand.time
    refine ⟨by simp,(subsetMask (leftPrefix k (prefixRows (J := J) (parentAt pres j))) : ℤ),
      (subsetMask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) (parentAt pres j))) : ℤ),found,
      ν₂,?_,?_,?_,?_⟩
    · simp [update_frame_setLocal]
    · change Seg ν₂ outL (((through I w pres hk (j+1)).map fun pre =>
        subsetMask (leftPrefix (k+1) (prefixRows (J := J) pre))).map fun x : ℕ => (x : ℤ))
      rw [hstep,List.map_append,List.map_append,seg_append]
      refine ⟨?_,?_⟩
      · apply houtLeft.congr
        intro i hi
        have hi' : i < (through I w pres hk j).length := by simpa only [List.length_map] using hi
        exact hkeepNew _ ⟨by omega,Or.inl (by omega),Or.inl (by omega)⟩
      · simpa only [List.length_map] using hnewLeft
    · change Seg ν₂ outR (((through I w pres hk (j+1)).map fun pre =>
        subsetMask (rightPrefix (k+1) (outputRows w.2.2) (prefixRows (J := J) pre))).map fun x : ℕ => (x : ℤ))
      rw [hstep,List.map_append,List.map_append,seg_append]
      refine ⟨?_,?_⟩
      · apply houtRight.congr
        intro i hi
        have hi' : i < (through I w pres hk j).length := by simpa only [List.length_map] using hi
        exact hkeepNew _ ⟨by omega,Or.inr (by omega),Or.inl (by omega)⟩
      · simpa only [List.length_map] using hnewRight
    · intro i hi
      rw [hnextLen] at hi
      apply (hkeepNew i ⟨hi.1,?_,?_⟩).trans
      · exact hkeep i ⟨hi.1,by rcases hi.2.1 with h | h <;> omega,by rcases hi.2.2 with h | h <;> omega⟩
      · rcases hi.2.1 with h | h <;> omega
      · rcases hi.2.2 with h | h <;> omega
  case done =>
    intro σ _ hs
    exact hs
  case bound =>
    rintro j _ hj _ ⟨left,right,ret,ν,rfl,_,_,_⟩
    light_side
  case after =>
    rintro _ ⟨left,right,ret,ν,rfl,houtLeft,houtRight,hkeep⟩
    have hlen := through_length_le (j := pres.length) I w pres hk
    light_set ((through I w pres hk pres.length).length : ℕ) using LightReportingPositiveExpand.time
    have he := through_all I w pres hk
    refine ⟨by simp [he,I],?_,?_,?_⟩
    · simpa only [he] using houtLeft
    · simpa only [he] using houtRight
    · simpa only [he] using hkeep

theorem time_bound {h J k t n : ℕ} (hk : k < J) (ht : t ≤ residualSize h J (k+1)+1) :
    time h J k t n ≤
      27000*(width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J (k+1)) t+1)*(groupSize h+1)*(n+1) := by
  have he := LightReportingPositiveExpand.time_bound hk ht
  have hp : 1 ≤ (width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J (k+1)) t+1)*(groupSize h+1) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold time
  nlinarith [Nat.mul_le_mul_left n he]

end ThreeSum.LightReportingFrontierStep
