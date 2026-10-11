import Submission.ThreeSum.LightReportingPrefixArrays
import Submission.ThreeSum.ReportingHostPrefixOrder
import Submission.ThreeSum.ReportingHostRelocation
import Submission.ThreeSum.LightReportingSuffixCatalogSetup

/-!
# Actual complete shared prefix catalog from the original source tables

A single closed program constructs every aligned prefix-mask pair, reads its
computed count header, and builds all local suffix box tables. The original
record order is exact; no supplied enumeration, count, or table pointer is
used as an algorithmic oracle.
-/

namespace ThreeSum.LightReportingPrefixCatalog

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPrefixCatalog ReportingHostPrefixOrder ReportingHostSuffix
open LightReportingSuffixCatalog

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

variable {lim : Limits}

def count (h k : ℕ) : ℕ := (LightReportingPrefixArrays.localCount (512*h) h)^k

def body (pPrefixes pCatalog : ℕ) : Stmt :=
  .call pPrefixes [v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 19] 20 ;;
  .set 21 (M (v 20)) ;;
  .set 22 (v 20 -' v 14) ;;
  .set 23 (v 15 +' v 22) ;;
  .set 24 (v 20 +' k 1) ;;
  .set 25 (v 23 +' k 1) ;;
  .set 26 (v 10 *' v 9) ;;
  .call pCatalog [v 0,v 1,v 2,v 3,v 26,v 26,v 4,v 5,v 6,v 7,v 24,v 25,v 21,
    v 16,v 17,v 18,v 19] 27 ;;
  .set 0 (v 20)

def program : Program :=
  ReportingHostRelocation.program LightReportingPrefixArrays.program LightReportingSuffixCatalogSetup.program ++
    [body 10 42]

def time (h J k boxCut : ℕ) : ℕ :=
  LightReportingPrefixArrays.time (512*h) h k+
    LightReportingSuffixCatalogSetup.time (J*(512*h)) ((J-k)*(512*h)) boxCut (k*(512*h)) (count h k)+500

theorem count_eq_length (h k : ℕ) : count h k = (prefixes h k).length :=
  (prefixes_length h k).symm

theorem count_pos (h k : ℕ) : 0 < count h k := by
  exact Nat.pow_pos (Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega)))

theorem readL {h J k a : ℕ} {μ : ℕ → ℤ} (hk : k ≤ J)
    (hs : Seg μ a (RadixKeyLists.values ((2^(512*h) : ℕ) : ℤ)
      (ReportingHostPairSegments.leftMasks (512*h) h) k)) :
    ∀ i < count h k, μ (a+i) = (subsetMask (preL h J k i) : ℤ) := by
  rw [ReportingHostPrefixOrder.left_values hk] at hs
  intro i hi
  have hi' : i < (prefixes h k).length := by rwa [← count_eq_length]
  have hh := hs i (by simpa only [leftSets,List.length_map] using hi')
  simpa only [leftSets,List.getElem_map,preL_get hi'] using hh

theorem readR {h J k a : ℕ} {μ : ℕ → ℤ} (hk : k ≤ J)
    (hs : Seg μ a (RadixKeyLists.values ((2^(512*h) : ℕ) : ℤ)
      (ReportingHostPairSegments.rightMasks (512*h) h) k)) :
    ∀ i < count h k, μ (a+i) = (subsetMask (preR h J k i) : ℤ) := by
  rw [ReportingHostPrefixOrder.right_values hk] at hs
  intro i hi
  have hi' : i < (prefixes h k).length := by rwa [← count_eq_length]
  have hh := hs i (by simpa only [rightSets,List.length_map] using hi')
  simpa only [rightSets,List.getElem_map,preR_get hi'] using hh

theorem program_meets {μ : ℕ → ℤ}
    {h J k cut boxCut baseL baseR srcS pairL pairR stageL stageR ptrBase boxBase maskBase work B D d : ℕ}
    (hk : k ≤ J) (f g : Finset (Fin (J*(512*h))) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hcut : cut ≤ J*(512*h)) (hboxCut : boxCut ≤ (J-k)*(512*h))
    (hdataL : baseL+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ srcS)
    (hdataR : baseR+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ srcS)
    (hS : srcS+(512*h).choose h ≤ pairL)
    (hL : pairL+LightReportingPrefixArrays.localCount (512*h) h ≤ pairR)
    (hR : pairR+LightReportingPrefixArrays.localCount (512*h) h ≤ stageL)
    (hstageL : LightRadixKeys.space stageL (LightReportingPrefixArrays.localCount (512*h) h) k ≤ stageR)
    (hstageR : LightRadixKeys.space stageR (LightReportingPrefixArrays.localCount (512*h) h) k ≤ ptrBase)
    (hptr : ptrBase+count h k ≤ boxBase)
    (hbox : boxBase+count h k*stride ((J-k)*(512*h)) boxCut ≤ maskBase)
    (hmasks : maskBase+downsetCap ((J-k)*(512*h)) boxCut ≤ work)
    (hpairSpace : work+2*(512*h)+2 ≤ lim.space)
    (hspace : work+1+tableSize (J*(512*h))+(J*(512*h)+1) ≤ lim.space)
    (hpowWord : ((2^(512*h+1) : ℕ) : ℤ) ≤ lim.word)
    (hkeysWord : (LightRadixKeys.word (2^(512*h)) (2^(512*h)) k : ℤ) ≤ lim.word)
    (hword : (((J*(512*h)+1)*2^(J*(512*h)+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^((J-k)*(512*h))*
      ((2^((J-k)*(512*h))*B)*(2^((J-k)*(512*h))*D)) : ℕ) : ℤ) ≤ lim.word)
    (hpre : k*h+boxCut ≤ cut)
    (hf : ∀ S, S.card ≤ cut → |f S| ≤ B) (hg : ∀ S, S.card ≤ cut → |g S| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f (J*(512*h)))
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g (J*(512*h)))
    (hdPair : d+512*h+k+5 ≤ lim.depth) (hd : d+J*(512*h)+14 ≤ lim.depth) :
    Meets lim program 43 d
      [J*(512*h),cut,boxCut,(J-k)*(512*h),(J-k)*(512*h),k*(512*h),baseL,baseR,
        512*h,h,k,srcS,pairL,pairR,stageL,stageR,ptrBase,boxBase,maskBase,work]
      μ (time h J k boxCut)
      (fun r μ' =>
        r = (stageL+LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k : ℕ) ∧
        SegN μ' ptrBase (List.ofFn fun i : Fin (count h k) =>
          boxBase+i.val*stride ((J-k)*(512*h)) boxCut) ∧
        (∀ i < count h k, LightBoxStages.StoredThrough μ'
          (boxBase+i*stride ((J-k)*(512*h)) boxCut) boxCut
          (leafWeight (block_fit hk) f g ((J-k)*(512*h)) (preL h J k i) (preR h J k i))
          ((J-k)*(512*h))) ∧
        LightZetaStages.StoredThrough μ' baseL cut f (J*(512*h)) ∧
        LightZetaStages.StoredThrough μ' baseR cut g (J*(512*h)) ∧
        μ' (stageL+LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k) =
          (count h k : ℤ) ∧
        (∀ i < count h k,
          μ' (stageL+LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k+1+i) =
            (subsetMask (preL h J k i) : ℤ)) ∧
        (∀ i < count h k,
          μ' (stageR+LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k+1+i) =
            (subsetMask (preR h J k i) : ℤ)) ∧
        Kept μ μ' srcS) := by
  have hn := count_pos h k
  have hstageOrder : stageL ≤ stageR := by unfold LightRadixKeys.space at hstageL; omega
  have hptrOrder : stageR ≤ ptrBase := by unfold LightRadixKeys.space at hstageR; omega
  have hprefixEndL : stageL+LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k+1+
      count h k ≤ ptrBase := hstageL.trans hptrOrder
  have hprefixEndR : stageR+LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k+1+
      count h k ≤ ptrBase := hstageR
  have hkhWord : ((k*h : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by omega : k*h ≤ lim.space)).trans hw
  have hkhWordZ : (k : ℤ)*(h : ℤ) ≤ lim.word := by simpa only [Nat.cast_mul] using hkhWord
  have hwidth : (J-k)*(512*h) ≤ J*(512*h) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  apply Meets.of_body (p := 43) (by rfl : program[43]? = some (body 10 42))
  unfold body time
  have hp := ((LightReportingPrefixArrays.program_meets (d := d+1) (μ := μ)
    hw (by omega) hS hL hR hstageL (hstageR.trans (by omega)) hpairSpace hpowWord hkeysWord (by omega)).append
      (LightReportingSuffixCatalogSetup.program.map
        (ReportingHostRelocation.relocate LightReportingPrefixArrays.program.length))).append [body 10 42]
  light_call hp using LightReportingPrefixArrays.time,LightReportingSuffixCatalogSetup.time
    with leftHead μ₁ ⟨hhead,hcountL,hcountR,hleftArray,hrightArray,hkeepArrays⟩
  light_set (count h k : ℕ) using hhead,hcountL,count,
    LightReportingPrefixArrays.time,LightReportingSuffixCatalogSetup.time
  light_set (LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k : ℕ)
    using hhead,LightReportingPrefixArrays.time,LightReportingSuffixCatalogSetup.time
  light_set (stageR+LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k : ℕ)
    using LightReportingPrefixArrays.time,LightReportingSuffixCatalogSetup.time
  light_set (stageL+LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k+1 : ℕ)
    using hhead,LightReportingPrefixArrays.time,LightReportingSuffixCatalogSetup.time
  light_set (stageR+LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k+1 : ℕ)
    using LightReportingPrefixArrays.time,LightReportingSuffixCatalogSetup.time
  light_set (k*h : ℕ) using hkhWord,hkhWordZ,
    LightReportingPrefixArrays.time,LightReportingSuffixCatalogSetup.time
  have hstoredL₁ := LightSignedLeafBatch.storedThrough_of_on hstoredL
    (by intro i _ hi; exact hkeepArrays i (by omega))
  have hstoredR₁ := LightSignedLeafBatch.storedThrough_of_on hstoredR
    (by intro i _ hi; exact hkeepArrays i (by omega))
  have hc := (ReportingHostRelocation.meets
    (LightReportingSuffixCatalogSetup.program_meets (d := d+1) (μ := μ₁)
      (block_fit hk) (preL h J k) (preR h J k) f g hw hcut hboxCut hwidth hn
      (hdataL.trans (by omega)) (hdataR.trans (by omega)) hprefixEndL hprefixEndR hptr hbox hmasks
      hspace hword hvalueWord
      (by intro i hi; exact preL_card hk (by rwa [← count_eq_length]))
      (by intro i hi; exact preR_card hk (by rwa [← count_eq_length]))
      hpre hpre hf hg hstoredL₁ hstoredR₁ (readL hk hleftArray) (readR hk hrightArray) (by omega))
    LightReportingPrefixArrays.program).append [body 10 42]
  light_call hc using count,LightReportingPrefixArrays.time,LightReportingSuffixCatalogSetup.time
    with result μ₂ ⟨hptrs,hboxes,hsourceL,hsourceR,hkeepCatalog⟩
  light_set (stageL+LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k : ℕ)
    using hhead,LightReportingPrefixArrays.time,LightReportingSuffixCatalogSetup.time
  refine ⟨by simp,hptrs,hboxes,hsourceL,hsourceR,?_,?_,?_,?_⟩
  · exact (hkeepCatalog _ (by omega)).trans hcountL
  · intro i hi
    exact (hkeepCatalog _ (by omega)).trans (readL hk hleftArray i hi)
  · intro i hi
    exact (hkeepCatalog _ (by omega)).trans (readR hk hrightArray i hi)
  · intro i hi
    exact (hkeepCatalog i (by omega)).trans (hkeepArrays i hi)

end ThreeSum.LightReportingPrefixCatalog
