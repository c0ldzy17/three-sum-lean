import Submission.ThreeSum.LightReportingPrefixCatalog
import Submission.ThreeSum.LightReportingSortedCatalog

/-!
# Complete actual suffix catalog with a sorted physical lookup index

The returned header and both array addresses are obtained from the previous
actual constructor. The program then constructs the sorted packed index,
retaining every original box pointer and source/table cell.
-/

namespace ThreeSum.LightReportingCatalogIndex

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPrefixOrder ReportingHostSuffix LightReportingSuffixCatalog
open LightReportingPrefixCatalog

set_option maxHeartbeats 1500000
set_option maxRecDepth 8000

variable {lim : Limits}

def body (pCatalog pIndex : ℕ) : Stmt :=
  .call pCatalog [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,
    v 14,v 15,v 16,v 17,v 18,v 19] 21 ;;
  .set 22 (M (v 21)) ;;
  .set 23 (v 21 -' v 14) ;;
  .set 24 (v 15 +' v 23 +' k 1) ;;
  .set 25 (v 21 +' k 1) ;;
  .call pIndex [v 0,v 25,v 24,v 22,v 20,v 19] 26 ;;
  .set 0 (v 21)

def program : Program :=
  ReportingHostRelocation.program LightReportingPrefixCatalog.program LightReportingSortedCatalog.program ++
    [body 43 50]

def time (h J k boxCut : ℕ) : ℕ := LightReportingPrefixCatalog.time h J k boxCut+
  LightReportingSortedCatalog.time (J*(512*h)) (count h k)+250

theorem program_meets {μ : ℕ → ℤ}
    {h J k cut boxCut baseL baseR srcS pairL pairR stageL stageR ptrBase boxBase maskBase indexBase work B D d : ℕ}
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
    (hindex : maskBase ≤ indexBase) (hindexEnd : indexBase+count h k ≤ work)
    (hpairSpace : work+2*(512*h)+2 ≤ lim.space)
    (hspace : work+1+tableSize (J*(512*h))+(J*(512*h)+1) ≤ lim.space)
    (hsortSpace : work+count h k ≤ lim.space)
    (hpowWord : ((2^(512*h+1) : ℕ) : ℤ) ≤ lim.word)
    (hkeysWord : (LightRadixKeys.word (2^(512*h)) (2^(512*h)) k : ℤ) ≤ lim.word)
    (hword : (((J*(512*h)+1)*2^(J*(512*h)+1) : ℕ) : ℤ) ≤ lim.word)
    (hindexWord : (LightReportingSortedCatalog.word (J*(512*h)) (count h k) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^((J-k)*(512*h))*
      ((2^((J-k)*(512*h))*B)*(2^((J-k)*(512*h))*D)) : ℕ) : ℤ) ≤ lim.word)
    (hpre : k*h+boxCut ≤ cut)
    (hf : ∀ S, S.card ≤ cut → |f S| ≤ B) (hg : ∀ S, S.card ≤ cut → |g S| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f (J*(512*h)))
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g (J*(512*h)))
    (hdPair : d+512*h+k+6 ≤ lim.depth) (hd : d+J*(512*h)+15 ≤ lim.depth)
    (hdSort : d+Nat.clog 2 (count h k)+3 ≤ lim.depth) :
    Meets lim program 51 d
      [J*(512*h),cut,boxCut,(J-k)*(512*h),(J-k)*(512*h),k*(512*h),baseL,baseR,
        512*h,h,k,srcS,pairL,pairR,stageL,stageR,ptrBase,boxBase,maskBase,work,indexBase]
      μ (time h J k boxCut)
      (fun r μ' =>
        r = (stageL+LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k : ℕ) ∧
        μ' (stageL+LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k) = (count h k : ℤ) ∧
        SegN μ' ptrBase (List.ofFn fun i : Fin (count h k) =>
          boxBase+i.val*stride ((J-k)*(512*h)) boxCut) ∧
        (∀ i < count h k, LightBoxStages.StoredThrough μ'
          (boxBase+i*stride ((J-k)*(512*h)) boxCut) boxCut
          (leafWeight (block_fit hk) f g ((J-k)*(512*h)) (preL h J k i) (preR h J k i))
          ((J-k)*(512*h))) ∧
        LightZetaStages.StoredThrough μ' baseL cut f (J*(512*h)) ∧
        LightZetaStages.StoredThrough μ' baseR cut g (J*(512*h)) ∧
        (∃ S : List ℤ, Seg μ' indexBase S ∧
          S.Perm (ReportingHostPackedCatalog.codes (ReportingHostPackedCatalog.prefixKey h J k) (count h k)) ∧
          S.Pairwise (· ≤ ·)) ∧
        Kept μ μ' srcS) := by
  have hn := count_pos h k
  have hstageOrder : stageL ≤ stageR := by unfold LightRadixKeys.space at hstageL; omega
  have hptrOrder : stageR ≤ ptrBase := by unfold LightRadixKeys.space at hstageR; omega
  have hprefixEndL : stageL+LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k+1+
      count h k ≤ ptrBase := hstageL.trans hptrOrder
  have hprefixEndR : stageR+LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k+1+
      count h k ≤ ptrBase := hstageR
  apply Meets.of_body (p := 51) (by rfl : program[51]? = some (body 43 50))
  unfold body time
  have hc := ((LightReportingPrefixCatalog.program_meets (d := d+1) (μ := μ)
    hk f g hw hcut hboxCut hdataL hdataR hS hL hR hstageL hstageR hptr hbox hmasks
    hpairSpace hspace hpowWord hkeysWord hword hvalueWord hpre hf hg hstoredL hstoredR (by omega) (by omega)).append
    (LightReportingSortedCatalog.program.map
      (ReportingHostRelocation.relocate LightReportingPrefixCatalog.program.length))).append [body 43 50]
  light_call hc using LightReportingPrefixCatalog.time,LightReportingSortedCatalog.time
    with head μ₁ ⟨hhead,hptrs,hboxes,hsourceL,hsourceR,hcount,hleft,hright,hkeepCatalog⟩
  light_set (count h k : ℕ) using hhead,hcount,
    LightReportingPrefixCatalog.time,LightReportingSortedCatalog.time
  light_set (LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k : ℕ)
    using hhead,LightReportingPrefixCatalog.time,LightReportingSortedCatalog.time
  light_set (stageR+LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k+1 : ℕ)
    using LightReportingPrefixCatalog.time,LightReportingSortedCatalog.time
  light_set (stageL+LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k+1 : ℕ)
    using hhead,LightReportingPrefixCatalog.time,LightReportingSortedCatalog.time
  have hs := (ReportingHostRelocation.meets
    (LightReportingSortedCatalog.program_meets (d := d+1) (μ := μ₁)
      (fun i => subsetMask (preL h J k i)) (fun i => subsetMask (preR h J k i)) hw
      (hprefixEndL.trans (by omega)) (hprefixEndR.trans (by omega)) hindexEnd (by omega)
      hsortSpace hindexWord hleft hright
      (fun i _ => (subsetMask_isMask (preL h J k i)).1)
      (fun i _ => (subsetMask_isMask (preR h J k i)).1) (by omega))
    LightReportingPrefixCatalog.program).append [body 43 50]
  light_call hs using LightReportingPrefixCatalog.time,LightReportingSortedCatalog.time
    with result μ₂ ⟨hindexData,hkeepIndex⟩
  light_set (stageL+LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k : ℕ)
    using hhead,LightReportingPrefixCatalog.time,LightReportingSortedCatalog.time
  refine ⟨by simp,?_,?_,?_,?_,?_,hindexData,?_⟩
  · exact (hkeepIndex _ (by omega)).trans hcount
  · intro i hi
    change μ₂ (ptrBase+i) = _
    rw [hkeepIndex _ (by simpa only [List.length_ofFn,List.length_map] using
      (show ptrBase+i < indexBase by
        have hi' : i < count h k := by simpa only [List.length_ofFn,List.length_map] using hi
        omega))]
    exact hptrs i hi
  · intro i hi
    have hmul := Nat.mul_le_mul_right (stride ((J-k)*(512*h)) boxCut) (show i+1 ≤ count h k by omega)
    have hmul' : i*stride ((J-k)*(512*h)) boxCut+stride ((J-k)*(512*h)) boxCut ≤
        count h k*stride ((J-k)*(512*h)) boxCut := by simpa only [Nat.add_mul,Nat.one_mul] using hmul
    have hEnd : boxBase+i*stride ((J-k)*(512*h)) boxCut+
        (((J-k)*(512*h)+1)*downsetCap ((J-k)*(512*h)) boxCut) ≤ indexBase := by
      change boxBase+i*stride ((J-k)*(512*h)) boxCut+stride ((J-k)*(512*h)) boxCut ≤ indexBase
      omega
    exact ReportingHostQueryBounds.boxStored_of_on (hboxes i hi)
      (by intro a _ ha; exact hkeepIndex a (ha.trans_le hEnd))
  · exact LightSignedLeafBatch.storedThrough_of_on hsourceL
      (by intro i _ hi; exact hkeepIndex i (by omega))
  · exact LightSignedLeafBatch.storedThrough_of_on hsourceR
      (by intro i _ hi; exact hkeepIndex i (by omega))
  · intro i hi
    exact (hkeepIndex i (by omega)).trans (hkeepCatalog i hi)

end ThreeSum.LightReportingCatalogIndex
