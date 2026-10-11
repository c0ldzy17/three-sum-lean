import Submission.ThreeSum.SharedReportingBankData

/-!
# Load two retained source pointers and construct one shared catalog record

The two sources may come from independent B and C bands. The occurrence
code is already represented by the supplied physical pointer cells. This
program loads those cells, runs the complete existing catalog constructor,
reads its computed prefix count, and writes the five-cell level record.
-/

namespace ThreeSum.LightSharedReportingEntry

open Light SubsetAddress LightPascal ReportingHostSuffix ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData
open SharedReportingBankData

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000

/-- The catalog's twenty-one arguments, with arguments 6 and 7 now source
pointer cells, followed by the exact switch and record destination. -/
def body (pCatalog : ℕ) : Stmt :=
  .set 23 (M (v 6)) ;;
  .set 24 (M (v 7)) ;;
  .call pCatalog [v 0,v 1,v 2,v 3,v 4,v 5,v 23,v 24,v 8,v 9,v 10,v 11,
    v 12,v 13,v 14,v 15,v 16,v 17,v 18,v 19,v 20] 25 ;;
  .set 26 (M (v 25)) ;;
  .store (v 22) (v 21) ;;
  .store (v 22 +' k 1) (v 2) ;;
  .store (v 22 +' k 2) (v 20) ;;
  .store (v 22 +' k 3) (v 16) ;;
  .store (v 22 +' k 4) (v 26) ;;
  .set 0 (v 26)

def program : Program := LightReportingCatalogIndex.program ++ [body 51]

def time (h J k boxCut : ℕ) : ℕ := LightReportingCatalogIndex.time h J k boxCut+500

theorem program_length : program.length=53 := rfl

theorem program_meets {lim : Limits} {μ : ℕ → ℤ}
    {h J k cut boxCut baseL baseR cellL cellR srcS pairL pairR stageL stageR
      ptrBase boxBase maskBase indexBase work B D d t rec : ℕ}
    (hk : k ≤ J) (f g : Finset (Fin (J*(512*h))) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hcut : cut ≤ J*(512*h)) (hboxCut : boxCut ≤ (J-k)*(512*h))
    (hcellL : cellL < rec) (hcellR : cellR < rec)
    (hdataL : baseL+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ rec)
    (hdataR : baseR+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ rec)
    (hrec : rec+5 ≤ srcS)
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
    (hvalueWord : (((2^((J-k)*(512*h))*
      ((2^((J-k)*(512*h))*B)*(2^((J-k)*(512*h))*D))) : ℕ) : ℤ) ≤ lim.word)
    (htWord : (t : ℤ) ≤ lim.word)
    (hpre : k*h+boxCut ≤ cut) (hf : ∀ S, S.card ≤ cut → |f S| ≤ B)
    (hg : ∀ S, S.card ≤ cut → |g S| ≤ D)
    (hleftRead : μ cellL=(baseL : ℤ)) (hrightRead : μ cellR=(baseR : ℤ))
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f (J*(512*h)))
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g (J*(512*h)))
    (hdPair : d+512*h+k+7 ≤ lim.depth) (hd : d+J*(512*h)+16 ≤ lim.depth)
    (hdSort : d+Nat.clog 2 (count h k)+4 ≤ lim.depth) :
    Meets lim program 52 d
      [J*(512*h),cut,boxCut,(J-k)*(512*h),(J-k)*(512*h),k*(512*h),cellL,cellR,
        512*h,h,k,srcS,pairL,pairR,stageL,stageR,ptrBase,boxBase,maskBase,work,indexBase,t,rec]
      μ (time h J k boxCut) (fun r ν =>
        r=(count h k : ℤ) ∧
        Entry ν rec ⟨t,boxCut,boxBase,indexBase,ptrBase⟩ hk f g ∧
        LightZetaStages.StoredThrough ν baseL cut f (J*(512*h)) ∧
        LightZetaStages.StoredThrough ν baseR cut g (J*(512*h)) ∧
        KeptBut μ ν srcS rec 5) := by
  have hstageOrder : stageL ≤ stageR := by unfold LightRadixKeys.space at hstageL; omega
  have hheaderBound : stageL+LightRadixKeys.offset
      (LightReportingPrefixArrays.localCount (512*h) h) k+1+count h k ≤ stageR := hstageL
  have hptrOrder : stageR ≤ ptrBase := by unfold LightRadixKeys.space at hstageR; omega
  have hsourceOrder : srcS ≤ ptrBase := by omega
  have hrecSpace : rec+5 ≤ lim.space := by omega
  have hcountSpace : count h k ≤ lim.space := by omega
  have hbaseLSpace : baseL ≤ lim.space := by omega
  have hbaseRSpace : baseR ≤ lim.space := by omega
  have hboxCutWord : (boxCut : ℤ) ≤ lim.word := by
    have hh : boxCut ≤ (J*(512*h)+1)*2^(J*(512*h)+1) := by
      have hV : (J-k)*(512*h) ≤ J*(512*h) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      have hp : 1 ≤ 2^(J*(512*h)+1) := Nat.one_le_pow _ _ (by decide)
      nlinarith
    exact (Int.ofNat_le.mpr hh).trans hword
  apply Meets.of_body (p := 52) (by rfl : program[52]?=some (body 51))
  unfold body time
  light_set (baseL : ℕ) using hleftRead
  light_set (baseR : ℕ) using hrightRead
  have hc := (LightReportingCatalogIndex.program_meets (d := d+1) hk f g hw hcut hboxCut
    (by omega) (by omega) hS hL hR hstageL hstageR hptr hbox hmasks hindex hindexEnd
    hpairSpace hspace hsortSpace hpowWord hkeysWord hword hindexWord hvalueWord hpre hf hg
    hstoredL hstoredR (by omega) (by omega) (by omega)).append [body 51]
  light_call hc with head ν₁ ⟨hhead,hcount,hptrs,hboxes,hsourceL,hsourceR,hindexData,hkeepCatalog⟩
  light_set (count h k : ℕ) using hhead,hcount
  light_store rec (t : ℕ)
  light_store (rec+1) (boxCut : ℕ)
  light_store (rec+2) (indexBase : ℕ)
  light_store (rec+3) (ptrBase : ℕ)
  light_store (rec+4) (count h k : ℕ)
  light_set (count h k : ℕ)
  let ν₂ := Function.update (Function.update (Function.update (Function.update (Function.update ν₁ rec
    (t : ℤ)) (rec+1) (boxCut : ℤ)) (rec+2) (indexBase : ℤ)) (rec+3) (ptrBase : ℤ))
    (rec+4) (count h k : ℤ)
  have hbefore : Kept ν₁ ν₂ rec := by
    intro a ha
    dsimp only [ν₂]
    repeat' rw [Function.update_of_ne (by omega)]
  have hafter : ∀ a, rec+5 ≤ a → ν₂ a=ν₁ a := by
    intro a ha
    dsimp only [ν₂]
    repeat' rw [Function.update_of_ne (by omega)]
  have htables : Tables ν₁ (⟨t,boxCut,boxBase,indexBase,ptrBase⟩ : Catalog) hk f g :=
    ⟨hindexData,hptrs,hboxes⟩
  refine ⟨by simp,⟨?_,htables.of_after hafter (by dsimp only; omega)
    (by dsimp only; omega) (by dsimp only; omega)⟩,?_,?_,?_⟩
  · intro i hi
    have hi' : i < 5 := by simpa only [Catalog.record,List.length_map,List.length_cons,List.length_nil] using hi
    change ν₂ (rec+i)=_
    interval_cases i <;> simp [ν₂,Catalog.record]
  · exact LightSignedLeafBatch.storedThrough_of_on hsourceL
      (by intro a _ ha; exact hbefore a (ha.trans_le hdataL))
  · exact LightSignedLeafBatch.storedThrough_of_on hsourceR
      (by intro a _ ha; exact hbefore a (ha.trans_le hdataR))
  · intro a ⟨ha,houtside⟩
    change ν₂ a=μ a
    dsimp only [ν₂]
    repeat' rw [Function.update_of_ne (by rcases houtside with hl | hr <;> omega)]
    exact hkeepCatalog a ha

end ThreeSum.LightSharedReportingEntry
