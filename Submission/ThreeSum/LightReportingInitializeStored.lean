import Submission.ThreeSum.LightReportingInitialize

/-!
# Root initialization from retained catalog and cover headers

The root query reads its sorted-catalog controls and the selected cover's
actual group-size cell. The empty-prefix dimensions are computed directly
from the common source width and cut; root mass and capacity are returned
by the executed query and initializer.
-/

namespace ThreeSum.LightReportingInitializeStored

open Light Finset ThreeSum.SubsetAddress
open BlockRows BlockIndex BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostLevelData ReportingHostFrontierLayout

set_option maxHeartbeats 2600000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false

/-- Width, source cut, source stages, catalog bank, packed query mask,
retained cover, root output, mask scratch, and work. -/
def body (pInit : ℕ) : Stmt :=
  .set 10 (M (v 6 +' k 3)) ;;
  .set 11 (M (v 4)) ;;
  .set 12 (M (v 4 +' k 1)) ;;
  .set 13 (M (v 4 +' k 2)) ;;
  .set 14 (M (v 4 +' k 3)) ;;
  .set 15 (M (v 4 +' k 4)) ;;
  .call pInit [v 0,v 1,v 0,k 0,k 0,k 0,k 0,v 0,k 0,v 1,v 5,v 11,v 2,v 3,v 12,v 13,v 14,v 15,
    v 8,v 9,v 7,v 10] 0

def program : Program := LightReportingInitialize.program ++ [body 36]
def time (h J t : ℕ) : ℕ := LightReportingInitialize.time h J t+500

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem program_meets {μ : ℕ→ℤ}
    {h J baseL baseR catalogs cover maskBase work root depth : ℕ} {D : Catalog}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ) (w : Wanted h J α)
    (hkey : w.1∈A ∧ globalModulus h J ∣ (a w.1%pMod+lift w.2.1*pMod+shift)-globalKey w.2.2)
    (hw : (lim.space : ℤ)≤lim.word)
    (HS : Sources μ pMod shift B C b c w.2.2 baseL baseR)
    (HC : Stored μ D (Nat.zero_le J) pMod shift B C b c w.2.2)
    (HB : Bounds h J 0 D baseL baseR root)
    (HW : Scratch lim h J 0 D B.card C.card maskBase work)
    (hmeta : SegN μ catalogs (D.record h 0)) (hmetaEnd : catalogs+5≤root)
    (hgroup : μ (cover+3)=(groupSize h : ℤ)) (hcoverEnd : cover+4≤root)
    (hout : slot root (capacity (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w) 1≤maskBase)
    (hd : depth+2*width h J+14≤lim.depth) :
    Meets lim program 37 depth
      [width h J,sourceCut h J,baseL,baseR,catalogs,subsetMask (querySet 0 (outputRows w.2.2)),
        cover,root,maskBase,work]
      μ (time h J D.t)
      (fun r ν =>
        let I := rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c
        r=((ReportingHostFrontier.frontier I w 0).length : ℤ) ∧
        At ν I w root (capacity I w) 0 ∧
        ν (root+2)=(rootMass I w : ℤ) ∧ ν (root+3)=(capacity I w : ℤ) ∧ Kept μ ν root) := by
  let I := rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c
  have hcap : groupSize h≤capacity I w := Nat.le_mul_of_pos_left _ (by omega)
  have hout' : root+4+2*capacity I w≤maskBase := by simpa [slot,Nat.add_assoc] using hout
  have hwork := HW.masks
  have hspace := HW.space
  have ht := HW.t
  have hcut := HW.cut
  have hindex := HB.index
  have hpointers := HB.pointers
  have hmetaT := hmeta.getElem (i := 0) (by simp [Catalog.record])
  have hmetaCut := hmeta.getElem (i := 1) (by simp [Catalog.record])
  have hmetaIndex := hmeta.getElem (i := 2) (by simp [Catalog.record])
  have hmetaPtr := hmeta.getElem (i := 3) (by simp [Catalog.record])
  have hmetaN := hmeta.getElem (i := 4) (by simp [Catalog.record])
  simp only [Catalog.record,List.getElem_cons_zero,List.getElem_cons_succ,Nat.add_zero]
    at hmetaT hmetaCut hmetaIndex hmetaPtr hmetaN
  have hN : LightReportingPrefixCatalog.count h 0=1 := by simp [LightReportingPrefixCatalog.count]
  have hstage : suffixStage J (512*h) 0=width h J := by simp [suffixStage]
  have hres : residualSize h J 0=sourceCut h J := by
    simp only [residualSize,sourceCut,Nat.sub_zero]
    ring
  have hcutWidth := sourceCut_le_width h J
  have hgroupZ : μ (((cover : ℤ)+3).toNat)=(groupSize h : ℤ) := by
    rw [show ((cover : ℤ)+3).toNat=cover+3 by omega]
    exact hgroup
  have hmetaIndexZ : μ (((catalogs : ℤ)+2).toNat)=(D.indexBase : ℤ) := by
    rw [show ((catalogs : ℤ)+2).toNat=catalogs+2 by omega]
    exact hmetaIndex
  have hmetaPtrZ : μ (((catalogs : ℤ)+3).toNat)=(D.ptrBase : ℤ) := by
    rw [show ((catalogs : ℤ)+3).toNat=catalogs+3 by omega]
    exact hmetaPtr
  have hmetaNZ : μ (((catalogs : ℤ)+4).toNat)=(LightReportingPrefixCatalog.count h 0 : ℤ) := by
    rw [show ((catalogs : ℤ)+4).toNat=catalogs+4 by omega]
    exact hmetaN
  apply Meets.of_body (p := 37) (by rfl : program[37]?=some (body 36))
  unfold body time
  light_set (groupSize h : ℕ) using hgroup,hgroupZ,LightReportingInitialize.time
  light_set (D.t : ℕ) using hmetaT,hres,LightReportingInitialize.time
  light_set (D.boxCut : ℕ) using hmetaCut,hres,LightReportingInitialize.time
  light_set (D.indexBase : ℕ) using hmetaIndex,hmetaIndexZ,LightReportingInitialize.time
  light_set (D.ptrBase : ℕ) using hmetaPtr,hmetaPtrZ,LightReportingInitialize.time
  light_set (LightReportingPrefixCatalog.count h 0 : ℕ) using hmetaN,hmetaNZ,hN,LightReportingInitialize.time
  have hrun := (LightReportingInitialize.program_meets (depth := depth+1) pMod shift A B C a b c w
    hkey hw HS HC HB HW hout (by omega)).append [body 36]
  rw [hstage,hres] at hrun
  light_call hrun using LightReportingInitialize.time with result ν hpost
  exact hpost

end ThreeSum.LightReportingInitializeStored
