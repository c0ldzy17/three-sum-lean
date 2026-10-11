import Submission.ThreeSum.ReportingHostLevelData
import Submission.ThreeSum.ReportingHostFrontierLayout

/-!
# Actual root query and frontier initialization

The machine executes the exact catalog-backed empty-prefix query, computes
its capacity from the returned raw mass, and writes the root frontier and
its two aligned zero masks. No supplied root count or capacity is used.
-/

namespace ThreeSum.LightReportingInitialize

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockIndex BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
open ReportingHostLevelData ReportingHostFrontierLayout

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-- Query arguments, destination root slot, and local child count. -/
def body (pQuery : ℕ) : Stmt :=
  .call pQuery [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,v 17,v 18,v 19] 22 ;;
  .set 23 ((v 22 +' k 1) *' v 21) ;;
  .store (v 20 +' k 2) (v 22) ;;
  .store (v 20 +' k 3) (v 23) ;;
  .store (v 20 +' k 1) (v 10) ;;
  .store (v 20 +' k 4) (k 0) ;;
  .store (v 20 +' k 4 +' v 23) (k 0) ;;
  .ite (k 0 <' v 22)
    (.store (v 20) (k 1) ;; .set 0 (k 1))
    (.store (v 20) (k 0) ;; .set 0 (k 0))

def program : Program := LightReportingCatalogQuery.program ++ [body 35]
def time (h J t : ℕ) : ℕ := LightReportingCatalogQuery.time h J 0 t+400

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem program_meets {μ : ℕ→ℤ} {h J baseL baseR maskBase work dst depth : ℕ} {D : Catalog}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ) (w : Wanted h J α)
    (hkey : w.1∈A ∧ globalModulus h J ∣ (a w.1%pMod+lift w.2.1*pMod+shift)-globalKey w.2.2)
    (hw : (lim.space : ℤ)≤lim.word)
    (HS : Sources μ pMod shift B C b c w.2.2 baseL baseR)
    (HC : Stored μ D (Nat.zero_le J) pMod shift B C b c w.2.2)
    (HB : Bounds h J 0 D baseL baseR dst)
    (HW : Scratch lim h J 0 D B.card C.card maskBase work)
    (hout : slot dst (capacity (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w) 1≤maskBase)
    (hd : depth+2*width h J+13≤lim.depth) :
    Meets lim program 36 depth
      [width h J,sourceCut h J,suffixStage J (512*h) 0,0,0,0,0,suffixStage J (512*h) 0,0,
        residualSize h J 0,subsetMask (querySet 0 (outputRows w.2.2)),D.t,baseL,baseR,
        D.boxCut,D.indexBase,D.ptrBase,count h 0,maskBase,work,dst,groupSize h]
      μ (time h J D.t)
      (fun r ν =>
        let I := rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c
        r=((ReportingHostFrontier.frontier I w 0).length : ℤ) ∧
        At ν I w dst (capacity I w) 0 ∧
        ν (dst+2)=(rootMass I w : ℤ) ∧ ν (dst+3)=(capacity I w : ℤ) ∧ Kept μ ν dst) := by
  let I := rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c
  let cap := capacity I w
  change Meets lim program 36 depth _ μ (time h J D.t)
    (fun r ν => r=((ReportingHostFrontier.frontier I w 0).length : ℤ) ∧
      At ν I w dst cap 0 ∧ ν (dst+2)=(rootMass I w : ℤ) ∧ ν (dst+3)=(cap : ℤ) ∧ Kept μ ν dst)
  change slot dst cap 1≤maskBase at hout
  have hpos : 0<cap := capacity_pos I w
  have hmass : rootMass I w<cap := mass_lt_capacity I w
  have hout' : dst+4+2*cap≤maskBase := by simpa [slot,Nat.add_assoc] using hout
  have hmaskWork := HW.masks
  have hspace := HW.space
  have hcapSpace : cap≤lim.space := by omega
  have hcapWord : (cap : ℤ)≤lim.word := (Int.ofNat_le.mpr hcapSpace).trans hw
  have hrootWord : (rootMass I w : ℤ)≤lim.word := (Int.ofNat_le.mpr (hmass.le.trans hcapSpace)).trans hw
  have hmaskWord : (subsetMask (querySet 0 (outputRows w.2.2)) : ℤ)≤lim.word := by
    have hp : 2^(width h J)≤(width h J+1)*2^(width h J+1) :=
      (Nat.pow_le_pow_right (by decide) (by omega)).trans (Nat.le_mul_of_pos_left _ (by omega))
    exact (Int.ofNat_le.mpr ((subsetMask_isMask _).1.le.trans hp)).trans HW.word
  have hp : ValidPrefix w.2.2 0 [] := by simp [ValidPrefix]
  apply Meets.of_body (p := 36) (by rfl : program[36]?=some (body 35))
  unfold body time
  have he := (ReportingHostLevelData.query_meets (depth := depth+1) (Nat.zero_le J)
    pMod shift A B C a b c w [] hp hkey hw HS HC (HB.mono (by omega)) HW (by omega)).append [body 35]
  have hEmpty : subsetMask (∅ : Finset (Fin (width h J)))=0 := by rfl
  simp only [ReportingHostFrontierLayout.left_zero,ReportingHostFrontierLayout.right_zero,hEmpty,
    Nat.cast_zero,zero_mul] at he
  light_call he using LightReportingCatalogQuery.time with mass ν ⟨hmassRet,hkept⟩
  change mass=(rootMass I w : ℤ) at hmassRet
  have hcapCalc : (mass+1)*(groupSize h : ℤ)=(cap : ℤ) := by
    rw [hmassRet]
    simp only [cap,capacity,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  light_set (cap : ℕ) using hcapCalc,LightReportingCatalogQuery.time
  light_store (dst+2) (rootMass I w : ℕ) using hmassRet,LightReportingCatalogQuery.time
  light_store (dst+3) (cap : ℕ) using LightReportingCatalogQuery.time
  light_store (dst+1) (subsetMask (querySet 0 (outputRows w.2.2)) : ℕ) using LightReportingCatalogQuery.time
  light_store (dst+4) (0 : ℕ) using LightReportingCatalogQuery.time
  light_store (dst+4+cap) (0 : ℕ) using LightReportingCatalogQuery.time
  light_if hyes hno : (0 : ℤ)<mass using LightReportingCatalogQuery.time
  · have hpositive : 0<rootMass I w := by omega
    have hfront : ReportingHostFrontier.frontier I w 0=[[]] := by rw [frontier_zero,if_pos hpositive]
    have hL : leftMasks I w 0=[0] := by rw [leftMasks_zero,if_pos hpositive]
    have hR : rightMasks I w 0=[0] := by rw [rightMasks_zero,if_pos hpositive]
    light_store dst (1 : ℕ) using LightReportingCatalogQuery.time
    light_set (1 : ℕ) using LightReportingCatalogQuery.time
    refine ⟨by simp [hfront],?_,?_,?_,?_⟩
    · constructor
      · simp [slot,hfront]
      · simp [slot,Function.update_of_ne,show dst+1≠dst+4+cap by omega,show dst+1≠dst+4 by omega]
      · rw [hL]
        intro i hi
        have hz : i=0 := by simpa using hi
        subst i
        simp only [ReportingHostFrontierLayout.left,slot_zero,Nat.add_zero,
          Function.update_of_ne (show dst+4≠dst by omega),
          Function.update_of_ne (show dst+4≠dst+4+cap by omega),Function.update_self,List.map_cons,
          List.map_nil,List.getElem_cons_zero,Nat.cast_zero]
      · rw [hR]
        intro i hi
        have hz : i=0 := by simpa using hi
        subst i
        simp [ReportingHostFrontierLayout.right,ReportingHostFrontierLayout.left,slot,show dst+4+cap≠dst by omega]
    · simp [show dst+2≠dst by omega,show dst+2≠dst+4+cap by omega,show dst+2≠dst+4 by omega]
    · simp [show dst+3≠dst by omega,show dst+3≠dst+4+cap by omega,show dst+3≠dst+4 by omega]
    · intro i hi
      simp only [Function.update_of_ne (show i≠dst by omega),Function.update_of_ne (show i≠dst+4+cap by omega),
        Function.update_of_ne (show i≠dst+4 by omega),Function.update_of_ne (show i≠dst+1 by omega),
        Function.update_of_ne (show i≠dst+3 by omega),Function.update_of_ne (show i≠dst+2 by omega)]
      exact hkept i ⟨by omega,by omega⟩
  · have hzero : ¬0<rootMass I w := by omega
    have hfront : ReportingHostFrontier.frontier I w 0=[] := by rw [frontier_zero,if_neg hzero]
    have hL : leftMasks I w 0=[] := by rw [leftMasks_zero,if_neg hzero]
    have hR : rightMasks I w 0=[] := by rw [rightMasks_zero,if_neg hzero]
    light_store dst (0 : ℕ) using LightReportingCatalogQuery.time
    light_set (0 : ℕ) using LightReportingCatalogQuery.time
    refine ⟨by simp [hfront],?_,?_,?_,?_⟩
    · constructor
      · simp [slot,hfront]
      · simp [slot,Function.update_of_ne,show dst+1≠dst+4+cap by omega,show dst+1≠dst+4 by omega]
      · simp [hL,SegN]
      · simp [hR,SegN]
    · simp [show dst+2≠dst by omega,show dst+2≠dst+4+cap by omega,show dst+2≠dst+4 by omega]
    · simp [show dst+3≠dst by omega,show dst+3≠dst+4+cap by omega,show dst+3≠dst+4 by omega]
    · intro i hi
      simp only [Function.update_of_ne (show i≠dst by omega),Function.update_of_ne (show i≠dst+4+cap by omega),
        Function.update_of_ne (show i≠dst+4 by omega),Function.update_of_ne (show i≠dst+1 by omega),
        Function.update_of_ne (show i≠dst+3 by omega),Function.update_of_ne (show i≠dst+2 by omega)]
      exact hkept i ⟨by omega,by omega⟩

end ThreeSum.LightReportingInitialize
