import Submission.ThreeSum.LightReportingStoredStep

/-!
# Actual bounded sequence of reporting levels

The recursive host executes only the requested number of levels, loading
all catalogs from persistent records. Its exact cost is the sum of the
actual level costs, with no multiplication by a worst-level query bound.
-/

namespace ThreeSum.LightReportingLevels

open Light Finset ThreeSum.SubsetAddress
open BlockRows BlockIndex BlockMaskLayout BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix LightReportingPrefixCatalog
open ReportingHostLevelData ReportingHostFrontierLayout

set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

def body (pSelf pStep : ℕ) : Stmt :=
  .ite (k 0 <' v 3)
    (.call pSelf [v 0,v 1,v 2,v 3 -' k 1,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,v 17,v 18] 19 ;;
      .call pStep [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,v 17,v 18] 0)
    (.set 0 (M (v 8)))

def program : Program := LightReportingStoredStep.program ++ [body 52 51]

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def time {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) (D : ℕ→Catalog) : ℕ→ℕ
  | 0 => 30
  | k+1 => time I w D k+
    LightReportingStoredStep.time h J k (D (k+1)).t (ReportingHostFrontier.frontier I w k).length+200

variable {lim : Limits}

theorem program_meets {μ : ℕ→ℤ}
    {h J K k baseL baseR catalogs rows root masks childL childR counts selected maskBase work depth : ℕ}
    (D : ℕ→Catalog) (hk : k≤K) (hK : K≤J)
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ) (w : Wanted h J α)
    (hkey : w.1∈A ∧ globalModulus h J ∣ (a w.1%pMod+lift w.2.1*pMod+shift)-globalKey w.2.2)
    (hw : (lim.space : ℤ)≤lim.word)
    (HS : Sources μ pMod shift B C b c w.2.2 baseL baseR)
    (HC : ∀ (j : ℕ) (hj : j≤K), Stored μ (D j) (hj.trans hK) pMod shift B C b c w.2.2)
    (HB : ∀ j≤K, Bounds h J j (D j) baseL baseR root)
    (HW : ∀ j≤K, Scratch lim h J j (D j) B.card C.card maskBase work)
    (hmeta : ∀ j≤K, SegN μ (catalogs+5*j) ((D j).record h j))
    (hmetaEnd : catalogs+5*(K+1)≤root) (hrows : rows+J≤root)
    (hrow : ∀ (j : ℕ) (hj : j<J), μ (rows+j)=(rowMask (outputRows w.2.2) ⟨j,hj⟩ : ℤ))
    (hcap : μ (root+3)=(capacity (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w : ℤ))
    (HA : At μ (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w root
      (capacity (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w) 0)
    (hout : slot root (capacity (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w) (K+1)≤masks)
    (hmasks : masks+groupSize h≤childL) (hchildL : childL+groupSize h≤childR)
    (hchildR : childR+groupSize h≤counts) (hcounts : counts+groupSize h≤selected)
    (hselected : selected+groupSize h≤maskBase)
    (hparams : J+512*h+groupSize h+sourceCut h J≤lim.space)
    (hd : depth+k+2*width h J+19≤lim.depth) :
    Meets lim program 52 depth
      [width h J,h,J,k,baseL,baseR,catalogs,rows,root,masks,childL,childR,counts,selected,maskBase,work,
        groupSize h,sourceCut h J,512*h]
      μ (time (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w D k)
      (fun r ν =>
        let I := rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c
        r=((ReportingHostFrontier.frontier I w k).length : ℤ) ∧
        (∀ j≤k, At ν I w root (capacity I w) j) ∧
        ν (root+3)=(capacity I w : ℤ) ∧ Kept μ ν root) := by
  let I := rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c
  let cap := capacity I w
  change At μ I w root cap 0 at HA
  change μ (root+3)=(cap : ℤ) at hcap
  change slot root cap (K+1)≤masks at hout
  change Meets lim program 52 depth _ μ (time I w D k)
    (fun r ν => r=((ReportingHostFrontier.frontier I w k).length : ℤ) ∧
      (∀ j≤k, At ν I w root cap j) ∧ ν (root+3)=(cap : ℤ) ∧ Kept μ ν root)
  have hcapPos : 0<cap := capacity_pos I w
  have hw0 := HW 0 (Nat.zero_le K)
  have hspace := hw0.space
  have hwork := hw0.masks
  have hfirst : slot root cap 1≤masks := (slot_mono (by omega)).trans hout
  have hfirst' : root+4+2*cap≤masks := by simpa [slot,Nat.add_assoc] using hfirst
  have hcapSpace : cap≤lim.space := by omega
  induction k generalizing depth with
  | zero =>
      apply Meets.of_body (p := 52) (by rfl : program[52]?=some (body 52 51))
      unfold body time
      light_if hbad hbase : (0 : ℤ)<0
      · omega
      · have hcount : μ root=((ReportingHostFrontier.frontier I w 0).length : ℤ) := by
          simpa only [slot_zero] using HA.count
        have hcountSpace := frontier_capacity I w (Nat.zero_le J)
        light_set ((ReportingHostFrontier.frontier I w 0).length : ℕ) using hcount
        refine ⟨by simp,?_,hcap,SameOn.refl⟩
        intro j hj
        have hj0 : j=0 := by omega
        subst j
        exact HA
  | succ k ih =>
      have hkle : k≤K := by omega
      have hkJ : k<J := by omega
      apply Meets.of_body (p := 52) (by rfl : program[52]?=some (body 52 51))
      unfold body
      rw [time]
      light_if hstep hbad : (0 : ℤ)<((k+1 : ℕ) : ℤ) using LightReportingStoredStep.time
      · have hr := ih hkle (depth := depth+1) (by omega)
        light_call hr using LightReportingStoredStep.time with prev ν ⟨hprev,hlevels,hcapν,hkeepν⟩
        have HSν := HS.of_kept (HB 0 (by omega)) hkeepν
        have HCν := (HC (k+1) hk).of_kept (HB (k+1) hk) hkeepν
        have hmetaν : SegN ν (catalogs+5*(k+1)) ((D (k+1)).record h (k+1)) := by
          intro i hi
          have hi' : i<5 := by simpa only [Catalog.record,List.length_map,List.length_cons,List.length_nil] using hi
          have hm := Nat.mul_le_mul_left 5 (show k+2≤K+1 by omega)
          exact (hkeepν _ (by omega)).trans (hmeta (k+1) hk i hi)
        have hrowν : ν (rows+k)=(rowMask (outputRows w.2.2) ⟨k,hkJ⟩ : ℤ) :=
          (hkeepν _ (by omega)).trans (hrow k hkJ)
        have houtk : slot root cap (k+2)≤masks := (slot_mono (by omega)).trans hout
        have hrun := (LightReportingStoredStep.program_meets (depth := depth+1) (μ := ν) hkJ
          pMod shift A B C a b c w hkey hw HSν HCν (HB (k+1) hk) (HW (k+1) hk)
          hmetaν (by have hm:=Nat.mul_le_mul_left 5 (show k+2≤K+1 by omega); omega)
          hrows hrowν hcapν (hlevels k le_rfl) houtk hmasks hchildL hchildR hcounts hselected hparams (by omega)).append [body 52 51]
        change Meets lim program 51 (depth+1) _ ν
          (LightReportingStoredStep.time h J k (D (k+1)).t
            (ReportingHostFrontier.frontier I w k).length) _ at hrun
        light_call hrun using LightReportingStoredStep.time with found ν₂ ⟨hfound,hnew,hkeepStep⟩
        change found=((ReportingHostFrontier.frontier I w (k+1)).length : ℤ) at hfound
        change At ν₂ I w root cap (k+1) at hnew
        change Kept ν ν₂ (slot root cap (k+1)) at hkeepStep
        have hrootStep : root+3<slot root cap (k+1) := by
          have hh : slot root cap 1≤slot root cap (k+1) := slot_mono (by omega)
          simp only [slot] at hh ⊢
          omega
        refine ⟨hfound,?_,(hkeepStep _ hrootStep).trans hcapν,?_⟩
        · intro j hj
          by_cases hjeq : j=k+1
          · simpa only [hjeq] using hnew
          · exact (hlevels j (by omega)).of_kept (frontier_capacity I w (by omega))
              (slot_mono (by omega)) hkeepStep
        · intro i hi
          exact (hkeepStep i (by omega)).trans (hkeepν i hi)
      · omega

end ThreeSum.LightReportingLevels
