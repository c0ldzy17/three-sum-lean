import Submission.ThreeSum.LightReportingCatalogIndex
import Submission.ThreeSum.ReportingHostCatalogCosts
import Submission.ThreeSum.ReportingHostCatalogIndexCosts
import Submission.ThreeSum.LightScales
import Submission.ThreeSum.ArithmeticStageBounds

/-!
# Charge the complete shared reporting catalog constructor

The actual prefix constructor enumerates the local balanced pairs even at
level zero. That additive local cost is included explicitly and bounded by
the existing local-search factor. Prefix generation, suffix tables and the
sorted physical lookup index are all charged in the complete bound below.
-/

namespace ThreeSum.SharedReportingCosts

open Scales CostLedger ReportingHostPrefixCatalog

set_option maxHeartbeats 1700000
set_option maxRecDepth 10000

def half (n : ℕ) : ℕ := microHalf (inputBits n)
def blocks (n : ℕ) : ℕ := blockCount (inputBits n)
def localWidth (n : ℕ) : ℕ := 512*half n
def width (n : ℕ) : ℕ := blocks n*localWidth n
def localCount (n : ℕ) : ℕ := LightReportingPrefixArrays.localCount (localWidth n) (half n)

def overhead (n : ℕ) : ℕ :=
  100000*(width n+1)^5+5000*(localWidth n+1)^2*(localSearch 257 n+1)+
    1200*(blocks n+1)+2000*(width n+1)+1050

def time (n k : ℕ) : ℕ := LightReportingCatalogIndex.time (half n) (blocks n) k
  (Switch.residualSize n k-Switch.actualSwitch n k)

/-- The complete local row-pair enumeration is a subpolynomial microblock
factor, including at level zero where the prefix count itself is one. -/
theorem local_count_le_search (n : ℕ) : localCount n ≤ localSearch 257 n := by
  have hsize : 2*half n=muZero n := rfl
  unfold localCount LightReportingPrefixArrays.localCount localWidth
  calc
    _ ≤ 2^(512*half n)*2^(2*half n) :=
      Nat.mul_le_mul (Nat.choose_le_two_pow _ _) (Nat.choose_le_two_pow _ _)
    _ = 2^(257*(2*half n)) := by rw [← pow_add]; congr 1; ring
    _ = 2^(257*muZero n) := by rw [hsize]
    _ ≤ localSearch 257 n :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 257 (Nat.le_self_pow (by decide : (2 : ℕ) ≠ 0) _))

theorem prefix_count_eq (n k : ℕ) :
    LightReportingPrefixCatalog.count (half n) k=prefixChoices n k := by
  have hcard : LightReportingPrefixCatalog.count (half n) k=Fintype.card (Prefix (half n) k) := by
    rw [prefix_card]
    rfl
  exact hcard.trans (ReportingHostCatalogCosts.prefix_card_eq_ledger rfl)

theorem prefix_count_le_boxes (n k : ℕ) :
    LightReportingPrefixCatalog.count (half n) k ≤ prefixBoxes n k := by
  rw [prefix_count_eq]
  exact Nat.le_mul_of_pos_right _ (suffixBoxes_pos n k)

/-- Every operation in the closed52-procedure constructor is included. -/
theorem time_le_boxes {n k : ℕ} (hk : k ≤ blocks n) :
    time n k ≤ overhead n*prefixBoxes n k := by
  let N := LightReportingPrefixCatalog.count (half n) k
  let X := prefixBoxes n k
  have hX : 0 < X := prefixBoxes_pos n k
  have hN : N ≤ X := prefix_count_le_boxes n k
  have hN1 : N+1 ≤ 2*X := by omega
  have hlocal := LightReportingPrefixArrays.time_bound (L := localWidth n) (h := half n) (k := k)
    (by unfold localWidth; omega)
  have hE := local_count_le_search n
  have hlocalTerm := Nat.mul_le_mul_left (5000*(localWidth n+1)^2) (Nat.add_le_add_right hE 1)
  have hlocalTermX := (Nat.le_mul_of_pos_right
    (5000*(localWidth n+1)^2*(localSearch 257 n+1)) hX)
  have hprefixTerm := Nat.mul_le_mul (Nat.mul_le_mul_left 600 (Nat.add_le_add_right hk 1)) hN1
  have hprefixTime : LightReportingPrefixArrays.time (localWidth n) (half n) k ≤
      (5000*(localWidth n+1)^2*(localSearch 257 n+1))*X+1200*(blocks n+1)*X+300 := by
    change LightReportingPrefixArrays.time (localWidth n) (half n) k ≤
      5000*(localWidth n+1)^2*(localCount n+1)+600*(k+1)*(N+1)+300 at hlocal
    have hprefixTerm' : 600*(k+1)*(N+1) ≤ 1200*(blocks n+1)*X := by
      convert hprefixTerm using 1 <;> ring
    omega
  have hsuffix := ReportingHostCatalogCosts.actual_catalog_time_le_prefixBoxes hk
  have hcard : Fintype.card (Prefix (half n) k)=N := by rw [prefix_card]; rfl
  change LightReportingSuffixCatalogSetup.time (width n) ((blocks n-k)*localWidth n)
    (Switch.residualSize n k-Switch.actualSwitch n k) (k*localWidth n)
    (Fintype.card (Prefix (half n) k)) ≤ 100000*(width n+1)^5*X at hsuffix
  rw [hcard] at hsuffix
  change LightReportingSuffixCatalogSetup.time (width n) ((blocks n-k)*localWidth n)
    (Switch.residualSize n k-Switch.actualSwitch n k) (k*localWidth n) N ≤
    100000*(width n+1)^5*X at hsuffix
  have hsort := ReportingHostCatalogIndexCosts.prefix_index_setup_time_le
    (h := half n) (J := blocks n) hk
  change LightReportingSortedCatalog.time (width n) N ≤ 1000*(width n+1)*(N+1) at hsort
  have hsortX : LightReportingSortedCatalog.time (width n) N ≤ 2000*(width n+1)*X := by
    calc
      _ ≤ 1000*(width n+1)*(N+1) := hsort
      _ ≤ 1000*(width n+1)*(2*X) := Nat.mul_le_mul_left _ hN1
      _ = _ := by ring
  have hconstant : 1050 ≤ 1050*X := Nat.le_mul_of_pos_right _ hX
  unfold time LightReportingCatalogIndex.time LightReportingPrefixCatalog.time
  change LightReportingPrefixArrays.time (localWidth n) (half n) k+
    LightReportingSuffixCatalogSetup.time (width n) ((blocks n-k)*localWidth n)
      (Switch.residualSize n k-Switch.actualSwitch n k) (k*localWidth n) N+500+
    LightReportingSortedCatalog.time (width n) N+250 ≤ overhead n*X
  unfold overhead
  simp only [Nat.add_mul]
  omega

theorem terminal_le_blocks (n : ℕ) : Switch.terminalDepth n ≤ blocks n := by
  have hh := Switch.actual_depth_condition (n := n) (le_refl (Switch.terminalDepth n))
  change 20*Switch.terminalDepth n ≤ 13*blocks n at hh
  omega

def levelsTime (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (Switch.terminalDepth n+1), time n k

def sharedTime (n : ℕ) : ℕ :=
  3*CostLedger.bandCount n^2*TrimScales.scheduleCount n*levelsTime n

def budget (n : ℕ) : ℕ := overhead n*StageBounds.boxCount n

theorem levels_time_le (n : ℕ) : levelsTime n ≤ overhead n*allPrefixBoxes n := by
  unfold levelsTime allPrefixBoxes
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  apply time_le_boxes
  exact (Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans (terminal_le_blocks n)

theorem shared_time_le (n : ℕ) : sharedTime n ≤ budget n := by
  have hh := Nat.mul_le_mul_left
    (3*CostLedger.bandCount n^2*TrimScales.scheduleCount n) (levels_time_le n)
  unfold sharedTime budget StageBounds.boxCount
  convert hh using 1 <;> ring

end ThreeSum.SharedReportingCosts
