import Submission.ThreeSum.LightSharedReportingHost
import Submission.ThreeSum.LightSwitchCosts

/-!
# Charge the executed shared catalog bank, including every surrounding loop

The exact sum of level costs is preserved. Actual switch evaluation,
downset sizing, address arithmetic, row iteration, and the one-time depth
and Pascal initializers add only a factor of exponent zero to the existing
shared-box ledger. The bank is indexed by occurrence and two bands alone.
-/

namespace ThreeSum.SharedReportingBankCosts

open Scales Parameters StageBounds ArithmeticStageBounds CostLedger Filter
open SharedReportingCosts
open scoped Topology

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

def roundExtra (n : ℕ) : ℕ :=
  LightSwitchCosts.timeBudget n+1400*(width n+1)^2+2808
def roundOverhead (n : ℕ) : ℕ := SharedReportingCosts.overhead n+roundExtra n
def setup (n : ℕ) : ℕ :=
  LightSwitchCosts.depthBudget n+1500*(localWidth n+1)^2+3300
def overhead (n : ℕ) : ℕ := roundOverhead n+1600+setup n
def budget (n : ℕ) : ℕ := overhead n*(boxCount n+1)

theorem residual_eq (n k : ℕ) :
    SharedReportingBankLevels.residual (half n) (blocks n) k=Switch.residualSize n k := by
  unfold SharedReportingBankLevels.residual half blocks Switch.residualSize muZero microSize microHalf
  ring

theorem cut_eq (n k : ℕ) :
    SharedReportingBankLevels.boxCut (half n) (blocks n) k=
      Switch.residualSize n k-Switch.actualSwitch n k := by
  unfold SharedReportingBankLevels.boxCut SharedReportingBankLevels.switch
  rw [residual_eq]
  rfl

theorem levels_eq (n : ℕ) : SharedReportingBankHeader.levels (blocks n)=Switch.terminalDepth n+1 := rfl

theorem round_time_le {n k : ℕ} (hk : k ≤ blocks n) :
    LightSharedReportingLevels.roundTime (half n) (blocks n) k+8 ≤
      roundOverhead n*prefixBoxes n k := by
  have hV : (blocks n-k)*(512*half n) ≤ width n :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hdownset := (LightDownsetSize.time_bound ((blocks n-k)*(512*half n))).trans
    (Nat.mul_le_mul_left 1400 (Nat.pow_le_pow_left (Nat.add_le_add_right hV 1) 2))
  have hswitch := LightSwitchCosts.time_le_budget n k
  rw [← residual_eq] at hswitch
  have hcatalog := SharedReportingCosts.time_le_boxes hk
  have hextra : LightSwitch.time (SharedReportingBankLevels.residual (half n) (blocks n) k)+
      LightDownsetSize.time ((blocks n-k)*(512*half n))+2808 ≤ roundExtra n := by
    unfold roundExtra
    omega
  have hextraBoxes := Nat.le_mul_of_pos_right (roundExtra n) (prefixBoxes_pos n k)
  unfold LightSharedReportingLevels.roundTime LightSharedReportingCell.time LightSharedReportingEntry.time
  rw [cut_eq]
  change _ ≤ (SharedReportingCosts.overhead n+roundExtra n)*prefixBoxes n k
  change LightReportingCatalogIndex.time (half n) (blocks n) k
    (Switch.residualSize n k-Switch.actualSwitch n k) ≤
    SharedReportingCosts.overhead n*prefixBoxes n k at hcatalog
  rw [Nat.add_mul]
  omega

theorem all_prefix_pos (n : ℕ) : 0 < allPrefixBoxes n := by
  have h0 : 0 ∈ Finset.range (Switch.terminalDepth n+1) := by simp
  have hh := Finset.single_le_sum (f := fun k => prefixBoxes n k) (fun k _ => Nat.zero_le _) h0
  exact (prefixBoxes_pos n 0).trans_le hh

theorem pair_time_le (n : ℕ) :
    LightSharedReportingPair.time (half n) (blocks n) (SharedReportingBankHeader.levels (blocks n))+1000 ≤
      (roundOverhead n+1600)*allPrefixBoxes n := by
  have hsum : (∑ k ∈ Finset.range (Switch.terminalDepth n+1),
      (LightSharedReportingLevels.roundTime (half n) (blocks n) k+8)) ≤
      roundOverhead n*allPrefixBoxes n := by
    unfold allPrefixBoxes
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun k hk => round_time_le
      ((Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans (terminal_le_blocks n)))
  have hconstant := Nat.le_mul_of_pos_right 1600 (all_prefix_pos n)
  unfold LightSharedReportingPair.time LightSharedReportingLevels.time
  rw [levels_eq,Nat.add_mul]
  omega

theorem total_le {NB NC n : ℕ} (hB : NB ≤ n) (hC : NC ≤ n) :
    SharedReportingBankRows.total (half n) (blocks n) NB NC (BandScales.bandSize n) ≤
      3*bandCount n^2*TrimScales.scheduleCount n := by
  have hb := SourceBandCosts.size_le_bandCount hB
  have hc := SourceBandCosts.size_le_bandCount hC
  unfold SharedReportingBankRows.total SharedReportingBankRows.pairs
  rw [show LightBlockSourceCatalog.count (half n) (blocks n)=TrimScales.scheduleCount n from
    BlockSourceCatalogCosts.count_eq_scheduleCount n]
  calc
    _ ≤ TrimScales.scheduleCount n*bandCount n*bandCount n :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hb) hc
    _ = bandCount n^2*TrimScales.scheduleCount n := by ring
    _ ≤ 3*bandCount n^2*TrimScales.scheduleCount n := by nlinarith

theorem host_time_le {NB NC n : ℕ} (hB : NB ≤ n) (hC : NC ≤ n) :
    LightSharedReportingHost.time (half n) (blocks n) NB NC (BandScales.bandSize n) ≤ budget n := by
  have hproduct := Nat.mul_le_mul (total_le hB hC) (pair_time_le n)
  have hmain : SharedReportingBankRows.total (half n) (blocks n) NB NC (BandScales.bandSize n)*
      (LightSharedReportingPair.time (half n) (blocks n) (SharedReportingBankHeader.levels (blocks n))+1000) ≤
      (roundOverhead n+1600)*boxCount n := by
    convert hproduct using 1 <;> unfold boxCount <;> ring
  have hdepth := LightSwitchCosts.depth_time_le_budget n
  have hcounts := LightSharedReportingCounts.time_bound (half n)
  change LightSharedReportingCounts.time (half n) ≤ 1500*(localWidth n+1)^2 at hcounts
  change LightSwitchDepth.time (blocks n) ≤ LightSwitchCosts.depthBudget n at hdepth
  unfold LightSharedReportingHost.time LightSharedReportingBank.time
  unfold budget overhead setup
  nlinarith

noncomputable section

theorem round_extra_powerBound : PowerBound roundExtra 0 := by
  have hw := SharedReportingCosts.width_powerBound.add_same (PowerBound.const 1)
  have hpoly : PowerBound (fun n => 1400*(width n+1)^2) 0 := by
    simpa only [mul_zero,zero_add] using (PowerBound.const 1400).mul (hw.pow 2)
  exact (LightSwitchCosts.time_powerBound.add_same hpoly).add_same (PowerBound.const 2808)

theorem round_overhead_powerBound : PowerBound roundOverhead 0 :=
  SharedReportingCosts.overhead_powerBound.add_same round_extra_powerBound

theorem setup_powerBound : PowerBound setup 0 := by
  have hw := SharedReportingCosts.local_width_powerBound.add_same (PowerBound.const 1)
  have hpoly : PowerBound (fun n => 1500*(localWidth n+1)^2) 0 := by
    simpa only [mul_zero,zero_add] using (PowerBound.const 1500).mul (hw.pow 2)
  exact (LightSwitchCosts.depth_powerBound.add_same hpoly).add_same (PowerBound.const 3300)

theorem overhead_powerBound : PowerBound overhead 0 :=
  (round_overhead_powerBound.add_same (PowerBound.const 1600)).add_same setup_powerBound

theorem budget_powerBound : PowerBound budget (2-epsilon*boxSaving) := by
  have hconst : PowerBound (fun _ : ℕ => 1) (2-epsilon*boxSaving) :=
    (PowerBound.const 1).mono_exponent (by norm_num [epsilon,boxSaving])
  change PowerBound (fun n => overhead n*(boxCount n+1)) (2-epsilon*boxSaving)
  simpa only [zero_add] using overhead_powerBound.mul (boxes_powerBound.add_same hconst)

theorem budget_certificate : PowerBound budget certificateExponent :=
  budget_powerBound.mono_exponent (all_costs_le_certificate _ (by simp [costLedger]))

theorem budget_endStatementBigO : EndStatement.BigO budget (981/500 : Rat) := by
  have hh := budget_certificate (targetExponent-certificateExponent) (sub_pos.mpr certificate_lt_target)
  apply BudgetTime.endStatementBigO_of_eventually_le_rpow (by norm_num)
  simpa [targetExponent] using hh

end
end ThreeSum.SharedReportingBankCosts
