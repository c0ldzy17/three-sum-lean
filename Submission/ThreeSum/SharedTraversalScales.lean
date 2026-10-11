import Submission.ThreeSum.SharedTraversalCostBounds
import Submission.ThreeSum.SharedReportingCostBounds
import Submission.ThreeSum.SharedReportingBankAccess
import Submission.ThreeSum.UniformStageBounds

/-!
# The physical reporting catalogs use the certified traversal ledger

The switch in every retained catalog is the literal switch used by the
original finite ledger. This module connects the executed level and terminal
costs to those exact binomial terms, preserving the sum over levels.
-/

namespace ThreeSum.SharedTraversalCosts

open Finset Scales LocalCoverBounds LightBlockQuery ReportingHostLevelData
open StageBounds CostLedger
open scoped BigOperators

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000

def half (n : ℕ) : ℕ := microHalf (inputBits n)
def blocks (n : ℕ) : ℕ := blockCount (inputBits n)
def scaledOverhead (n : ℕ) : ℕ := overhead (half n) (blocks n)

theorem residual_eq (n k : ℕ) :
    residualSize (half n) (blocks n) k=Switch.residualSize n k := rfl

theorem group_eq (n : ℕ) : groupSize (half n)=microPartitions n := by
  have hsize : 2*half n=muZero n := rfl
  have hhalf : muZero n/2=half n := by omega
  simp only [groupSize,microPartitions,hsize,hhalf]

theorem terminal_le_blocks (n : ℕ) : Switch.terminalDepth n ≤ blocks n :=
  SharedReportingCosts.terminal_le_blocks n

theorem terminal_eq_depth (n : ℕ) : Switch.terminalDepth n=LightSwitchDepth.depth (blocks n) := rfl

theorem switch_le_half {n k : ℕ} (hk : k ≤ Switch.terminalDepth n) :
    Switch.actualSwitch n k ≤ Switch.residualSize n k/2 := by
  have hn := SharedReportingBankLevels.candidates_nonempty
    (h := half n) (J := blocks n) (k := k) hk
  have hm := (Switch.mem_candidates.mp (Switch.switchIndex_mem hn)).1
  have hr : SharedReportingBankLevels.residual (half n) (blocks n) k=Switch.residualSize n k := by
    rw [← residual_eq]
    unfold SharedReportingBankLevels.residual residualSize
    ring
  rw [hr] at hm
  exact hm

theorem query_terms_pos {n k : ℕ} (hk : k ≤ Switch.terminalDepth n) : 0 < queryTerms n k :=
  Nat.choose_pos ((switch_le_half hk).trans (Nat.div_le_self _ _))

def CatalogScales (n : ℕ) (D : ℕ → Catalog) : Prop :=
  ∀ k ≤ Switch.terminalDepth n, (D k).t=Switch.actualSwitch n k

theorem physical_catalog_scales (n report NB NC g s i j : ℕ) :
    CatalogScales n (SharedReportingBankAccess.levelCatalog report (half n) (blocks n) NB NC g s i j) := by
  intro k hk
  change SharedReportingBankLevels.switch (half n) (blocks n) k=Switch.actualSwitch n k
  unfold SharedReportingBankLevels.switch Switch.actualSwitch
  congr 1
  rw [← residual_eq]
  unfold SharedReportingBankLevels.residual residualSize
  ring

theorem initial_le_scaled {n : ℕ} (D : ℕ → Catalog) (hD : CatalogScales n D) :
    initialUnit (half n) (blocks n) D (Switch.terminalDepth n) ≤
      scaledOverhead n*queryTerms n 0 := by
  have ht : (D 0).t ≤ residualSize (half n) (blocks n) 0/2 := by
    rw [hD 0 (by omega),residual_eq]
    exact switch_le_half (by omega)
  have hh := initial_le_layer D (terminal_le_blocks n) ht
  simpa only [scaledOverhead,queryTerms,residual_eq,hD 0 (by omega)] using hh

theorem level_unit_le_scaled {n : ℕ} (D : ℕ → Catalog) (hD : CatalogScales n D) :
    levelUnit (half n) (blocks n) D (Switch.terminalDepth n) ≤
      scaledOverhead n*microPartitions n*allQueryTerms n := by
  have hterm (k : ℕ) (hk : k < Switch.terminalDepth n) :
      LightReportingPositiveExpand.time (half n) (blocks n) k (D (k+1)).t+200 ≤
        scaledOverhead n*microPartitions n*queryTerms n (k+1) := by
    have hkJ := hk.trans_le (terminal_le_blocks n)
    have hkp : k+1 ≤ Switch.terminalDepth n := hk
    have ht : (D (k+1)).t ≤ residualSize (half n) (blocks n) (k+1)/2 := by
      rw [hD (k+1) hkp,residual_eq]
      exact switch_le_half hkp
    have hh := expansion_le_layer hkJ ht
    simpa only [scaledOverhead,queryTerms,group_eq,residual_eq,hD (k+1) hkp] using hh
  have hs : (∑ k ∈ range (Switch.terminalDepth n), queryTerms n (k+1)) ≤ allQueryTerms n := by
    unfold allQueryTerms
    rw [sum_range_succ']
    omega
  calc
    _ ≤ ∑ k ∈ range (Switch.terminalDepth n),
        scaledOverhead n*microPartitions n*queryTerms n (k+1) :=
      sum_le_sum (fun k hk => hterm k (mem_range.mp hk))
    _ = scaledOverhead n*microPartitions n*
        (∑ k ∈ range (Switch.terminalDepth n), queryTerms n (k+1)) := (mul_sum _ _ _).symm
    _ ≤ _ := Nat.mul_le_mul_left _ hs

theorem terminal_charge_le_scaled (n : ℕ) :
    ReportingHostTerminalFrontier.charge (half n) (blocks n) (Switch.terminalDepth n)+240 ≤
      scaledOverhead n*terminalChoices n := by
  have hh := terminal_charge_le (half n) (blocks n) (Switch.terminalDepth n)
  have hp := (size_bounds (half n) (blocks n)).1
  have hpow := Nat.pow_le_pow_right hp (by decide : 2 ≤ 4)
  have hscalar : 31000*size (half n) (blocks n)^2 ≤ scaledOverhead n :=
    Nat.mul_le_mul (by decide) hpow
  have he : 2^((blocks n-Switch.terminalDepth n)*(2*half n))=terminalChoices n := rfl
  rw [he] at hh
  exact hh.trans (Nat.mul_le_mul_right _ hscalar)

theorem search_unit_le_scaled {n : ℕ} (D : ℕ → Catalog) (hD : CatalogScales n D) :
    searchUnit (half n) (blocks n) D (Switch.terminalDepth n) ≤
      scaledOverhead n*(microPartitions n*allQueryTerms n+terminalChoices n) := by
  have hl := level_unit_le_scaled D hD
  have ht := terminal_charge_le_scaled n
  unfold searchUnit
  nlinarith only [hl,ht]

def traversalBudget (k n : ℕ) : ℕ := 30+scaledOverhead n*
  (initialCount UniformStageBounds.wantedBudget n+
    activeCount (UniformStageBounds.falseBudget k) n+
    terminalCount (UniformStageBounds.falseBudget k) n)

/-- The actual cumulative guard and the physical catalog dimensions remove
all input-dependent reporting masses from the time bound. -/
theorem prefix_time_le_budget {time mass : ℕ → ℕ} {n k threshold count : ℕ}
    (hzero : time 0 ≤ 30)
    (hstep : ∀ i, time (i+1) ≤ time i+scaledOverhead n*queryTerms n 0+
      if threshold < prefixMass mass i+mass i then 0 else
        mass i*(scaledOverhead n*(microPartitions n*allQueryTerms n+terminalChoices n)))
    (hcount : count ≤ UniformStageBounds.wantedBudget n)
    (hthreshold : threshold ≤ UniformStageBounds.falseBudget k n*TrimScales.representationBound n) :
    time count ≤ traversalBudget k n := by
  have ht := prefix_time_le hzero hstep count
  have hi := Nat.mul_le_mul_right (scaledOverhead n*queryTerms n 0) hcount
  have ha := Nat.mul_le_mul_right
    (scaledOverhead n*(microPartitions n*allQueryTerms n+terminalChoices n)) hthreshold
  have hsum := ht.trans (Nat.add_le_add (Nat.add_le_add_left hi 30) ha)
  unfold traversalBudget initialCount activeCount terminalCount
  calc
    time count ≤ (30+UniformStageBounds.wantedBudget n*(scaledOverhead n*queryTerms n 0)+
        UniformStageBounds.falseBudget k n*TrimScales.representationBound n*
          (scaledOverhead n*(microPartitions n*allQueryTerms n+terminalChoices n)))+
        scaledOverhead n*UniformStageBounds.falseBudget k n*TrimScales.representationBound n*terminalChoices n :=
      hsum.trans (Nat.le_add_right _ _)
    _ = _ := by ring

open Filter Real Parameters
open scoped Topology

noncomputable section

theorem size_powerBound : PowerBound (fun n => size (half n) (blocks n)) 0 := by
  have hh : PowerBound half 0 := SharedReportingCosts.half_powerBound
  have hj : PowerBound blocks 0 := SharedReportingCosts.blocks_powerBound
  have hl : PowerBound (fun n => 2048*half n+20) 0 := by
    have hm : PowerBound (fun n => 2048*half n) 0 := by
      simpa only [zero_add] using (PowerBound.const 2048).mul hh
    exact hm.add_same (PowerBound.const 20)
  change PowerBound (fun n => (blocks n+1)*(2048*half n+20)) 0
  simpa only [zero_add] using (hj.add_same (PowerBound.const 1)).mul hl

theorem overhead_powerBound : PowerBound scaledOverhead 0 := by
  change PowerBound (fun n => 200000*(size (half n) (blocks n))^4) 0
  simpa only [zero_add,mul_zero] using (PowerBound.const 200000).mul (size_powerBound.pow 4)

theorem traversal_counts_powerBound (k : ℕ) : PowerBound
    (fun n => initialCount UniformStageBounds.wantedBudget n+
      activeCount (UniformStageBounds.falseBudget k) n+
      terminalCount (UniformStageBounds.falseBudget k) n) certificateExponent := by
  have hi := UniformStageBounds.budget_initial_powerBound.mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have ha := (UniformStageBounds.budget_active_powerBound k).mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have ht := (UniformStageBounds.budget_terminal_powerBound k).mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  exact (hi.add_same ha).add_same ht

theorem traversalBudget_powerBound (k : ℕ) : PowerBound (traversalBudget k) certificateExponent := by
  have hprod : PowerBound (fun n => scaledOverhead n*
      (initialCount UniformStageBounds.wantedBudget n+
        activeCount (UniformStageBounds.falseBudget k) n+
        terminalCount (UniformStageBounds.falseBudget k) n)) certificateExponent := by
    simpa only [zero_add] using overhead_powerBound.mul (traversal_counts_powerBound k)
  have hconst := (PowerBound.const 30).mono_exponent
    (by unfold certificateExponent; norm_num : (0 : ℝ) ≤ certificateExponent)
  exact hconst.add_same hprod

theorem traversalBudget_endStatementBigO (k : ℕ) :
    EndStatement.BigO (traversalBudget k) (981/500 : Rat) := by
  apply BudgetTime.endStatementBigO_of_eventually_le_rpow (by norm_num)
  have hh := (traversalBudget_powerBound k) (targetExponent-certificateExponent)
    (sub_pos.mpr certificate_lt_target)
  simpa [targetExponent] using hh

end
end ThreeSum.SharedTraversalCosts
