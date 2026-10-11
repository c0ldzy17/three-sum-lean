import Submission.ThreeSum.SharedTraversalScales
import Submission.ThreeSum.SharedReportingBankResourceBoundsWantedIndices
import Submission.ThreeSum.LightReportingWantedDecodeAccess
import Submission.ThreeSum.LightReportingWantedLayout

/-!
# Include the executed wanted decoder and scratch-pointer constructor

The actual physical indices have a size-only bound, independently of the
input integer magnitude. Their logarithmic decoder cost and the literal
layout power loop therefore contribute exponent zero. A fixed caller cost
is included explicitly for the remaining register loads and calls.
-/

namespace ThreeSum.SharedTraversalCosts

open Scales StageBounds CostLedger LightBlockQuery

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000

def scalarOverhead (c n : ℕ) : ℕ :=
  800*(blocks n+1)*(8192*(inputBits n+1)+3)+8300+
    20*width (half n) (blocks n)+2520+c

theorem dispatch_time_le (c n : ℕ) :
    LightReportingWantedDecodeAccess.time (blocks n)
        (SharedReportingBankResourceBounds.wantedDecodeV n)+
      LightReportingWantedLayout.time (half n) (blocks n)+c ≤ scalarOverhead c n := by
  have hd := LightWantedDecode.time_bound (blocks n)
    (SharedReportingBankResourceBounds.wantedDecodeV n)
  have hl := SharedReportingBankResourceBounds.wanted_decode_log_le n
  have hb := hd.trans (Nat.mul_le_mul_left (800*(blocks n+1))
    (show Nat.log 2 (SharedReportingBankResourceBounds.wantedDecodeV n+1)+2 ≤
      8192*(inputBits n+1)+3 by omega))
  unfold LightReportingWantedDecodeAccess.time LightReportingWantedLayout.time LightNatPower.time scalarOverhead
  omega

def totalOverhead (c n : ℕ) : ℕ := scaledOverhead n+scalarOverhead c n

def dispatchBudget (c k n : ℕ) : ℕ := 30+totalOverhead c n*
  (initialCount UniformStageBounds.wantedBudget n+
    activeCount (UniformStageBounds.falseBudget k) n+
    terminalCount (UniformStageBounds.falseBudget k) n)

theorem initial_with_dispatch_le {n : ℕ} (c : ℕ) (D : ℕ → ReportingHostLevelData.Catalog)
    (hD : CatalogScales n D) :
    initialUnit (half n) (blocks n) D (Switch.terminalDepth n)+
      LightReportingWantedDecodeAccess.time (blocks n)
        (SharedReportingBankResourceBounds.wantedDecodeV n)+
      LightReportingWantedLayout.time (half n) (blocks n)+c ≤
        totalOverhead c n*queryTerms n 0 := by
  have hi := initial_le_scaled D hD
  have hd := dispatch_time_le c n
  have hq := Nat.le_mul_of_pos_right (scalarOverhead c n)
    (query_terms_pos (n := n) (k := 0) (by omega))
  unfold totalOverhead
  nlinarith only [hi,hd,hq]

theorem prefix_time_le_dispatch_budget {time mass : ℕ → ℕ} {c n k threshold count : ℕ}
    (hzero : time 0 ≤ 30)
    (hstep : ∀ i, time (i+1) ≤ time i+(scaledOverhead n*queryTerms n 0+scalarOverhead c n)+
      if threshold < prefixMass mass i+mass i then 0 else
        mass i*(scaledOverhead n*(microPartitions n*allQueryTerms n+terminalChoices n)))
    (hcount : count ≤ UniformStageBounds.wantedBudget n)
    (hthreshold : threshold ≤ UniformStageBounds.falseBudget k n*TrimScales.representationBound n) :
    time count ≤ dispatchBudget c k n := by
  have ht := prefix_time_le hzero hstep count
  have hq := Nat.le_mul_of_pos_right (scalarOverhead c n)
    (query_terms_pos (n := n) (k := 0) (by omega))
  have hinit : scaledOverhead n*queryTerms n 0+scalarOverhead c n ≤
      totalOverhead c n*queryTerms n 0 := by unfold totalOverhead; nlinarith only [hq]
  have hwork : scaledOverhead n*(microPartitions n*allQueryTerms n+terminalChoices n) ≤
      totalOverhead c n*(microPartitions n*allQueryTerms n+terminalChoices n) :=
    Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  have hi := Nat.mul_le_mul hcount hinit
  have ha := Nat.mul_le_mul hthreshold hwork
  have hs := ht.trans (Nat.add_le_add (Nat.add_le_add_left hi 30) ha)
  unfold dispatchBudget initialCount activeCount terminalCount
  calc
    time count ≤ (30+UniformStageBounds.wantedBudget n*(totalOverhead c n*queryTerms n 0)+
        UniformStageBounds.falseBudget k n*TrimScales.representationBound n*
          (totalOverhead c n*(microPartitions n*allQueryTerms n+terminalChoices n)))+
        totalOverhead c n*UniformStageBounds.falseBudget k n*TrimScales.representationBound n*terminalChoices n :=
      hs.trans (Nat.le_add_right _ _)
    _ = _ := by ring

open Filter Real Parameters
open scoped Topology

noncomputable section

theorem scalar_overhead_powerBound (c : ℕ) : PowerBound (scalarOverhead c) 0 := by
  have hb := SharedReportingCosts.bits_powerBound
  have hj : PowerBound blocks 0 := SharedReportingCosts.blocks_powerBound
  have hw : PowerBound (fun n => width (half n) (blocks n)) 0 := SharedReportingCosts.width_powerBound
  have hlog : PowerBound (fun n => 8192*(inputBits n+1)+3) 0 := by
    have hh : PowerBound (fun n => 8192*(inputBits n+1)) 0 := by
      simpa only [zero_add] using (PowerBound.const 8192).mul (hb.add_same (PowerBound.const 1))
    exact hh.add_same (PowerBound.const 3)
  have hd : PowerBound (fun n => 800*(blocks n+1)*(8192*(inputBits n+1)+3)) 0 := by
    simpa only [zero_add] using ((PowerBound.const 800).mul (hj.add_same (PowerBound.const 1))).mul hlog
  have hwidth : PowerBound (fun n => 20*width (half n) (blocks n)) 0 := by
    simpa only [zero_add] using (PowerBound.const 20).mul hw
  exact (((hd.add_same (PowerBound.const 8300)).add_same hwidth).add_same
    (PowerBound.const 2520)).add_same (PowerBound.const c)

theorem total_overhead_powerBound (c : ℕ) : PowerBound (totalOverhead c) 0 :=
  overhead_powerBound.add_same (scalar_overhead_powerBound c)

theorem dispatchBudget_powerBound (c k : ℕ) : PowerBound (dispatchBudget c k) certificateExponent := by
  have hp : PowerBound (fun n => totalOverhead c n*
      (initialCount UniformStageBounds.wantedBudget n+
        activeCount (UniformStageBounds.falseBudget k) n+
        terminalCount (UniformStageBounds.falseBudget k) n)) certificateExponent := by
    simpa only [zero_add] using (total_overhead_powerBound c).mul (traversal_counts_powerBound k)
  exact ((PowerBound.const 30).mono_exponent
    (by unfold certificateExponent; norm_num : (0 : ℝ) ≤ certificateExponent)).add_same hp

theorem dispatchBudget_endStatementBigO (c k : ℕ) :
    EndStatement.BigO (dispatchBudget c k) (981/500 : Rat) := by
  apply BudgetTime.endStatementBigO_of_eventually_le_rpow (by norm_num)
  have hh := (dispatchBudget_powerBound c k) (targetExponent-certificateExponent)
    (sub_pos.mpr certificate_lt_target)
  simpa [targetExponent] using hh

end
end ThreeSum.SharedTraversalCosts
