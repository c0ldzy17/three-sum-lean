import Submission.ThreeSum.SharedTraversalDispatchCosts
import Submission.ThreeSum.LightReportingWantedScan
import Submission.ThreeSum.EncodedColorReportingCosts

/-!
# Charge the actual fixed153 wanted scan and fixed154 header caller

The concrete dispatcher contributes4500 operations, and the ascending
recursion contributes300 per slot. The exact active-branch mass remains
inside the cumulative guard until the original reporting ledger is applied.
-/

namespace ThreeSum.SharedTraversalCosts

open Light Finset Scales BandScales GlobalEncoding RawIncidences RawReporting
open ReportingHostLevelData StageBounds CostLedger
open ReportingHostFrontierLayout Parameters

set_option maxHeartbeats 1800000
set_option maxRecDepth 14000

def slotEnvelope (n threshold : ℕ) (mass : ℕ→ℕ) (i : ℕ) : ℕ :=
  scaledOverhead n*queryTerms n 0+scalarOverhead 4800 n+
    if threshold<prefixMass mass i+mass i then 0 else
      mass i*(scaledOverhead n*(microPartitions n*allQueryTerms n+terminalChoices n))

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem actual_dispatch_step_le {n NL NR old threshold : ℕ}
    {cfg : LightReportingWantedDispatch.Config}
    (hcH : cfg.h=half n) (hcJ : cfg.J=blocks n)
    (p : ℕ) (shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ) (left right : ℕ→ℤ)
    (eL : Fin NL≃B) (eR : Fin NR≃C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i))
    (hvR : ∀ i : Fin NR, right i.val=c (eR i))
    (w : Wanted (half n) (blocks n) α) (D : ℕ→Catalog)
    (hD : CatalogScales n D)
    (hkey : w.1∈A ∧ globalModulus (half n) (blocks n)∣
      (a w.1%(p : ℤ)+lift w.2.1*(p : ℤ)+shift)-globalKey w.2.2) :
    let I := rawOn (half n) (blocks n) (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
    LightReportingWantedDispatch.time cfg (SharedReportingBankResourceBounds.wantedDecodeV n)
      (LightReportingWanted.time p shift left right NL NR old threshold I w D (Switch.terminalDepth n))+300 ≤
        scaledOverhead n*queryTerms n 0+scalarOverhead 4800 n+
          if threshold<old+rootMass I w then 0 else
            rootMass I w*(scaledOverhead n*(microPartitions n*allQueryTerms n+terminalChoices n)) := by
  dsimp only
  let I := rawOn (half n) (blocks n) (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
  have hr := wanted_time_le (old := old) (threshold := threshold) p shift A B C a b c
    left right eL eR hvL hvR w D (terminal_le_blocks n) hkey
  have hi := initial_le_scaled D hD
  have hw := Nat.mul_le_mul_left (rootMass I w) (search_unit_le_scaled D hD)
  have hd := dispatch_time_le 4800 n
  change LightReportingWanted.time p shift left right NL NR old threshold I w D (Switch.terminalDepth n) ≤
    initialUnit (half n) (blocks n) D (Switch.terminalDepth n)+
      (if threshold<old+rootMass I w then 0 else
        rootMass I w*searchUnit (half n) (blocks n) D (Switch.terminalDepth n)) at hr
  change LightReportingWantedDispatch.time cfg (SharedReportingBankResourceBounds.wantedDecodeV n)
      (LightReportingWanted.time p shift left right NL NR old threshold I w D (Switch.terminalDepth n))+300 ≤
    scaledOverhead n*queryTerms n 0+scalarOverhead 4800 n+
      if threshold<old+rootMass I w then 0 else
        rootMass I w*(scaledOverhead n*(microPartitions n*allQueryTerms n+terminalChoices n))
  unfold LightReportingWantedDispatch.time
  rw [hcH,hcJ]
  by_cases hg : threshold<old+rootMass I w
  · simp only [if_pos hg] at hr ⊢
    omega
  · simp only [if_neg hg] at hr ⊢
    omega

/-- The time recurrence is the one proved for the actual153 executable. -/
theorem actual_scan_time_le {n k threshold count : ℕ} {mass stepTime : ℕ→ℕ}
    (hstep : ∀ i, stepTime i+300≤slotEnvelope n threshold mass i)
    (hcount : count≤UniformStageBounds.wantedBudget n)
    (hthreshold : threshold≤UniformStageBounds.falseBudget k n*TrimScales.representationBound n) :
    LightReportingWantedScan.time stepTime count≤dispatchBudget 4800 k n := by
  apply prefix_time_le_dispatch_budget (mass := mass) (threshold := threshold)
    (by rfl) _ hcount hthreshold
  intro i
  rw [LightReportingWantedScan.time]
  have hh := hstep i
  unfold slotEnvelope at hh
  omega

def colorBudget (k n : ℕ) : ℕ :=
  EncodedColorReportingCosts.time n (n^k)+dispatchBudget 4800 k n+5000

theorem header_and_prelude_time_le {n k threshold count : ℕ} {mass stepTime : ℕ→ℕ}
    (hstep : ∀ i, stepTime i+300≤slotEnvelope n threshold mass i)
    (hcount : count≤UniformStageBounds.wantedBudget n)
    (hthreshold : threshold≤UniformStageBounds.falseBudget k n*TrimScales.representationBound n) :
    EncodedColorReportingCosts.time n (n^k)+LightReportingWantedScan.time stepTime count+4300≤
      colorBudget k n := by
  have hh := actual_scan_time_le hstep hcount hthreshold
  unfold colorBudget
  omega

noncomputable section

theorem color_budget_powerBound (k : ℕ) : PowerBound (colorBudget k) certificateExponent := by
  have hp := EncodedColorReportingCosts.time_powerBound k
  have hr := dispatchBudget_powerBound 4800 k
  exact (hp.add_same hr).add_same ((PowerBound.const 5000).mono_exponent
    (by unfold certificateExponent; norm_num))

theorem color_budget_endStatementBigO (k : ℕ) :
    EndStatement.BigO (colorBudget k) (981/500 : Rat) := by
  apply BudgetTime.endStatementBigO_of_eventually_le_rpow (by norm_num)
  have hh := (color_budget_powerBound k) (Parameters.targetExponent-certificateExponent)
    (sub_pos.mpr certificate_lt_target)
  simpa [Parameters.targetExponent] using hh

end
end ThreeSum.SharedTraversalCosts
