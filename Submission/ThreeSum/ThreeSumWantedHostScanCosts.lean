import Submission.ThreeSum.ThreeSumWantedHostCosts
import Submission.ThreeSum.ThreeSumWantedHostConditions
import Submission.ThreeSum.ReportingHostWantedConsumerScanData

/-! # The exact physical scan fits the uniform selected-color budget -/

namespace ThreeSum.ThreeSumWantedHostCosts

open Light Scales BandScales BandRawA RawReporting RawIncidences GlobalEncoding
open ReportingHostWantedConsumerData SharedTraversalCosts ThreeSumWantedHostData

set_option maxHeartbeats 1800000
set_option maxRecDepth 15000

variable {μ : ℕ→ℤ} {free n k : ℕ}
  {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

theorem physical_steps_le
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) (i : ℕ) :
    stepTime H i+300≤slotEnvelope n (threshold n A B C hsA hsB hsC) (mass H) i := by
  by_cases hi : i<count n A B C hsA hsB hsC
  · have hh := physical_step_le (free := free)
      (output := outputIndex μ (config free n A B C hsA hsB hsC) i)
      (old := prefixMass (mass H) i) (threshold := threshold n A B C hsA hsB hsC)
      (label H ⟨i,hi⟩) (label_key H ⟨i,hi⟩)
    rw [stepTime_at H ⟨i,hi⟩]
    unfold slotEnvelope
    rw [mass_at H ⟨i,hi⟩]
    exact hh
  · simp only [stepTime,dif_neg hi]
    unfold slotEnvelope scalarOverhead
    omega

theorem physical_scan_time_le
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hn : ThreeSumWantedHostConditions.Ready k n)
    (hx : ∀ i, |x i|≤((n^k : ℕ) : ℤ)) :
    scanTime H≤dispatchBudget 4800 k n := by
  apply actual_scan_time_le (physical_steps_le H)
  · have hh := ThreeSumColorBudgets.wanted_count_le H
    rwa [count_read H,Int.toNat_natCast] at hh
  · exact ThreeSumColorBudgets.threshold_le_budget H hn.divisor hx

theorem physical_color_time_le
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hn : ThreeSumWantedHostConditions.Ready k n)
    (hx : ∀ i, |x i|≤((n^k : ℕ) : ℤ)) :
    EncodedColorReportingCosts.time n (n^k)+scanTime H+4300≤colorBudget k n := by
  have hh := physical_scan_time_le H hn hx
  unfold colorBudget
  omega

end ThreeSum.ThreeSumWantedHostCosts
