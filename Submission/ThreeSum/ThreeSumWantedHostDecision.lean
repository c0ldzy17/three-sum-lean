import Submission.ThreeSum.ThreeSumWantedHostConditions
import Submission.ThreeSum.ReportingHostWantedConsumerScanData
import Submission.ThreeSum.SharedReportingBankResourceBoundsWantedMassStored

/-!
# The physical whole-scan decision is exactly an original color witness

The concrete threshold is the retained weighted false score, and the
auxiliary pool separates every original difference in the uniform size
regime. No input-dependent primality or correctness premise is added.
-/

namespace ThreeSum.ThreeSumWantedHostDecision

open Light Scales BandScales BandRawA RawIncidences RawReporting
open ReportingHostWantedConsumerData ThreeSumWantedHostData
open ThreeSumWantedHostConditions SharedReportingBankResourceBounds

set_option maxHeartbeats 1800000
set_option maxRecDepth 15000

theorem accepted_iff_witness {μ : ℕ→ℤ} {free n k : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hn : Ready k n) (hx : ∀ i, |x i|≤((n^k : ℕ) : ℤ)) :
    LightReportingWantedScan.Accepted (mass H) (hit H)
      (threshold n A B C hsA hsB hsC) (count n A B C hsA hsB hsC) ↔
        ColorClassLists.witness color x := by
  have hh := ReportingHostWantedDecision.accepted_iff_original H.wanted
    (fun j => B.getD j 0) (fun j => C.getD j 0) B.length C.length
    (LightSwitchDepth.depth (blocks n)) (ThreeSumColorBudgets.falseScore n A B C hsA hsB hsC)
    (DenseGuard.actualAux n) hn.half
    (by change 13*blockCount (inputBits n)/20≤blockCount (inputBits n); omega)
    EncodedColorPrimeReadyData.selected_pos (wanted_selected_guard hn.radix)
    (actual_separation H hn hx) (le_refl _)
  change LightReportingWantedScan.Accepted (mass H) (hit H)
      (threshold n A B C hsA hsB hsC)
      (μ (EncodedColorPipelineData.wantedHeader free n
        (EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length)).toNat ↔
        OriginalZero n A B C hsA hsB hsC at hh
  rw [count_read H,Int.toNat_natCast] at hh
  exact hh.trans (original_zero_iff_witness H)

end ThreeSum.ThreeSumWantedHostDecision
