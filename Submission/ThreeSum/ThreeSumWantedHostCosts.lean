import Submission.ThreeSum.SharedTraversalScanCosts
import Submission.ThreeSum.ReportingHostWantedConsumerData

/-! # The retained physical wanted record uses the certified per-slot ledger -/

namespace ThreeSum.ThreeSumWantedHostCosts

open Light Scales BandScales BandRawA RawReporting RawIncidences GlobalEncoding
open ReportingHostWantedOriginal ReportingHostWantedConsumerData SharedTraversalCosts

set_option maxHeartbeats 1800000
set_option maxRecDepth 14000

theorem physical_step_le {free n output old threshold : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (w : Label n A B C hsA hsB hsC)
    (hkey : globalModulus (half n) (blocks n) ∣
      valueAt A.length (bandSize n) (EncodedColorWantedConsumerData.records n A B C hsA hsB hsC)
        (fun j => A.getD j 0) w.1.val%(EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)+
      lift w.2.1*(EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)+
      ThreeSumReportingSetupData.shift n A B C hsA hsB hsC-globalKey w.2.2) :
    LightReportingWantedDispatch.time (ThreeSumWantedHostData.config free n A B C hsA hsB hsC)
      (SharedReportingBankResourceBounds.wantedDecodeV n)
      (recordTime free n A B C hsA hsB hsC w output old threshold)+300 ≤
      scaledOverhead n*CostLedger.queryTerms n 0+scalarOverhead 4800 n+
        if threshold<old+labelMass n A B C hsA hsB hsC w then 0 else
          labelMass n A B C hsA hsB hsC w*(scaledOverhead n*
            (CostLedger.microPartitions n*CostLedger.allQueryTerms n+StageBounds.terminalChoices n)) := by
  let rs := EncodedColorWantedConsumerData.records n A B C hsA hsB hsC
  let D := ReportingHostWantedRecordData.catalogs A.length B.length C.length (bandSize n)
    (ThreeSumWantedHostData.config free n A B C hsA hsB hsC).report (half n) (blocks n) rs w output
  have hD : CatalogScales n D := physical_catalog_scales n
    (ThreeSumWantedHostData.config free n A B C hsA hsB hsC).report B.length C.length (bandSize n)
    (OutputDecodeOccurrenceCode.code (scheduleSize (half n)) (OutputDecodeRecords.layerCount (half n))
      (blocks n) output)
    (ownerRecord A.length (bandSize n) rs w.1.val).b (ownerRecord A.length (bandSize n) rs w.1.val).c
  have hh := actual_dispatch_step_le
    (cfg := ThreeSumWantedHostData.config free n A B C hsA hsB hsC) rfl rfl
    (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
    (ThreeSumReportingSetupData.shift n A B C hsA hsB hsC)
    (finiteAIndices A.length (bandSize n) rs (owner rs w))
    (finiteBandPositions B.length (bandSize n) (ownerRecord A.length (bandSize n) rs w.1.val).b)
    (finiteBandPositions C.length (bandSize n) (ownerRecord A.length (bandSize n) rs w.1.val).c)
    (fun i => valueAt A.length (bandSize n) rs (fun j => A.getD j 0) i.val)
    (fun i => B.getD i.val 0) (fun i => C.getD i.val 0)
    (left rs (fun j => B.getD j 0) w) (right rs (fun j => C.getD j 0) w)
    (finiteBandEquiv B.length (bandSize n) (ownerRecord A.length (bandSize n) rs w.1.val).b)
    (finiteBandEquiv C.length (bandSize n) (ownerRecord A.length (bandSize n) rs w.1.val).c)
    (fun _ => rfl) (fun _ => rfl) w D hD ⟨mem_owner rs w,hkey⟩
    (old := old) (threshold := threshold)
  exact hh

end ThreeSum.ThreeSumWantedHostCosts
