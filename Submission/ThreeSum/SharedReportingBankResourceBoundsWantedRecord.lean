import Submission.ThreeSum.SharedReportingBankResourceBoundsWantedRecordValues
import Submission.ThreeSum.LightReportingWantedRecordCall

/-! # Relative resources for the actual packed wanted-record call -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light GlobalEncoding LocalCoverBounds ReportingHostWantedLayout
open ReportingHostWantedControls

set_option maxHeartbeats 2100000
set_option maxRecDepth 16000

theorem wanted_record_space_of_ok {lim : Limits} {dst cover counter n U K N NB NC d : ℕ}
    (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hcover : cover+8≤dst) (hcounter : counter+2≤dst)
    (hok : (wantedNeed n U).Ok lim dst d) :
    LightReportingWantedRecordCall.space (access dst (blocks n)) dst cover counter
      (half n) (blocks n) K≤lim.space := by
  have H := wanted_buffers_of_ok hK hN hB hC hok
  have ha := wanted_access_output_le hK hN hB hC hok
  have hw := H.numeric
  have he := wanted_work_eq dst (half n) (blocks n) K N NB NC
  have hf := wanted_work_formula (half n) (blocks n) K N NB NC
  have hcell := hok.cells
  change dst+wantedEnvelope n≤lim.space at hcell
  have hn : LightReportingWantedRecordCall.numericExtra (half n) (blocks n) K≤lim.space :=
    (wanted_record_scalars_le hK).trans (by omega)
  unfold LightReportingWantedRecordCall.space
  apply max_le
  · exact max_le ha (by omega)
  · exact max_le (max_le (by omega) (by omega)) hn

theorem wanted_record_meets {lim : Limits} {μ : ℕ→ℤ} {S : Selection}
    {dst cover counter n U K N NB NC d T : ℕ} {Q : ℤ→(ℕ→ℤ)→Prop}
    (H : Seg μ (access dst (blocks n)) (ReportingHostWantedControls.record S))
    (HL : SegN μ dst (values (LightReportingWantedLayout.layout dst (half n) (blocks n) K N NB NC)))
    (hprime : μ (cover+6)=(localPrime (half n) : ℤ))
    (hcap : μ (cover+7)=(localBucketCap (half n) : ℤ))
    (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hcover : cover+8≤dst) (hcounter : counter+2≤dst)
    (hok : (wantedNeed n U).Ok lim dst d)
    (hselected : ∀ z∈ReportingHostWantedControls.record S, |z|≤lim.word)
    (hreport : Meets lim LightReportingWanted.program 137 (d+1)
      (arguments S (LightReportingWantedLayout.layout dst (half n) (blocks n) K N NB NC)
        dst cover counter (half n) (blocks n) K) μ T Q) :
    Meets lim LightReportingWantedRecordCall.program 138 d
      [access dst (blocks n),dst,half n,blocks n,K,
        BlockSourceEncoding.modulus (half n) (blocks n),cover,counter] μ (T+4000) Q := by
  have hd := hok.depth
  change d+wantedEnvelope n≤lim.depth at hd
  have hp := wanted_envelope_positive n
  exact LightReportingWantedRecordCall.program_meets H HL hprime hcap hok.space (by omega)
    (wanted_record_space_of_ok hK hN hB hC hcover hcounter hok) hselected
    (wanted_buffers_of_ok hK hN hB hC hok).values hreport

end ThreeSum.SharedReportingBankResourceBounds
