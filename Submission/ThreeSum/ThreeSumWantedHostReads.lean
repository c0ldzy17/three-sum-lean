import Submission.ThreeSum.LightThreeSumWantedHostDefs

/-! # Small independent header and numeric facts used by the concrete loader -/

namespace ThreeSum.LightThreeSumWantedHost

open Light Scales BandScales

set_option maxHeartbeats 1200000

theorem word_bounds (n : ℕ) :
    n≤word n ∧ blockCount (inputBits n)≤word n ∧ microHalf (inputBits n)≤word n ∧
    LightSwitchDepth.depth (blockCount (inputBits n))+1≤word n ∧ bandSize n≤word n ∧
    radix n≤word n ∧ OutputDecodeRecords.layerCount (microHalf (inputBits n))≤word n ∧
    GlobalEncoding.scheduleSize (microHalf (inputBits n))≤word n ∧
    ColorBandBounds.count n (bandSize n)≤word n ∧
    bandSize n*ColorBandBounds.count n (bandSize n)≤word n := by
  unfold word
  omega

theorem cover_header_reads {μ : ℕ→ℤ} {cover h J : ℕ}
    (H : LightCoverKeyData.Stored μ cover h J) :
    μ cover=(OutputDecodeRecords.layerCount h : ℤ) ∧
    μ (cover+10)=(GlobalEncoding.scheduleSize h : ℤ) ∧
    μ (cover+18)=(LightCoverKeys.afterCover cover h : ℤ) := by
  have Hread (i : ℕ) (hi : i<20) := H.header.getD (i := i)
    (by simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
      LightLocalCoverMetadata.values] using hi) 0
  refine ⟨?_,?_,?_⟩
  · simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
      OutputDecodeRecords.layerCount] using Hread 0 (by omega)
  · simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
      LightLocalCoverMetadata.values] using Hread 10 (by omega)
  · simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
      LightLocalCoverMetadata.values,LightCoverKeys.afterCover] using Hread 18 (by omega)

theorem report_level_read {μ : ℕ→ℤ} {report h J NB NC g : ℕ} {fB fC : ℕ→ℤ} {p shift : ℤ}
    (H : SharedReportingBankHeader.Stored μ report h J NB NC g fB fC p shift) :
    μ (report+2)=((LightSwitchDepth.depth J+1 : ℕ) : ℤ) := by
  simpa only [SharedReportingBankHeader.header,List.getD_cons_zero,List.getD_cons_succ,
    SharedReportingBankHeader.levels] using H.heads.read (i := 2)
      (by simp [SharedReportingBankHeader.header])

end ThreeSum.LightThreeSumWantedHost
