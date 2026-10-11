import Submission.ThreeSum.SourceFiniteInputs

/-! # Read source controls from the actually constructed local-cover header -/

namespace ThreeSum.EncodedColorCoverData

open Light GlobalEncoding LocalCoverBounds SourceFiniteInputs

theorem header_end (free h J : ℕ) : free+20 ≤ LightCoverKeyData.keyEnd free h J :=
  (LightLocalCoverRetention.base_le_nextFree (LightLocalCoverInit.base free) h).trans
    (LightCoverKeyData.afterCover_le_keyEnd free h J)

theorem source_controls {μ : ℕ → ℤ} {free h J : ℕ} (H : LightCoverKeyData.Stored μ free h J) :
    μ (free+6)=(localPrime h : ℤ) ∧ μ (free+7)=(localBucketCap h : ℤ) ∧
    μ (free+8)=(512*h : ℤ) ∧ μ (free+10)=(scheduleSize h : ℤ) ∧
    μ (free+12)=(maps free h : ℤ) ∧ μ (free+13)=(candidates free h : ℤ) ∧
    μ (free+14)=(leftCounts free h : ℤ) ∧ μ (free+15)=(rightCounts free h : ℤ) := by
  have h (i : ℕ) (hi : i < 20) := H.header.getD (i := i)
    (by simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
      LightLocalCoverMetadata.values] using hi) 0
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals
    first
    | simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
        LightLocalCoverMetadata.values,maps,candidates,leftCounts,rightCounts] using h 6 (by omega)
    | simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
        LightLocalCoverMetadata.values,maps,candidates,leftCounts,rightCounts] using h 7 (by omega)
    | simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
        LightLocalCoverMetadata.values,maps,candidates,leftCounts,rightCounts] using h 8 (by omega)
    | simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
        LightLocalCoverMetadata.values,maps,candidates,leftCounts,rightCounts] using h 10 (by omega)
    | simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
        LightLocalCoverMetadata.values,maps,candidates,leftCounts,rightCounts] using h 12 (by omega)
    | simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
        LightLocalCoverMetadata.values,maps,candidates,leftCounts,rightCounts] using h 13 (by omega)
    | simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
        LightLocalCoverMetadata.values,maps,candidates,leftCounts,rightCounts] using h 14 (by omega)
    | simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
        LightLocalCoverMetadata.values,maps,candidates,leftCounts,rightCounts] using h 15 (by omega)

end ThreeSum.EncodedColorCoverData
