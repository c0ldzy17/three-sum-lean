import Submission.ThreeSum.EncodedColorWantedConsumerEnds

/-!
# Retain the selected-color inputs while the wanted counter changes

Only the first dense-header cell is mutable during the scan. The encoded
payload, shared reporting catalog, threshold, cap and original false score
remain available with exactly the same normalized-list witnesses.
-/

namespace ThreeSum.EncodedColorWantedConsumerData

open Light Scales BandScales ThreeSumWantedHostData

set_option maxHeartbeats 1800000
set_option maxRecDepth 14000

def DenseMetadata (μ : ℕ→ℤ) (counter cap score : ℕ) : Prop :=
  μ (counter+1)=((cap*score : ℕ) : ℤ) ∧
    μ (counter+2)=(cap : ℤ) ∧ μ (counter+3)=(score : ℤ)

variable {μ ν : ℕ→ℤ} {free n : ℕ}
  {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

theorem kept_counter
    (K : KeptBut μ ν (config free n A B C hsA hsB hsC).layoutHeader
      (config free n A B C hsA hsB hsC).counter 1) :
    Kept μ ν (config free n A B C hsA hsB hsC).counter := by
  intro a ha
  have he : (config free n A B C hsA hsB hsC).layoutHeader=
      (config free n A B C hsA hsB hsC).counter+4 := rfl
  exact K a ⟨by omega,Or.inl ha⟩

theorem retained_of_kept
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (HQ : ThreeSumReportingSetupData.Catalog μ free n A B C hsA hsB hsC)
    (K : Kept μ ν (config free n A B C hsA hsB hsC).counter) :
    EncodedColorPipelineData.Stored ν free n color x A B C hsA hsB hsC ∧
      ThreeSumReportingSetupData.Catalog ν free n A B C hsA hsB hsC := by
  have hbefore := ThreeSumReportingSetupData.report_le_counter free n A B C hsA hsB hsC
  have hsource : EncodedColorPipelineData.finish free n A B C hsA hsB hsC+8≤
      (config free n A B C hsA hsB hsC).counter := by
    change ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC≤
      ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC
    omega
  exact ⟨H.of_kept K hsource,SharedReportingBankHeader.Stored.of_kept HQ K le_rfl⟩

theorem retained_of_keptBut
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (HQ : ThreeSumReportingSetupData.Catalog μ free n A B C hsA hsB hsC)
    (K : KeptBut μ ν (config free n A B C hsA hsB hsC).layoutHeader
      (config free n A B C hsA hsB hsC).counter 1) :
    EncodedColorPipelineData.Stored ν free n color x A B C hsA hsB hsC ∧
      ThreeSumReportingSetupData.Catalog ν free n A B C hsA hsB hsC :=
  retained_of_kept H HQ (kept_counter K)

theorem metadata_reads_of_keptBut
    (K : KeptBut μ ν (config free n A B C hsA hsB hsC).layoutHeader
      (config free n A B C hsA hsB hsC).counter 1) :
    let ctr := (config free n A B C hsA hsB hsC).counter
    ν (ctr+1)=μ (ctr+1) ∧ ν (ctr+2)=μ (ctr+2) ∧ ν (ctr+3)=μ (ctr+3) := by
  have he : (config free n A B C hsA hsB hsC).layoutHeader=
      (config free n A B C hsA hsB hsC).counter+4 := rfl
  exact ⟨K _ ⟨by omega,Or.inr (by omega)⟩,
    K _ ⟨by omega,Or.inr (by omega)⟩,K _ ⟨by omega,Or.inr (by omega)⟩⟩

theorem DenseMetadata.of_keptBut {cap score : ℕ}
    (H : DenseMetadata μ (config free n A B C hsA hsB hsC).counter cap score)
    (K : KeptBut μ ν (config free n A B C hsA hsB hsC).layoutHeader
      (config free n A B C hsA hsB hsC).counter 1) :
    DenseMetadata ν (config free n A B C hsA hsB hsC).counter cap score := by
  obtain ⟨h1,h2,h3⟩ := metadata_reads_of_keptBut K
  exact ⟨h1.trans H.1,h2.trans H.2.1,h3.trans H.2.2⟩

theorem initial_dense_metadata
    (H : ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC) :
    DenseMetadata μ (config free n A B C hsA hsB hsC).counter
      (GlobalEncoding.representationCap (microHalf (inputBits n)) (blockCount (inputBits n)))
      (ThreeSumColorBudgets.falseScore n A B C hsA hsB hsC) := H.dense.2

end ThreeSum.EncodedColorWantedConsumerData
