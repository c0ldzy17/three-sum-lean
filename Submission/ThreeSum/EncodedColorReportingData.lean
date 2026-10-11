import Submission.ThreeSum.ThreeSumReportingSetupData
import Submission.ThreeSum.EncodedColorPipelineResources

/-!
# The original source header after shared reporting and dense initialization

The prelude returns the source header unchanged. The reporting header starts
eight cells later, and its field six contains the initialized dense counter.
All contracts retain the same normalized A, B and C witnesses.
-/

namespace ThreeSum.EncodedColorReportingData

open Light Scales BandScales EncodedColorNormalizedData ThreeSumReportingSetupData

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

local instance (n : ℕ) : NeZero (radix n) := ⟨Nat.ne_of_gt (radix_pos n)⟩

def Output (μ : ℕ → ℤ) (free n : ℕ) (color : Coloring.Parameter (inputBits n+1))
    (x : Fin n → ℤ) (r : ℤ) : Prop :=
  ∃ (A : List ℤ) (hsA : A.Pairwise (· < ·))
    (B : List ℤ) (hsB : B.Pairwise (· < ·))
    (C : List ℤ) (hsC : C.Pairwise (· < ·)),
    r=(EncodedColorPipelineData.finish free n A B C hsA hsB hsC : ℤ) ∧
      ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC

theorem Output.encoded {μ : ℕ → ℤ} {free n : ℕ} {color : Coloring.Parameter (inputBits n+1)}
    {x : Fin n → ℤ} {r : ℤ} (H : Output μ free n color x r) :
    EncodedColorPipelineData.Output μ free n color x r := by
  obtain ⟨A,hsA,B,hsB,C,hsC,hr,H⟩ := H
  exact ⟨A,hsA,B,hsB,C,hsC,hr,H.encoded⟩

theorem counter_read {μ : ℕ → ℤ} {free n : ℕ} {color : Coloring.Parameter (inputBits n+1)}
    {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC) :
    μ (EncodedColorPipelineData.finish free n A B C hsA hsB hsC+14)=
      (counter free n A B C hsA hsB hsC : ℤ) := by
  have hh := H.catalog.heads 6 (by simp [SharedReportingBankHeader.header])
  simpa [SharedReportingBankHeader.header,reportBase,counter,Nat.add_assoc] using hh

theorem report_le_source_allocation {μ : ℕ → ℤ} {free n : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hn : 0 < n) (U : ℕ) :
    reportBase free n A B C hsA hsB hsC ≤ free+(EncodedColorResources.need n U).cells := by
  obtain ⟨ha,hb,hc⟩ := ThreeSumColorBudgets.normalized_lengths H
  have hlen := EncodedColorNormalizedData.incidences_length_le
    (hsA := hsA) (hsB := hsB) (hsC := hsC) ha hb hc
  have hbase : EncodedColorPipelineData.controls free n A B C hsA hsB hsC ≤
      LightEncodedColorPipeline.sourceBound free n := EncodedColorStageCosts.base_le hlen
  have hfinish : EncodedColorPipelineData.finish free n A B C hsA hsB hsC ≤
      LightEncodedColorPipeline.finishBound free n := EncodedColorStageCosts.finish_le hn hbase hb hc
  have hs : LightEncodedColorPipeline.finishBound free n+8 ≤ LightEncodedColorPipeline.space free n U :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hall := (Nat.add_le_add_right hfinish 8).trans (hs.trans (EncodedColorResources.pipeline_space_bound free n U))
  simpa only [reportBase,EncodedColorResources.need,Nat.add_assoc] using hall

theorem kept {μ ν : ℕ → ℤ} {free n stop : ℕ} {color : Coloring.Parameter (inputBits n+1)}
    {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
    (K : Kept μ ν stop) (hstop : counter free n A B C hsA hsB hsC+4 ≤ stop) :
    ThreeSumReportingSetupData.Stored ν free n color x A B C hsA hsB hsC := by
  have hr := report_le_counter free n A B C hsA hsB hsC
  refine ⟨H.encoded.of_kept K (by change reportBase free n A B C hsA hsB hsC ≤ stop; omega),
    SharedReportingBankHeader.Stored.of_kept H.catalog K (by change counter free n A B C hsA hsB hsC ≤ stop; omega),?_⟩
  obtain ⟨h0,h1,h2,h3⟩ := H.dense
  exact ⟨(K _ (by omega)).trans h0,(K _ (by omega)).trans h1,
    (K _ (by omega)).trans h2,(K _ (by omega)).trans h3⟩

theorem Output.of_kept {μ ν : ℕ → ℤ} {free n stop : ℕ} {color : Coloring.Parameter (inputBits n+1)}
    {x : Fin n → ℤ} {r : ℤ} (H : Output μ free n color x r) (K : Kept μ ν stop)
    (hstop : (μ (r.toNat+14)).toNat+4 ≤ stop) : Output ν free n color x r := by
  obtain ⟨A,hsA,B,hsB,C,hsC,hr,H⟩ := H
  rw [hr,Int.toNat_natCast,counter_read H,Int.toNat_natCast] at hstop
  exact ⟨A,hsA,B,hsB,C,hsC,hr,kept H K hstop⟩

end ThreeSum.EncodedColorReportingData
