import Submission.ThreeSum.ReportingHostWantedConsumerData
import Submission.ThreeSum.SharedReportingBankResourceBoundsWantedMass
import Submission.ThreeSum.SharedReportingBankResourceBoundsWantedScan

/-! # Frozen physical order and the exact cost of the ascending consumer -/

namespace ThreeSum.ReportingHostWantedConsumerData

open Light Scales BandScales BandRawA RawReporting RawIncidences GlobalEncoding
open EncodedColorNormalizedData EncodedColorWantedConsumerData ThreeSumWantedHostData
open SharedReportingBankResourceBounds SharedTraversalCosts

set_option maxHeartbeats 2200000
set_option maxRecDepth 17000

def threshold (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  representationCap (half n) (blocks n)*ThreeSumColorBudgets.falseScore n A B C hsA hsB hsC

variable {μ ν : ℕ→ℤ} {free n : ℕ}
  {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

def mass (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) : ℕ→ℕ :=
  ReportingHostWantedPrefix.slotMass H.wanted (fun j => B.getD j 0) (fun j => C.getD j 0) B.length C.length

def hit (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) : ℕ→Prop :=
  ReportingHostWantedDecision.slotHit H.wanted (fun j => B.getD j 0) (fun j => C.getD j 0)
    B.length C.length (LightSwitchDepth.depth (blocks n))

def stepTime (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) (i : ℕ) : ℕ :=
  if hi : i<count n A B C hsA hsB hsC then
    LightReportingWantedDispatch.time (config free n A B C hsA hsB hsC) (wantedDecodeV n)
      (recordTime free n A B C hsA hsB hsC (label H ⟨i,hi⟩)
        (outputIndex μ (config free n A B C hsA hsB hsC) i)
        (prefixMass (mass H) i) (threshold n A B C hsA hsB hsC))
  else 0

def scanTime (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) : ℕ :=
  LightReportingWantedScan.time (stepTime H) (count n A B C hsA hsB hsC)

theorem mass_at (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (count n A B C hsA hsB hsC)) :
    mass H s.val=labelMass n A B C hsA hsB hsC (label H s) := by
  exact (ReportingHostWantedPrefix.slotMass_at H.wanted
    (fun j => B.getD j 0) (fun j => C.getD j 0) B.length C.length (slot H s)).trans
      (ReportingHostWantedOriginal.global_local_mass (records n A B C hsA hsB hsC)
        (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
        (ThreeSumReportingSetupData.shift n A B C hsA hsB hsC) (label H s))

theorem hit_at (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (count n A B C hsA hsB hsC)) :
    hit H s.val ↔ labelHit n A B C hsA hsB hsC (label H s) := by
  exact ReportingHostWantedDecision.slotHit_at H.wanted
    (fun j => B.getD j 0) (fun j => C.getD j 0) B.length C.length
    (LightSwitchDepth.depth (blocks n)) (slot H s)

theorem stepTime_at (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (count n A B C hsA hsB hsC)) :
    stepTime H s.val=
      LightReportingWantedDispatch.time (config free n A B C hsA hsB hsC) (wantedDecodeV n)
        (recordTime free n A B C hsA hsB hsC (label H s)
          (outputIndex μ (config free n A B C hsA hsB hsC) s.val)
          (prefixMass (mass H) s.val) (threshold n A B C hsA hsB hsC)) := by
  simp only [stepTime,dif_pos s.isLt]

theorem mass_le (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (i : ℕ) (hp : 0<EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
    (hg : 4*(EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)≤globalModulus (half n) (blocks n)) :
    mass H i≤3*(magnitude n)^7 := by
  have hN := incidence_length_le_magnitude H
  rw [incidence_length_eq] at hN
  exact wanted_physical_slot_mass_le H.wanted i hp hg hN
    (ThreeSumColorBudgets.normalized_lengths H).2.1 (ThreeSumColorBudgets.normalized_lengths H).2.2

theorem prefix_mass_le (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    {k : ℕ} (hk : k≤count n A B C hsA hsB hsC)
    (hp : 0<EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
    (hg : 4*(EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)≤globalModulus (half n) (blocks n)) :
    prefixMass (mass H) k≤3*(magnitude n)^7 := by
  have hN := incidence_length_le_magnitude H
  rw [incidence_length_eq] at hN
  exact wanted_physical_prefix_mass_le H.wanted k
    (by rw [count_read H,Int.toNat_natCast]; exact hk) hp hg hN
    (ThreeSumColorBudgets.normalized_lengths H).2.1 (ThreeSumColorBudgets.normalized_lengths H).2.2

theorem slot_reads_of_keptBut (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (count n A B C hsA hsB hsC))
    (K : KeptBut μ ν (config free n A B C hsA hsB hsC).layoutHeader
      (config free n A B C hsA hsB hsC).counter 1) :
    let cfg := config free n A B C hsA hsB hsC
    ν (cfg.pairs+2*s.val)=(rawIndex μ cfg s.val : ℤ) ∧
      ν (cfg.pairs+2*s.val+1)=(outputIndex μ cfg s.val : ℤ) := by
  let cfg := config free n A B C hsA hsB hsC
  have he : cfg.pairs+2*count n A B C hsA hsB hsC≤cfg.counter := (persistent_ends H).pairs
  have hk := kept_counter K
  have hs := s.isLt
  have hr := slot_reads H s
  exact ⟨(hk _ (by dsimp only [cfg] at *; omega)).trans hr.1,
    (hk _ (by dsimp only [cfg] at *; omega)).trans hr.2⟩

end ThreeSum.ReportingHostWantedConsumerData
