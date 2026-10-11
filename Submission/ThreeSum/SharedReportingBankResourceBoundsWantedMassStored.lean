import Submission.ThreeSum.SharedReportingBankResourceBoundsWantedMass
import Submission.ThreeSum.EncodedColorWantedConsumerData

/-! # Physical mass limits from the retained selected color

The positive common modulus, its guard, every physical incidence count,
and both original sorted-source lengths come from the executed pipeline.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light Scales BandScales BandRawA RawReporting GlobalEncoding
open ReportingHostFrontierLayout ReportingHostWantedOriginal
open EncodedColorNormalizedData EncodedColorWantedConsumerData

set_option maxHeartbeats 1800000
set_option maxRecDepth 16000

variable {μ : ℕ→ℤ} {free n : ℕ}
  {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

theorem wanted_stored_mass_dimensions
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    (items A.length (bandSize n) (records n A B C hsA hsB hsC)).length≤3*(magnitude n)^3 ∧
      B.length≤n ∧ C.length≤n := by
  have hh := incidence_length_le_magnitude H
  change (values (fun j => A.getD j 0)
    (items A.length (bandSize n) (records n A B C hsA hsB hsC))).length≤3*(magnitude n)^3 at hh
  rw [values_length] at hh
  exact ⟨hh,(ThreeSumColorBudgets.normalized_lengths H).2⟩

theorem wanted_selected_guard (hR : 4≤radix n) :
    4*(EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)≤globalModulus (half n) (blocks n) := by
  have hh : 4*(EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)≤(radix n : ℤ) := by
    exact_mod_cast EncodedColorPrimeReadyData.selected_guard (A := A) (B := B) (C := C)
      (hsA := hsA) (hsB := hsB) (hsC := hsC) hR
  simpa only [globalModulus,Scales.radix,Scales.localRadix,half,blocks,Nat.cast_pow] using hh

theorem wanted_stored_global_card_le
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hR : 4≤radix n) :
    (globalItems (half n) (blocks n) A.length B.length C.length (bandSize n)
      (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (records n A B C hsA hsB hsC)
      (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
      (ThreeSumReportingSetupData.shift n A B C hsA hsB hsC)).card≤3*(magnitude n)^7 := by
  obtain ⟨hi,hb,hc⟩ := wanted_stored_mass_dimensions H
  exact wanted_global_card_le _ _ _ _ _ EncodedColorPrimeReadyData.selected_pos
    (wanted_selected_guard hR) hi hb hc

theorem wanted_stored_local_card_le
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hR : 4≤radix n)
    (w : Wanted (half n) (blocks n) (AType A.length (bandSize n) (records n A B C hsA hsB hsC))) :
    (localItems (half n) (blocks n) A.length B.length C.length (bandSize n)
      (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (records n A B C hsA hsB hsC)
      (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
      (ThreeSumReportingSetupData.shift n A B C hsA hsB hsC) w).card≤3*(magnitude n)^7 := by
  obtain ⟨hi,hb,hc⟩ := wanted_stored_mass_dimensions H
  exact wanted_local_card_le _ _ _ _ _ w EncodedColorPrimeReadyData.selected_pos
    (wanted_selected_guard hR) hi hb hc

theorem wanted_stored_local_root_le
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hR : 4≤radix n)
    (w : Wanted (half n) (blocks n) (AType A.length (bandSize n) (records n A B C hsA hsB hsC))) :
    rootMass (localItems (half n) (blocks n) A.length B.length C.length (bandSize n)
      (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (records n A B C hsA hsB hsC)
      (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
      (ThreeSumReportingSetupData.shift n A B C hsA hsB hsC) w) w≤3*(magnitude n)^7 := by
  obtain ⟨hi,hb,hc⟩ := wanted_stored_mass_dimensions H
  exact wanted_local_root_le _ _ _ _ _ w EncodedColorPrimeReadyData.selected_pos
    (wanted_selected_guard hR) hi hb hc

theorem wanted_stored_threshold_le
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    representationCap (half n) (blocks n)*ThreeSumColorBudgets.falseScore n A B C hsA hsB hsC≤
      9*(magnitude n)^8 := by
  have hrs : (records n A B C hsA hsB hsC).length≤3*n^2 :=
    (record_count_le H).trans
      (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (BandPartition.size_le n (bandSize n)) 2))
  exact wanted_threshold_le (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
    (records n A B C hsA hsB hsC) hrs

theorem wanted_stored_slot_mass_le
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hR : 4≤radix n) (i : ℕ) :
    ReportingHostWantedPrefix.slotMass H.wanted (fun j => B.getD j 0) (fun j => C.getD j 0)
      B.length C.length i≤3*(magnitude n)^7 := by
  obtain ⟨hi,hb,hc⟩ := wanted_stored_mass_dimensions H
  exact wanted_physical_slot_mass_le H.wanted i EncodedColorPrimeReadyData.selected_pos
    (wanted_selected_guard hR) hi hb hc

theorem wanted_stored_prefix_mass_le
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hR : 4≤radix n) (k : ℕ) (hk : k≤ThreeSumWantedHostData.count n A B C hsA hsB hsC) :
    SharedTraversalCosts.prefixMass (ReportingHostWantedPrefix.slotMass H.wanted
      (fun j => B.getD j 0) (fun j => C.getD j 0) B.length C.length) k≤3*(magnitude n)^7 := by
  have hk' : k≤(μ (EncodedColorPipelineData.wantedHeader free n (incidences n A B C hsA hsB hsC).length)).toNat := by
    rw [ThreeSumWantedHostData.count_read H,Int.toNat_natCast]
    exact hk
  obtain ⟨hi,hb,hc⟩ := wanted_stored_mass_dimensions H
  exact wanted_physical_prefix_mass_le H.wanted k hk' EncodedColorPrimeReadyData.selected_pos
    (wanted_selected_guard hR) hi hb hc

end ThreeSum.SharedReportingBankResourceBounds
