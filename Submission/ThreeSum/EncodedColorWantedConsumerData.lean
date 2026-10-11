import Submission.ThreeSum.ThreeSumWantedHostData
import Submission.ThreeSum.SharedReportingBankResourceBoundsPolynomial

/-!
# The actual retained inputs of the physical wanted consumer

These are projections and finite bounds for the same normalized witnesses
retained by the selected-color pipeline. Physical A incidences preserve
their owner labels even when their integer values are equal.
-/

namespace ThreeSum.EncodedColorWantedConsumerData

open Light Scales BandScales EncodedColorNormalizedData ThreeSumWantedHostData

set_option maxHeartbeats 2200000
set_option maxRecDepth 16000

abbrev records (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :=
  BandRawA.sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC

def positions (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  LightBandRawA.positionBase (config free n A B C hsA hsB hsC).vals
    (recordCount n A B C hsA hsB hsC) (bandSize n)

def occurrence (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  LightSourceBandHost.occurrenceBase (config free n A B C hsA hsB hsC).pair
    B.length C.length (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n))

variable {μ : ℕ→ℤ} {free n : ℕ}
  {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

theorem raw_stored (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    BandRawA.Stored μ (config free n A B C hsA hsB hsC).vals
      (config free n A B C hsA hsB hsC).owners (positions free n A B C hsA hsB hsC)
      (fun j => A.getD j 0) (BandRawA.items A.length (bandSize n) (records n A B C hsA hsB hsC)) :=
  H.normalized.2.2.2.2.2.2

theorem records_stored (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    Seg μ (config free n A B C hsA hsB hsC).records (BandCandidateRows.cells (records n A B C hsA hsB hsC)) :=
  H.normalized.2.2.2.2.2.1

theorem normalized_read (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    (∀ j<A.length, μ (EncodedColorLayout.av free n+j)=A.getD j 0) ∧
      (∀ j<(config free n A B C hsA hsB hsC).NB,
        μ ((config free n A B C hsA hsB hsC).srcB+j)=B.getD j 0) ∧
      (∀ j<(config free n A B C hsA hsB hsC).NC,
        μ ((config free n A B C hsA hsB hsC).srcC+j)=C.getD j 0) :=
  ⟨SourceFiniteInputs.prepared_read H.normalized.2.1,
    SourceFiniteInputs.prepared_read H.normalized.2.2.1,
    SourceFiniteInputs.prepared_read H.normalized.2.2.2.1⟩

theorem normalized_bound {U : ℕ}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hx : ∀ i, |x i|≤(U : ℤ)) :
    (∀ j<A.length, |A.getD j 0|≤(U : ℤ)) ∧
      (∀ j<(config free n A B C hsA hsB hsC).NB, |B.getD j 0|≤(U : ℤ)) ∧
      (∀ j<(config free n A B C hsA hsB hsC).NC, |C.getD j 0|≤(U : ℤ)) :=
  ThreeSumColorBudgets.normalized_values H hx

theorem incidence_length_eq (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    (config free n A B C hsA hsB hsC).N=
      (BandRawA.items A.length (bandSize n) (records n A B C hsA hsB hsC)).length :=
  BandRawA.values_length ..

theorem incidence_length_le_records (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    (config free n A B C hsA hsB hsC).N≤bandSize n*recordCount n A B C hsA hsB hsC := by
  rw [incidence_length_eq]
  exact BandRawA.items_length_le ..

theorem record_count_le (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    recordCount n A B C hsA hsB hsC≤ColorBandBounds.count n (bandSize n) := by
  obtain ⟨ha,hb,hc⟩ := ThreeSumColorBudgets.normalized_lengths H
  exact EncodedColorNormalizedData.records_length_le ha hb hc

theorem size_le_magnitude (n : ℕ) : n≤SharedReportingBankResourceBounds.magnitude n := by
  have hp : n≤2^(inputBits n+1) := by
    simpa [inputBits,Nat.log2_eq_log_two,Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by decide : 1<2) n).le
  exact hp.trans (Nat.pow_le_pow_right (by decide) (by omega))

theorem incidence_length_le_magnitude
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    (config free n A B C hsA hsB hsC).N≤3*(SharedReportingBankResourceBounds.magnitude n)^3 := by
  have hr := record_count_le H
  have hc : ColorBandBounds.count n (bandSize n)≤3*n^2 :=
    Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (BandPartition.size_le n (bandSize n)) 2)
  have hg := SharedReportingBankResourceBounds.band_le_magnitude n
  have hn := size_le_magnitude n
  calc
    _ ≤ bandSize n*recordCount n A B C hsA hsB hsC := incidence_length_le_records ..
    _ ≤ SharedReportingBankResourceBounds.magnitude n*(3*n^2) := Nat.mul_le_mul hg (hr.trans hc)
    _ ≤ SharedReportingBankResourceBounds.magnitude n*(3*(SharedReportingBankResourceBounds.magnitude n)^2) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hn 2))
    _ = _ := by ring

theorem count_le_product (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    ThreeSumWantedHostData.count n A B C hsA hsB hsC≤3*(config free n A B C hsA hsB hsC).N*
      LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n)) := by
  have hh := H.countBound
  rw [ThreeSumWantedHostData.count_read H,Int.toNat_natCast] at hh
  exact (Nat.le_mul_of_pos_left _ (radix_pos n)).trans hh

theorem incidence_value_bound {U i : ℕ}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hx : ∀ j, |x j|≤(U : ℤ)) (hi : i<(config free n A B C hsA hsB hsC).N) :
    |A.getD (BandRawA.labelAt A.length (bandSize n) (records n A B C hsA hsB hsC) i).position 0|≤(U : ℤ) := by
  rw [incidence_length_eq] at hi
  exact (normalized_bound H hx).1 _ (BandRawA.position_lt (BandRawA.at_mem hi))

theorem owner_bands {i : ℕ} (hi : i<(config free n A B C hsA hsB hsC).N) :
    (BandRawA.ownerRecord A.length (bandSize n) (records n A B C hsA hsB hsC) i).a<
      BandPartition.size A.length (bandSize n) ∧
    (BandRawA.ownerRecord A.length (bandSize n) (records n A B C hsA hsB hsC) i).b<
      BandPartition.size (config free n A B C hsA hsB hsC).NB (bandSize n) ∧
    (BandRawA.ownerRecord A.length (bandSize n) (records n A B C hsA hsB hsC) i).c<
      BandPartition.size (config free n A B C hsA hsB hsC).NC (bandSize n) := by
  rw [incidence_length_eq] at hi
  have hb := BandRawA.at_bounds hi
  have hs := BandCandidateRows.getD_sound hb.1 hb.2.1
  exact ⟨hs.1,hs.2.1,hs.2.2.1⟩

end ThreeSum.EncodedColorWantedConsumerData
