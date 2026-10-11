import Submission.ThreeSum.SharedReportingBankResourceBoundsScales

/-!
# Polynomial limits for the actual shared reporting host

The finite word, cell, and depth formulas are bounded at every input size.
The resulting `Need` includes the complete executed host, while its time
bound remains the exact shared-box budget proved separately.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Scales StageBounds Filter Light
open scoped Topology

set_option maxHeartbeats 1200000
set_option maxRecDepth 14000

noncomputable section

theorem bits_power_powerBound : PowerBound (fun n => 2^(inputBits n)) 1 := by
  apply ArithmeticStageBounds.powerBound_mono ArithmeticStageBounds.identity_powerBound
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  simpa only [inputBits,Nat.log2_eq_log_two] using
    Nat.pow_log_le_self 2 (by omega : n ≠ 0)

theorem magnitude_powerBound : PowerBound magnitude 2048 := by
  have hh := (PowerBound.const (2^2048)).mul (bits_power_powerBound.pow 2048)
  have he : magnitude = fun n => 2^2048*(2^(inputBits n))^2048 := by
    funext n
    unfold magnitude
    rw [show 2048*(inputBits n+1)=2048+inputBits n*2048 by omega,pow_add,pow_mul]
  rw [he]
  simpa only [Nat.cast_ofNat,mul_one,zero_add] using hh

theorem polynomial_part_powerBound : PowerBound polynomialPart 10242 := by
  have hm := magnitude_powerBound.add_same
    ((PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ) ≤ 2048))
  have hn := ArithmeticStageBounds.identity_powerBound.add_same
    ((PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ) ≤ 1))
  have hh := ((PowerBound.const 5000).mul (hm.pow 5)).mul (hn.pow 2)
  convert hh using 1 <;> (first | rfl | norm_num [polynomialPart])

theorem envelope_powerBound : PowerBound envelope 131072 := by
  have hp := polynomial_part_powerBound.mono_exponent
    (by norm_num : (10242 : ℝ) ≤ 131072)
  have hm : PowerBound (fun n => (magnitude n)^64) 131072 := by
    convert magnitude_powerBound.pow 64 using 1 <;> norm_num
  exact hp.add_same hm

theorem scaled_extent_le_envelope (n : ℕ) : scaledExtent n ≤ envelope n :=
  (scaled_extent_le n).trans (Nat.le_add_right _ _)

theorem scaled_depth_le_envelope (n : ℕ) : scaledDepth n ≤ envelope n :=
  (scaled_depth_le n).trans (Nat.le_add_right _ _)

theorem resource_polynomials : ∃ s k : ℕ, ∀ n : ℕ,
    scaledWord n ≤ Light.polyBound s k [n] ∧
    scaledExtent n ≤ Light.polyBound s k [n] ∧
    scaledDepth n ≤ Light.polyBound s k [n] := by
  obtain ⟨s,k,h⟩ := PolynomialResources.polyBound_of_powerBound envelope_powerBound
  exact ⟨s,k,fun n => ⟨(scaled_word_le n).trans (h n),
    (scaled_extent_le_envelope n).trans (h n),
    (scaled_depth_le_envelope n).trans (h n)⟩⟩

def need (n _U : ℕ) : Light.Need := ⟨scaledWord n,scaledExtent n,scaledDepth n⟩

theorem poly_need : Light.PolyNeed need := by
  apply PolynomialResources.polyNeed_of_envelope envelope_powerBound 0
  · intro n U; simpa only [need,pow_zero,mul_one] using scaled_word_le n
  · intro n U; simpa only [need,pow_zero,mul_one] using scaled_extent_le_envelope n
  · intro n U; simpa only [need,pow_zero,mul_one] using scaled_depth_le_envelope n

theorem resources_of_ok {lim : Light.Limits} {n U free NB NC d : ℕ}
    (hB : NB ≤ n) (hC : NC ≤ n) (hok : (need n U).Ok lim free d) :
    LightSharedReportingHost.Resources lim free (half n) (blocks n)
      NB NC (BandScales.bandSize n) d :=
  resources hB hC hok.cells hok.word hok.depth

end
end ThreeSum.SharedReportingBankResourceBounds
