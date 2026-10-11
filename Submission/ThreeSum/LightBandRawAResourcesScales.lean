import Submission.ThreeSum.LightBandRawAResources
import Submission.ThreeSum.SharedReportingBankResourceBoundsPolynomial
import Submission.ThreeSum.LightColorParametersCosts

/-! # Proved polynomial limits for original-input band and incidence preprocessing -/

namespace ThreeSum.LightBandRawAResources

open Light Scales BandScales StageBounds

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

def base (n : ℕ) : ℕ := (SharedReportingBankResourceBounds.magnitude n+1)*(n+1)^2
def envelope (n : ℕ) : ℕ := 1000*base n

def need (n U : ℕ) : Light.Need :=
  ⟨LightBandRawAColor.word (inputBits n+1) n (bandSize n) U,
    cells (inputBits n+1) n (bandSize n),
    LightBandRawAColor.depth (inputBits n+1) n (bandSize n)⟩

theorem factor_bounds (n : ℕ) :
    1 ≤ base n ∧ n+1 ≤ base n ∧ n^2 ≤ base n ∧
      SharedReportingBankResourceBounds.magnitude n ≤ base n ∧
      SharedReportingBankResourceBounds.magnitude n*n^2 ≤ base n := by
  have hq : 1 ≤ (n+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hbase : (n+1)^2 ≤ base n := Nat.le_mul_of_pos_left _ (by omega)
  have hn : n+1 ≤ (n+1)^2 := Nat.le_self_pow (by decide) _
  refine ⟨hq.trans hbase,hn.trans hbase,
    (Nat.pow_le_pow_left (Nat.le_succ _) 2).trans hbase,?_,?_⟩
  · exact (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ hq)
  · exact Nat.mul_le_mul (Nat.le_succ _) (Nat.pow_le_pow_left (Nat.le_succ _) 2)

theorem color_power_le (n : ℕ) : 2^((inputBits n+1)+1) ≤ 4*(n+1) := by
  have hp : 2^(inputBits n) ≤ n+1 := by
    simpa only [inputBits,Nat.log2_eq_log_two] using Nat.pow_log_le_add_one 2 n
  calc
    _ = 4*2^(inputBits n) := by
      rw [show inputBits n+1+1=inputBits n+2 by omega,pow_add]
      norm_num
      ring
    _ ≤ _ := Nat.mul_le_mul_left 4 hp

theorem word_bound (n U : ℕ) :
    LightBandRawAColor.word (inputBits n+1) n (bandSize n) U ≤ envelope n*(U+1) := by
  obtain ⟨h1,hn,hn2,hm,_⟩ := factor_bounds n
  have hg := (SharedReportingBankResourceBounds.band_le_magnitude n).trans hm
  have hp := (color_power_le n).trans (Nat.mul_le_mul_left 4 hn)
  have hh := word_le (inputBits n+1) n (bandSize n) U
  have hsum : LightBandRawAColor.word (inputBits n+1) n (bandSize n) U ≤ 138*base n+9*U := by omega
  have hb : base n ≤ base n*(U+1) := Nat.le_mul_of_pos_right _ (by omega)
  have hU : U ≤ base n*(U+1) := (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ h1)
  rw [show envelope n*(U+1)=1000*(base n*(U+1)) by unfold envelope; ring]
  omega

theorem cells_bound (n : ℕ) : cells (inputBits n+1) n (bandSize n) ≤ envelope n := by
  obtain ⟨h1,hn,hn2,_,hmn2⟩ := factor_bounds n
  have hcount := count_le n (bandSize n)
  have hcountBase := hcount.trans (Nat.mul_le_mul_left 3 hn2)
  have hwidth := width_le n (bandSize n)
  have hW : inputBits n+1 ≤ base n := (Nat.add_le_add_right (LightScales.inputBits_le_self n) 1).trans hn
  have hg := SharedReportingBankResourceBounds.band_le_magnitude n
  have hproduct : 3*bandSize n*ColorBandBounds.count n (bandSize n) ≤ 9*base n := by
    calc
      _ = 3*(bandSize n*ColorBandBounds.count n (bandSize n)) := by ring
      _ ≤ 3*(SharedReportingBankResourceBounds.magnitude n*(3*n^2)) :=
        Nat.mul_le_mul_left 3 (Nat.mul_le_mul hg hcount)
      _ = 9*(SharedReportingBankResourceBounds.magnitude n*n^2) := by ring
      _ ≤ _ := Nat.mul_le_mul_left 9 hmn2
  rw [cells_eq]
  unfold envelope
  apply max_le <;> omega

theorem depth_bound (n : ℕ) : LightBandRawAColor.depth (inputBits n+1) n (bandSize n) ≤ envelope n := by
  obtain ⟨h1,hn,_,_,_⟩ := factor_bounds n
  have hW : inputBits n+1 ≤ base n := (Nat.add_le_add_right (LightScales.inputBits_le_self n) 1).trans hn
  have hh := depth_le (inputBits n+1) n (bandSize n)
  unfold envelope
  omega

noncomputable section

theorem base_powerBound : PowerBound base 2050 := by
  have hm := SharedReportingBankResourceBounds.magnitude_powerBound.add_same
    ((PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ) ≤ 2048))
  have hn := ArithmeticStageBounds.identity_powerBound.add_same
    ((PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ) ≤ 1))
  have hh := hm.mul (hn.pow 2)
  convert hh using 1 <;> (first | rfl | norm_num [base])

theorem envelope_powerBound : PowerBound envelope 2050 := by
  change PowerBound (fun n => 1000*base n) 2050
  simpa only [zero_add] using (PowerBound.const 1000).mul base_powerBound

theorem poly_need : Light.PolyNeed need := by
  apply PolynomialResources.polyNeed_of_envelope envelope_powerBound 1
  · intro n U; simpa only [need,pow_one] using word_bound n U
  · intro n U
    simpa only [need,pow_one] using
      (cells_bound n).trans (Nat.le_mul_of_pos_right _ (by omega : 0 < U+1))
  · intro n U
    simpa only [need,pow_one] using
      (depth_bound n).trans (Nat.le_mul_of_pos_right _ (by omega : 0 < U+1))

end
end ThreeSum.LightBandRawAResources
