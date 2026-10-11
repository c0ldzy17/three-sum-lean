import Submission.ThreeSum.SharedReportingBankResourceBoundsDense

/-! # Polynomial limits for the exact dense initialization resources -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light Scales StageBounds ArithmeticStageBounds

set_option maxHeartbeats 1600000
set_option maxRecDepth 14000

def denseEnvelope (n : ℕ) : ℕ := 20000*(EncodedColorResources.scale n)^8

/-- Exact word, relative cell extent, and depth of the physical dense setup. -/
def denseNeed (n U : ℕ) : Light.Need := ⟨denseWord n U,denseCells n U,denseDepth n⟩

theorem dense_envelope_factors (n U : ℕ) :
    1 ≤ (EncodedColorResources.scale n)^8 ∧
    EncodedColorResources.scale n ≤ (EncodedColorResources.scale n)^8 ∧
    (EncodedColorResources.scale n)^8 ≤ (EncodedColorResources.scale n)^8*(U+1) ∧
    U ≤ (EncodedColorResources.scale n)^8*(U+1) := by
  have hS : 1 ≤ EncodedColorResources.scale n := by
    have hh := (EncodedColorResources.scale_bounds n).1
    omega
  have h1 : 1 ≤ (EncodedColorResources.scale n)^8 := Nat.one_le_pow _ _ hS
  exact ⟨h1,Nat.le_self_pow (by decide) _,Nat.le_mul_of_pos_right _ (by omega),
    (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ h1)⟩

theorem dense_word_bound (n U : ℕ) : denseWord n U ≤ denseEnvelope n*(U+1) := by
  obtain ⟨h1,_,hb,hU⟩ := dense_envelope_factors n U
  have hh := dense_word_le n U
  rw [show denseEnvelope n*(U+1)=20000*((EncodedColorResources.scale n)^8*(U+1)) by
    unfold denseEnvelope; ring]
  omega

theorem dense_cells_bound (n U : ℕ) : denseCells n U ≤ denseEnvelope n*(U+1) := by
  obtain ⟨h1,hS,hb,hU⟩ := dense_envelope_factors n U
  have hh := dense_cells_le n U
  rw [show denseEnvelope n*(U+1)=20000*((EncodedColorResources.scale n)^8*(U+1)) by
    unfold denseEnvelope; ring]
  omega

theorem dense_depth_bound (n : ℕ) : denseDepth n ≤ denseEnvelope n := by
  obtain ⟨h1,hS,_,_⟩ := dense_envelope_factors n 0
  have hh := dense_depth_le n
  unfold denseEnvelope
  omega

noncomputable section

theorem dense_envelope_powerBound : PowerBound denseEnvelope 16384 := by
  have hh := (PowerBound.const 20000).mul (EncodedColorResources.scale_powerBound.pow 8)
  convert hh using 1 <;> (first | rfl | norm_num [denseEnvelope])

theorem dense_poly_need : Light.PolyNeed denseNeed := by
  apply PolynomialResources.polyNeed_of_envelope dense_envelope_powerBound 1
  · intro n U; simpa only [denseNeed,pow_one] using dense_word_bound n U
  · intro n U; simpa only [denseNeed,pow_one] using dense_cells_bound n U
  · intro n U
    simpa only [denseNeed,pow_one] using
      (dense_depth_bound n).trans (Nat.le_mul_of_pos_right _ (by omega : 0<U+1))

end

theorem dense_resources_of_ok {lim : Limits} {dst n U d : ℕ}
    (hok : (denseNeed n U).Ok lim dst d) :
    LightWeightedScore.space (dst+4) (maxMod n) (BandScales.bandSize n) U ≤ lim.space ∧
    (denseWord n U : ℤ) ≤ lim.word ∧ d+Nat.clog 2 (maxMod n)+8 ≤ lim.depth := by
  refine ⟨?_,hok.word,?_⟩
  · rw [dense_space_eq]
    exact hok.cells
  · simpa only [denseNeed,denseDepth,Nat.add_assoc] using hok.depth

theorem dense_header_end_of_ok {lim : Limits} {dst n U d : ℕ}
    (hok : (denseNeed n U).Ok lim dst d) : dst+4 ≤ lim.space := by
  have hh := hok.cells
  change dst+denseCells n U ≤ lim.space at hh
  unfold denseCells at hh
  omega

end ThreeSum.SharedReportingBankResourceBounds
