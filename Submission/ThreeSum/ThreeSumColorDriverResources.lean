import Submission.ThreeSum.LightThreeSumColorDriver
import Submission.ThreeSum.ThreeSumParameterResources

/-!
# Affine resources for a color scan and its single parameter initialization

Per-color storage is reused after one six-cell color row. The full driver
uses nineteen persistent parameter cells and reclaims the initializer's
scratch before the scan. Both allocations have coefficient one on free.
-/

namespace ThreeSum.ThreeSumColorDriverResources

open Light Scales StageBounds ArithmeticStageBounds LightColorParametersCosts ColorParameters

set_option maxHeartbeats 2000000
set_option maxRecDepth 14000

def overhead (n _U : ℕ) : Need :=
  ⟨LightColorScanHost.word n,6,count (width n)+4⟩

def need (colorNeed : ℕ→ℕ→Need) (n U : ℕ) : Need :=
  ⟨(colorNeed n U).word+(overhead n U).word,
    (colorNeed n U).cells+(overhead n U).cells,
    (colorNeed n U).depth+(overhead n U).depth⟩

def fullNeed (colorNeed : ℕ→ℕ→Need) (n U : ℕ) : Need :=
  ⟨(ThreeSumParameterResources.need n U).word+(need colorNeed n U).word,
    max (ThreeSumParameterResources.need n U).cells (19+(need colorNeed n U).cells),
    (ThreeSumParameterResources.need n U).depth+(need colorNeed n U).depth+2⟩

theorem scan_bounds_of_ok {lim : Limits} {colorNeed : ℕ→ℕ→Need} {n U row d : ℕ}
    (H : (need colorNeed n U).Ok lim row d) :
    row+6≤lim.space ∧ (LightColorScanHost.word n : ℤ)≤lim.word ∧
      d+count (width n)+(colorNeed n U).depth+4≤lim.depth := by
  have hs := H.cells
  have hd := H.depth
  dsimp only [need,overhead] at hs hd
  refine ⟨by omega,?_,by omega⟩
  exact (Int.ofNat_le.mpr (by dsimp only [need,overhead]; omega)).trans H.word

theorem color_of_ok {lim : Limits} {colorNeed : ℕ→ℕ→Need} {n U row d dd : ℕ}
    (H : (need colorNeed n U).Ok lim row d)
    (hd : dd+(colorNeed n U).depth≤lim.depth) :
    (colorNeed n U).Ok lim (row+6) dd := by
  have hs := H.cells
  dsimp only [need,overhead] at hs
  exact ⟨(Int.ofNat_le.mpr (by dsimp only [need,overhead]; omega)).trans H.word,
    by omega,H.space,hd⟩

theorem parameters_of_full_ok {lim : Limits} {colorNeed : ℕ→ℕ→Need} {n U free d : ℕ}
    (H : (fullNeed colorNeed n U).Ok lim free d) :
    (ThreeSumParameterResources.need n U).Ok lim free (d+1) :=
  H.mono (by dsimp only [fullNeed]; omega) (by dsimp only [fullNeed]; omega)
    (by dsimp only [fullNeed]; omega)

theorem scan_of_full_ok {lim : Limits} {colorNeed : ℕ→ℕ→Need} {n U free d : ℕ}
    (H : (fullNeed colorNeed n U).Ok lim free d) :
    (need colorNeed n U).Ok lim (free+19) (d+1) :=
  H.mono (by dsimp only [fullNeed]; omega) (by dsimp only [fullNeed]; omega)
    (by dsimp only [fullNeed]; omega)

theorem allocation_eq (colorNeed : ℕ→ℕ→Need) (n U : ℕ) :
    (fullNeed colorNeed n U).cells=
      max (ThreeSumParameterResources.need n U).cells (25+(colorNeed n U).cells) := by
  dsimp only [fullNeed,need,overhead]
  congr 1
  omega

def overheadEnvelope (n : ℕ) : ℕ := 200*(n+1)^2

theorem overhead_bounds (n U : ℕ) :
    (overhead n U).word≤overheadEnvelope n ∧ (overhead n U).cells≤overheadEnvelope n ∧
      (overhead n U).depth≤overheadEnvelope n := by
  have hW : width n≤n+1 := Nat.add_le_add_right (LightScales.inputBits_le_self n) 1
  have hC : count (width n)≤81*(n+1)^2 := Nat.mul_le_mul_left 81 (Nat.pow_le_pow_left hW 2)
  have hpow : n+1≤(n+1)^2 := Nat.le_self_pow (by decide) _
  have hpos : 1≤(n+1)^2 := Nat.one_le_pow _ _ (by omega)
  dsimp only [overhead,overheadEnvelope,LightColorScanHost.word]
  omega

noncomputable section

theorem overheadEnvelope_powerBound : PowerBound overheadEnvelope 2 := by
  have hN : PowerBound (fun n : ℕ => n+1) 1 :=
    identity_powerBound.add_same ((PowerBound.const 1).mono_exponent (by norm_num))
  have hp : PowerBound (fun n : ℕ => (n+1)^2) 2 := by
    convert hN.pow 2 using 1
    norm_num
  change PowerBound (fun n : ℕ => 200*(n+1)^2) 2
  simpa only [zero_add] using (PowerBound.const 200).mul hp

theorem overhead_poly_need : PolyNeed overhead := by
  apply PolynomialResources.polyNeed_of_envelope overheadEnvelope_powerBound 0
  · intro n U; simpa only [pow_zero,mul_one] using (overhead_bounds n U).1
  · intro n U; simpa only [pow_zero,mul_one] using (overhead_bounds n U).2.1
  · intro n U; simpa only [pow_zero,mul_one] using (overhead_bounds n U).2.2

theorem poly_need {colorNeed : ℕ→ℕ→Need} (H : PolyNeed colorNeed) : PolyNeed (need colorNeed) := by
  obtain ⟨sa,ka,ha⟩ := H
  obtain ⟨sb,kb,hb⟩ := overhead_poly_need
  refine ⟨sa+sb+1,ka+kb,fun n U => ?_⟩
  let F := Light.polyBound (sa+sb) (ka+kb) [n,U]
  have hA := ha n U
  have hB := hb n U
  have hma : Light.polyBound sa ka [n,U]≤F := Light.polyBound_mono (by omega) (by omega) _
  have hmb : Light.polyBound sb kb [n,U]≤F := Light.polyBound_mono (by omega) (by omega) _
  have he : Light.polyBound (sa+sb+1) (ka+kb) [n,U]=2*F := by
    unfold F Light.polyBound
    rw [pow_add]
    norm_num
    ring
  rw [he]
  dsimp only [need]
  exact ⟨by omega,by omega,by omega⟩

theorem full_poly_need {colorNeed : ℕ→ℕ→Need} (H : PolyNeed colorNeed) : PolyNeed (fullNeed colorNeed) := by
  obtain ⟨sa,ka,ha⟩ := ThreeSumParameterResources.poly_need
  obtain ⟨sb,kb,hb⟩ := poly_need H
  refine ⟨sa+sb+5,ka+kb,fun n U => ?_⟩
  let F := Light.polyBound (sa+sb) (ka+kb) [n,U]
  have hA := ha n U
  have hB := hb n U
  have hma : Light.polyBound sa ka [n,U]≤F := Light.polyBound_mono (by omega) (by omega) _
  have hmb : Light.polyBound sb kb [n,U]≤F := Light.polyBound_mono (by omega) (by omega) _
  have hF : 1≤F := by
    unfold F Light.polyBound
    simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    exact Nat.mul_pos (by positivity) (by positivity)
  have he : Light.polyBound (sa+sb+5) (ka+kb) [n,U]=32*F := by
    unfold F Light.polyBound
    rw [pow_add]
    norm_num
    ring
  rw [he]
  dsimp only [fullNeed]
  exact ⟨by omega,by omega,by omega⟩

end
end ThreeSum.ThreeSumColorDriverResources
