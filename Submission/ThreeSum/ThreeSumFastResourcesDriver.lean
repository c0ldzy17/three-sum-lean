import Submission.ThreeSum.ThreeSumFastResourcesConfig
import Submission.ThreeSum.ThreeSumColorDriverResources

/-! # Concrete resources for the complete537-procedure fast driver

The nineteen parameter cells and six reusable color-row cells precede the
selected-color allocation. Parameter-initialization scratch is reclaimed.
The original free address has coefficient one in every memory premise.
-/

namespace ThreeSum.ThreeSumFastResourcesDriver

open Light Scales

set_option maxHeartbeats 1700000
set_option maxRecDepth 15000

def need : ℕ→ℕ→Light.Need :=
  ThreeSumColorDriverResources.fullNeed ThreeSumFastResourcesColor.need

theorem cells_eq (n U : ℕ) :
    (need n U).cells=max (ThreeSumParameterResources.need n U).cells
      (25+(ThreeSumFastResourcesColor.need n U).cells) :=
  ThreeSumColorDriverResources.allocation_eq _ n U

theorem word_eq (n U : ℕ) :
    (need n U).word=(ThreeSumParameterResources.need n U).word+
      (ThreeSumFastResourcesColor.need n U).word+LightColorScanHost.word n := by
  dsimp only [need,ThreeSumColorDriverResources.fullNeed,ThreeSumColorDriverResources.need,
    ThreeSumColorDriverResources.overhead]
  omega

theorem depth_eq (n U : ℕ) :
    (need n U).depth=(ThreeSumParameterResources.need n U).depth+
      (ThreeSumFastResourcesColor.need n U).depth+
      ColorParameters.count (LightColorParametersCosts.width n)+6 := by
  dsimp only [need,ThreeSumColorDriverResources.fullNeed,ThreeSumColorDriverResources.need,
    ThreeSumColorDriverResources.overhead]
  omega

theorem parameters_of_ok {lim : Limits} {n U free d : ℕ}
    (H : (need n U).Ok lim free d) :
    (ThreeSumParameterResources.need n U).Ok lim free (d+1) :=
  ThreeSumColorDriverResources.parameters_of_full_ok H

theorem scan_of_ok {lim : Limits} {n U free d : ℕ}
    (H : (need n U).Ok lim free d) :
    (ThreeSumColorDriverResources.need ThreeSumFastResourcesColor.need n U).Ok lim (free+19) (d+1) :=
  ThreeSumColorDriverResources.scan_of_full_ok H

theorem color_of_ok {lim : Limits} {n U free d dd : ℕ}
    (H : (need n U).Ok lim free d)
    (hd : dd+(ThreeSumFastResourcesColor.need n U).depth≤lim.depth) :
    (ThreeSumFastResourcesColor.need n U).Ok lim (free+25) dd := by
  simpa only [Nat.add_assoc] using ThreeSumColorDriverResources.color_of_ok (scan_of_ok H) hd

theorem driver_bounds_of_ok {lim : Limits} {n U free d : ℕ}
    (H : (need n U).Ok lim free d) :
    free+25≤lim.space ∧ (LightColorScanHost.word n : ℤ)≤lim.word ∧
      d+ColorParameters.count (LightColorParametersCosts.width n)+
        (ThreeSumFastResourcesColor.need n U).depth+5≤lim.depth := by
  obtain ⟨hs,hw,hd⟩ := ThreeSumColorDriverResources.scan_bounds_of_ok (scan_of_ok H)
  exact ⟨by omega,hw,by omega⟩

theorem outer_depth_of_ok {lim : Limits} {n U free d : ℕ}
    (H : (need n U).Ok lim free d) : d<lim.depth := by
  have hd := (driver_bounds_of_ok H).2.2
  omega

theorem header_regions_of_ok {lim : Limits} {n U free d : ℕ}
    (H : (need n U).Ok lim free d) :
    free+19≤lim.space ∧ free+19+6≤lim.space ∧ (free+25 : ℤ)≤lim.word := by
  have hs := (driver_bounds_of_ok H).1
  refine ⟨by omega,by omega,?_⟩
  exact (Int.ofNat_le.mpr hs).trans H.space

noncomputable section

theorem poly_need : Light.PolyNeed need :=
  ThreeSumColorDriverResources.full_poly_need ThreeSumFastResourcesColor.poly_need

end
end ThreeSum.ThreeSumFastResourcesDriver
