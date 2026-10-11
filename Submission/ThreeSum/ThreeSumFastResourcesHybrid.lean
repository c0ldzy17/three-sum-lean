import Submission.ThreeSum.ThreeSumFastResourcesDriverHost
import Submission.ThreeSum.LightBruteThreeSum
import Submission.ThreeSum.LightNatPower

/-! # Affine resources for the actual finite-cutoff hybrid

The fast branch uses the computed magnitude `n^κ`; the fallback retains
the supplied magnitude `U`. Both branches reuse the same free address.
The fixed cutoff and exponent are included among the actual scalar word
controls, together with every intermediate integer power.
-/

namespace ThreeSum.ThreeSumFastResourcesHybrid

open Light

set_option maxHeartbeats 1700000
set_option maxRecDepth 16000

def controls (κ cutoff n : ℕ) : ℕ := n+κ+cutoff+(n+1)^(κ+1)+10

def need (κ cutoff n U : ℕ) : Light.Need :=
  ⟨(ThreeSumFastResourcesDriver.need n (n^κ)).word+(LightBruteThreeSum.need n U).word+controls κ cutoff n,
    max (ThreeSumFastResourcesDriver.need n (n^κ)).cells (LightBruteThreeSum.need n U).cells,
    max (ThreeSumFastResourcesDriver.need n (n^κ)).depth (LightBruteThreeSum.need n U).depth+3⟩

theorem cells_eq (κ cutoff n U : ℕ) :
    (need κ cutoff n U).cells=(ThreeSumFastResourcesDriver.need n (n^κ)).cells := by
  simp only [need,LightBruteThreeSum.need,Nat.max_zero]

theorem fast_at_depth_of_ok {lim : Limits} {κ cutoff n U free d e : ℕ}
    (H : (need κ cutoff n U).Ok lim free d) (he : e≤d+2) :
    (ThreeSumFastResourcesDriver.need n (n^κ)).Ok lim free e :=
  H.mono (by dsimp only [need]; omega) (by dsimp only [need]; omega)
    (by dsimp only [need]; omega)

theorem fast_of_ok {lim : Limits} {κ cutoff n U free d : ℕ}
    (H : (need κ cutoff n U).Ok lim free d) :
    (ThreeSumFastResourcesDriver.need n (n^κ)).Ok lim free (d+1) :=
  fast_at_depth_of_ok H (by omega)

theorem brute_at_depth_of_ok {lim : Limits} {κ cutoff n U free d e : ℕ}
    (H : (need κ cutoff n U).Ok lim free d) (he : e≤d+2) :
    (LightBruteThreeSum.need n U).Ok lim free e :=
  H.mono (by dsimp only [need]; omega) (by dsimp only [need]; omega)
    (by dsimp only [need]; omega)

theorem brute_of_ok {lim : Limits} {κ cutoff n U free d : ℕ}
    (H : (need κ cutoff n U).Ok lim free d) :
    (LightBruteThreeSum.need n U).Ok lim free (d+1) :=
  brute_at_depth_of_ok H (by omega)

theorem scalar_word_of_ok {lim : Limits} {κ cutoff n U free d : ℕ}
    (H : (need κ cutoff n U).Ok lim free d) :
    ((n+κ+cutoff+U+(n+1)^(κ+1)+10 : ℕ) : ℤ)≤lim.word := by
  have hh : n+κ+cutoff+U+(n+1)^(κ+1)+10≤(need κ cutoff n U).word := by
    dsimp only [need,controls,LightBruteThreeSum.need,LightOriginalTripleRow.word]
    omega
  exact (Int.ofNat_le.mpr hh).trans H.word

theorem power_word_of_ok {lim : Limits} {κ cutoff n U free d i : ℕ}
    (H : (need κ cutoff n U).Ok lim free d) (hi : i≤κ) : ((n^i : ℕ) : ℤ)≤lim.word := by
  have hh : n^i≤(n+1)^(κ+1) :=
    (Nat.pow_le_pow_left (by omega : n≤n+1) i).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  exact (Int.ofNat_le.mpr (show n^i≤n+κ+cutoff+U+(n+1)^(κ+1)+10 by omega)).trans
    (scalar_word_of_ok H)

theorem outer_depth_of_ok {lim : Limits} {κ cutoff n U free d : ℕ}
    (H : (need κ cutoff n U).Ok lim free d) : d+2<lim.depth := by
  have hd := H.depth
  dsimp only [need] at hd
  omega

theorem source_region_of_ok {lim : Limits} {κ cutoff n U src free d : ℕ}
    (H : (need κ cutoff n U).Ok lim free d) (hsrc : src+n≤free) :
    src+n≤lim.space ∧ (free : ℤ)≤lim.word := by
  have hf : free≤lim.space := by have hh := H.cells; omega
  exact ⟨hsrc.trans hf,(Int.ofNat_le.mpr hf).trans H.space⟩

theorem power_meets {lim : Limits} {κ cutoff n U free d : ℕ} (μ : ℕ→ℤ)
    (H : (need κ cutoff n U).Ok lim free d) :
    Meets lim LightNatPower.program 0 (d+1) [n,κ] μ (LightNatPower.time κ)
      (fun r ν => r=((n^κ : ℕ) : ℤ) ∧ ν=μ) := by
  apply LightNatPower.program_meets μ
  · exact (Int.ofNat_le.mpr (show κ≤n+κ+cutoff+U+(n+1)^(κ+1)+10 by omega)).trans
      (scalar_word_of_ok H)
  · intro i hi
    exact power_word_of_ok H hi

end ThreeSum.ThreeSumFastResourcesHybrid
