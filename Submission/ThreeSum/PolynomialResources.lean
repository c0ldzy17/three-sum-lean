import Submission.ThreeSum.StageBounds
import Submission.ThreeSumApsp.Lang.Tasks

/-!
# From proved resource envelopes to the compiler's polynomial limits

An eventual power bound supplies a single polynomial valid at every input
size, by explicitly absorbing its finitely many exceptions. Multiplying
by a fixed power of the input magnitude then gives the exact two-parameter
`Light.PolyNeed` required by the verified compiler. These lemmas do not
supply resource envelopes for an algorithm; callers must prove those.
-/

namespace ThreeSum.PolynomialResources

open StageBounds Filter Real
open scoped Topology

noncomputable section

theorem natural_polynomial_of_powerBound {f : ℕ → ℕ} {a : ℝ} (hf : PowerBound f a) :
    ∃ C k : ℕ, ∀ n : ℕ, f n ≤ C*(n+1)^k := by
  let k : ℕ := ⌈a+1⌉₊
  have hk : a+1 ≤ (k : ℝ) := Nat.le_ceil _
  have he : ∀ᶠ n : ℕ in atTop, f n ≤ n^k := by
    filter_upwards [hf 1 (by norm_num),eventually_ge_atTop (1 : ℕ)] with n hn hn1
    have hh := hn.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) hk)
    rw [Real.rpow_natCast] at hh
    exact_mod_cast hh
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp he
  let C : ℕ := 1+∑ i ∈ Finset.range N, f i
  have hC : 1 ≤ C := by dsimp [C]; omega
  refine ⟨C,k,fun n => ?_⟩
  by_cases hn : N ≤ n
  · exact ((hN n hn).trans (Nat.pow_le_pow_left (by omega) k)).trans
      (Nat.le_mul_of_pos_left _ hC)
  · have hh : f n ≤ ∑ i ∈ Finset.range N, f i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    have hsmall : f n ≤ C := by dsimp [C]; omega
    exact hsmall.trans (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by omega)))

theorem polyBound_of_powerBound {f : ℕ → ℕ} {a : ℝ} (hf : PowerBound f a) :
    ∃ s k : ℕ, ∀ n : ℕ, f n ≤ Light.polyBound s k [n] := by
  obtain ⟨C,k,h⟩ := natural_polynomial_of_powerBound hf
  exact ⟨Nat.size C,k,fun n => by
    simpa only [zero_add] using Light.le_polyBound_of_le_pow (s := 0) le_rfl (h n)⟩

theorem pair_polyBound_of_powerBound {f : ℕ → ℕ} {a : ℝ} (hf : PowerBound f a) (e : ℕ) :
    ∃ s k : ℕ, ∀ n U : ℕ, f n*(U+1)^e ≤ Light.polyBound s k [n,U] := by
  obtain ⟨s,k,h⟩ := polyBound_of_powerBound hf
  refine ⟨s,k+e,fun n U => ?_⟩
  have hn : (n+1)^k ≤ (n+1)^(k+e) := Nat.pow_le_pow_right (by omega) (by omega)
  have hU : (U+1)^e ≤ (U+1)^(k+e) := Nat.pow_le_pow_right (by omega) (by omega)
  have hf' : f n ≤ 2^s*(n+1)^k := by simpa only [Light.polyBound,List.map_cons,
    List.map_nil,List.prod_cons,List.prod_nil,mul_one] using h n
  calc
    _ ≤ (2^s*(n+1)^k)*(U+1)^e := Nat.mul_le_mul_right _ hf'
    _ ≤ (2^s*(n+1)^(k+e))*(U+1)^(k+e) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hn) hU
    _ = Light.polyBound s (k+e) [n,U] := by simp [Light.polyBound,mul_pow,mul_assoc]

theorem polyNeed_of_envelope {need : ℕ → ℕ → Light.Need} {f : ℕ → ℕ} {a : ℝ}
    (hf : PowerBound f a) (e : ℕ)
    (hword : ∀ n U, (need n U).word ≤ f n*(U+1)^e)
    (hcells : ∀ n U, (need n U).cells ≤ f n*(U+1)^e)
    (hdepth : ∀ n U, (need n U).depth ≤ f n*(U+1)^e) : Light.PolyNeed need := by
  obtain ⟨s,k,h⟩ := pair_polyBound_of_powerBound hf e
  exact ⟨s,k,fun n U => ⟨(hword n U).trans (h n U),
    (hcells n U).trans (h n U),(hdepth n U).trans (h n U)⟩⟩

theorem polyNeed_of_separate_envelopes {need : ℕ → ℕ → Light.Need}
    {fw fc fd : ℕ → ℕ} {aw ac ad : ℝ}
    (hw : PowerBound fw aw) (hc : PowerBound fc ac) (hd : PowerBound fd ad)
    (ew ec ed : ℕ)
    (hword : ∀ n U, (need n U).word ≤ fw n*(U+1)^ew)
    (hcells : ∀ n U, (need n U).cells ≤ fc n*(U+1)^ec)
    (hdepth : ∀ n U, (need n U).depth ≤ fd n*(U+1)^ed) : Light.PolyNeed need := by
  obtain ⟨sw,kw,hwb⟩ := pair_polyBound_of_powerBound hw ew
  obtain ⟨sc,kc,hcb⟩ := pair_polyBound_of_powerBound hc ec
  obtain ⟨sd,kd,hdb⟩ := pair_polyBound_of_powerBound hd ed
  refine ⟨sw+sc+sd,kw+kc+kd,fun n U => ⟨?_,?_,?_⟩⟩
  · exact ((hword n U).trans (hwb n U)).trans (Light.polyBound_mono (by omega) (by omega) _)
  · exact ((hcells n U).trans (hcb n U)).trans (Light.polyBound_mono (by omega) (by omega) _)
  · exact ((hdepth n U).trans (hdb n U)).trans (Light.polyBound_mono (by omega) (by omega) _)

end
end ThreeSum.PolynomialResources
