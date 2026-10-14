import Submission.ThreeSum.PolynomialResources
import Submission.ThreeSum.ArithmeticStageBounds
import Submission.ThreeSum.LightBruteThreeSum
import Submission.ThreeSum.LightNatPower

/-! # Polynomial resources for an arbitrary concrete fast solver

The fast branch uses the computed magnitude `n^κ`; the fallback retains
the supplied magnitude `U`. Both branches reuse the same free address.
The fixed cutoff and exponent are included among the actual scalar word
controls, together with every intermediate integer power.
-/

namespace ThreeSum.TernaryHybridResources

open Light StageBounds ArithmeticStageBounds

set_option maxHeartbeats 1700000
set_option maxRecDepth 16000

def controls (κ cutoff n : ℕ) : ℕ := n+κ+cutoff+(n+1)^(κ+1)+10

variable (fastNeed : ℕ → ℕ → Light.Need)

def need (fastNeed : ℕ → ℕ → Light.Need) (κ cutoff n U : ℕ) : Light.Need :=
  ⟨(fastNeed n (n^κ)).word+(LightBruteThreeSum.need n U).word+controls κ cutoff n,
    max (fastNeed n (n^κ)).cells (LightBruteThreeSum.need n U).cells,
    max (fastNeed n (n^κ)).depth (LightBruteThreeSum.need n U).depth+3⟩

theorem cells_eq (κ cutoff n U : ℕ) :
    (need fastNeed κ cutoff n U).cells=(fastNeed n (n^κ)).cells := by
  simp only [need,LightBruteThreeSum.need,Nat.max_zero]

theorem fast_at_depth_of_ok {lim : Limits} {κ cutoff n U free d e : ℕ}
    (H : (need fastNeed κ cutoff n U).Ok lim free d) (he : e≤d+2) :
    (fastNeed n (n^κ)).Ok lim free e :=
  H.mono (by dsimp only [need]; omega) (by dsimp only [need]; omega)
    (by dsimp only [need]; omega)

theorem fast_of_ok {lim : Limits} {κ cutoff n U free d : ℕ}
    (H : (need fastNeed κ cutoff n U).Ok lim free d) :
    (fastNeed n (n^κ)).Ok lim free (d+1) :=
  fast_at_depth_of_ok fastNeed H (by omega)

theorem brute_at_depth_of_ok {lim : Limits} {κ cutoff n U free d e : ℕ}
    (H : (need fastNeed κ cutoff n U).Ok lim free d) (he : e≤d+2) :
    (LightBruteThreeSum.need n U).Ok lim free e :=
  H.mono (by dsimp only [need]; omega) (by dsimp only [need]; omega)
    (by dsimp only [need]; omega)

theorem brute_of_ok {lim : Limits} {κ cutoff n U free d : ℕ}
    (H : (need fastNeed κ cutoff n U).Ok lim free d) :
    (LightBruteThreeSum.need n U).Ok lim free (d+1) :=
  brute_at_depth_of_ok fastNeed H (by omega)

theorem scalar_word_of_ok {lim : Limits} {κ cutoff n U free d : ℕ}
    (H : (need fastNeed κ cutoff n U).Ok lim free d) :
    ((n+κ+cutoff+U+(n+1)^(κ+1)+10 : ℕ) : ℤ)≤lim.word := by
  have hh : n+κ+cutoff+U+(n+1)^(κ+1)+10≤(need fastNeed κ cutoff n U).word := by
    dsimp only [need,controls,LightBruteThreeSum.need,LightOriginalTripleRow.word]
    omega
  exact (Int.ofNat_le.mpr hh).trans H.word

theorem power_word_of_ok {lim : Limits} {κ cutoff n U free d i : ℕ}
    (H : (need fastNeed κ cutoff n U).Ok lim free d) (hi : i≤κ) : ((n^i : ℕ) : ℤ)≤lim.word := by
  have hh : n^i≤(n+1)^(κ+1) :=
    (Nat.pow_le_pow_left (by omega : n≤n+1) i).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  exact (Int.ofNat_le.mpr (show n^i≤n+κ+cutoff+U+(n+1)^(κ+1)+10 by omega)).trans
    (scalar_word_of_ok fastNeed H)

theorem outer_depth_of_ok {lim : Limits} {κ cutoff n U free d : ℕ}
    (H : (need fastNeed κ cutoff n U).Ok lim free d) : d+2<lim.depth := by
  have hd := H.depth
  dsimp only [need] at hd
  omega

theorem source_region_of_ok {lim : Limits} {κ cutoff n U src free d : ℕ}
    (H : (need fastNeed κ cutoff n U).Ok lim free d) (hsrc : src+n≤free) :
    src+n≤lim.space ∧ (free : ℤ)≤lim.word := by
  have hf : free≤lim.space := by have hh := H.cells; omega
  exact ⟨hsrc.trans hf,(Int.ofNat_le.mpr hf).trans H.space⟩

theorem power_meets {lim : Limits} {κ cutoff n U free d : ℕ} (μ : ℕ→ℤ)
    (H : (need fastNeed κ cutoff n U).Ok lim free d) :
    Meets lim LightNatPower.program 0 (d+1) [n,κ] μ (LightNatPower.time κ)
      (fun r ν => r=((n^κ : ℕ) : ℤ) ∧ ν=μ) := by
  apply LightNatPower.program_meets μ
  · exact (Int.ofNat_le.mpr (show κ≤n+κ+cutoff+U+(n+1)^(κ+1)+10 by omega)).trans
      (scalar_word_of_ok fastNeed H)
  · intro i hi
    exact power_word_of_ok fastNeed H hi

theorem polyBound_substitute_pow (s e κ n U : ℕ) :
    Light.polyBound s e [n,n^κ]≤Light.polyBound (s+e) ((κ+1)*e) [n,U] := by
  let B := (n+1)*(U+1)
  have hn : n+1≤B := Nat.le_mul_of_pos_right _ (by omega)
  have hB : 1≤B := by unfold B; exact Nat.mul_pos (by omega) (by omega)
  have hnPow : n^κ≤B^κ := Nat.pow_le_pow_left (by omega) κ
  have h1 : 1≤B^κ := Nat.one_le_pow _ _ hB
  have hsum : n^κ+1≤2*B^κ := by omega
  have hprod : (n+1)*(n^κ+1)≤2*B^(κ+1) := by
    calc
      _ ≤ B*(2*B^κ) := Nat.mul_le_mul hn hsum
      _ = _ := by rw [pow_succ]; ring
  calc
    _ = 2^s*((n+1)*(n^κ+1))^e := by simp [Light.polyBound,mul_pow]
    _ ≤ 2^s*(2*B^(κ+1))^e := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hprod e)
    _ = Light.polyBound (s+e) ((κ+1)*e) [n,U] := by
      have hr : Light.polyBound (s+e) ((κ+1)*e) [n,U]=2^(s+e)*B^((κ+1)*e) := by
        simp [Light.polyBound,B,mul_pow]
      rw [hr,mul_pow,← pow_mul,pow_add]
      ring

def poweredFastNeed (fastNeed : ℕ → ℕ → Light.Need) (κ n _U : ℕ) : Light.Need := fastNeed n (n^κ)

noncomputable section

theorem powered_fast_poly_need (hf : Light.PolyNeed fastNeed) (κ : ℕ) : Light.PolyNeed (poweredFastNeed fastNeed κ) := by
  obtain ⟨s,e,h⟩ := hf
  refine ⟨s+e,(κ+1)*e,fun n U => ?_⟩
  have hh := h n (n^κ)
  have ht := polyBound_substitute_pow s e κ n U
  exact ⟨hh.1.trans ht,hh.2.1.trans ht,hh.2.2.trans ht⟩

theorem controls_powerBound (κ cutoff : ℕ) :
    PowerBound (controls κ cutoff) ((κ+1 : ℕ) : ℝ) := by
  have hbase : PowerBound (fun n : ℕ => n+1) 1 :=
    identity_powerBound.add_same ((PowerBound.const 1).mono_exponent (by norm_num))
  have hp : PowerBound (fun n : ℕ => (n+1)^(κ+1)) ((κ+1 : ℕ) : ℝ) := by
    simpa only [mul_one] using hbase.pow (κ+1)
  have hn : PowerBound (fun n : ℕ => n) ((κ+1 : ℕ) : ℝ) :=
    identity_powerBound.mono_exponent (by exact_mod_cast (show 1≤κ+1 by omega))
  have hc : PowerBound (fun _ : ℕ => κ+cutoff+10) ((κ+1 : ℕ) : ℝ) :=
    (PowerBound.const _).mono_exponent (by positivity)
  change PowerBound (fun n => n+κ+cutoff+(n+1)^(κ+1)+10) ((κ+1 : ℕ) : ℝ)
  convert (hn.add_same hp).add_same hc using 1
  funext n
  omega

theorem poly_need (hf : Light.PolyNeed fastNeed) (κ cutoff : ℕ) : Light.PolyNeed (need fastNeed κ cutoff) := by
  obtain ⟨sf,ef,hf⟩ := powered_fast_poly_need fastNeed hf κ
  obtain ⟨sb,eb,hb⟩ := LightBruteThreeSum.poly_need
  obtain ⟨sc,ec,hc⟩ := PolynomialResources.pair_polyBound_of_powerBound (controls_powerBound κ cutoff) 0
  refine ⟨sf+sb+sc+3,ef+eb+ec,fun n U => ?_⟩
  let F := Light.polyBound (sf+sb+sc) (ef+eb+ec) [n,U]
  have hF := hf n U
  have hB := hb n U
  have hC : controls κ cutoff n≤Light.polyBound sc ec [n,U] := by
    simpa only [controls,pow_zero,mul_one] using hc n U
  have hmf : Light.polyBound sf ef [n,U]≤F := Light.polyBound_mono (by omega) (by omega) _
  have hmb : Light.polyBound sb eb [n,U]≤F := Light.polyBound_mono (by omega) (by omega) _
  have hmc : Light.polyBound sc ec [n,U]≤F := Light.polyBound_mono (by omega) (by omega) _
  have hpos : 1≤F := by
    unfold F Light.polyBound
    simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    exact Nat.mul_pos (by positivity) (by positivity)
  have he : Light.polyBound (sf+sb+sc+3) (ef+eb+ec) [n,U]=8*F := by
    unfold F Light.polyBound
    rw [pow_add]
    norm_num
    ring
  rw [he]
  dsimp only [poweredFastNeed] at hF
  dsimp only [need]
  exact ⟨by omega,by omega,by omega⟩


end
end ThreeSum.TernaryHybridResources
