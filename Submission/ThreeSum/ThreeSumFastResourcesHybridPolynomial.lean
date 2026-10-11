import Submission.ThreeSum.ThreeSumFastResourcesHybrid

/-! # Polynomial hybrid limits with the computed magnitude substituted

The exponent and cutoff are fixed program parameters. The polynomial
bound is valid for every input size and supplied magnitude, including
zero, and does not rely on eventual growth to justify substitution.
-/

namespace ThreeSum.ThreeSumFastResourcesHybrid

open Light StageBounds ArithmeticStageBounds

set_option maxHeartbeats 300000
set_option maxRecDepth 16000

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

def poweredDriverNeed (κ n _U : ℕ) : Light.Need := ThreeSumFastResourcesDriver.need n (n^κ)

noncomputable section

theorem powered_driver_poly_need (κ : ℕ) : Light.PolyNeed (poweredDriverNeed κ) := by
  obtain ⟨s,e,h⟩ := ThreeSumFastResourcesDriver.poly_need
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

theorem poly_need (κ cutoff : ℕ) : Light.PolyNeed (need κ cutoff) := by
  obtain ⟨sf,ef,hf⟩ := powered_driver_poly_need κ
  obtain ⟨sb,eb,hb⟩ := LightBruteThreeSum.poly_need
  obtain ⟨sc,ec,hc⟩ := PolynomialResources.pair_polyBound_of_powerBound (controls_powerBound κ cutoff) 0
  refine ⟨sf+sb+sc+3,ef+eb+ec,fun n U => ?_⟩
  let F := Light.polyBound (sf+sb+sc) (ef+eb+ec) [n,U]
  have hF := hf n U
  have hB := hb n U
  have hC : controls κ cutoff n≤Light.polyBound sc ec [n,U] := by
    simpa only [pow_zero,mul_one] using hc n U
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
  dsimp only [poweredDriverNeed] at hF
  dsimp only [need]
  exact ⟨by omega,by omega,by omega⟩

end
end ThreeSum.ThreeSumFastResourcesHybrid
