import Submission.ThreeSum.TernaryArenaAllocationResources
import Submission.ThreeSum.LightTernaryColorPreparationProof
import Submission.ThreeSum.TernaryColorPreludeResources

noncomputable section
namespace ThreeSum.TernaryColoredSolverNeed
open Light TernaryArenaLayout TernaryArenaAllocation TernaryArenaPrefixFootprints
open TernaryCoverGoodMaps TernaryLocalParameters LightTernaryColorPreparation
set_option maxHeartbeats 500000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]

/-- Actual worst-case color preparation storage, before the reused arena. -/
def preparationCells (M b n U : ℕ) : ℕ :=
  1000*(n+U+LightTernaryDimensions.J M b n U+3)^2*
    (2^(LightTernaryDimensions.J M b n U)+1)

def need {maps : Fin F→Weight m p} {τ cap M b K H drift scale : ℕ}
    (Alloc : Allocation maps τ cap M b K H drift scale) (n U : ℕ) : Need :=
  let J := LightTernaryDimensions.J M b n U
  let a := TernaryArenaAllocationResources.need Alloc n U
  ⟨LightTernaryColorPrelude.word n U+LightTernarySignedMatrix.word U b J+
    LightTernaryCarryCodes.word J (2^J)+LightTernaryDimensions.word M b p K n U+a.word+100,
    preparationCells M b n U+a.cells,a.depth+LightTernaryColorPrelude.depth n+1000⟩

theorem space_translate (free n J U : ℕ) :
    LightTernaryColorPreparationProof.space free n J U=
      free+LightTernaryColorPreparationProof.space 0 n J U := by
  unfold LightTernaryColorPreparationProof.space arenaFree work oMatrix positions carry cMatrix bMatrix headerAt
  omega

theorem preparation_space_general (n U J : ℕ) :
    LightTernaryColorPreparationProof.space 0 n J U≤1000*(n+U+J+3)^2*(2^J+1) := by
  let q := 2^J
  let a := n+U+J+3
  let e := a^2*(q+1)
  have ha : 1≤a := by dsimp [a]; omega
  have hs : a≤a^2 := by nlinarith
  have he : a^2≤e := Nat.le_mul_of_pos_right _ (by dsimp [q]; positivity)
  have hle (x : ℕ) (h : x≤a) : x≤e := h.trans (hs.trans he)
  have hn : n≤a := by dsimp [a]; omega
  have hU : U≤a := by dsimp [a]; omega
  have hJ : J+2≤a := by dsimp [a]; omega
  have hwidth : LightColorParametersCosts.width n≤a :=
    (TernaryColorPreludeResources.width_le n).trans (by dsimp [a]; omega)
  have hq : q≤e := (Nat.le_mul_of_pos_left (q+1) (by nlinarith : 0<a^2)).trans' (by omega)
  have hprod : n*(J+2)≤e := (Nat.mul_le_mul hn hJ).trans (by simpa [pow_two] using he)
  have hqp : q*(J+1)≤e := by
    have hh := Nat.mul_le_mul (show q≤q+1 by omega) ((show J+1≤a by omega).trans hs)
    simpa [e,Nat.mul_comm] using hh
  have hnq : n*q≤e := by
    have hh := Nat.mul_le_mul (hn.trans hs) (show q≤q+1 by omega)
    exact hh
  have hnqp : n*q*(J+2)≤e := by
    have hh := Nat.mul_le_mul_right (q+1) (Nat.mul_le_mul hn hJ)
    have hh' := Nat.mul_le_mul_right (n*(J+2)) (show q≤q+1 by omega)
    calc
      _=n*(J+2)*q := by ring
      _≤n*(J+2)*(q+1) := by simpa only [Nat.mul_comm] using hh'
      _≤e := by simpa [e,pow_two] using hh
  have hne := hle n hn
  have hue := hle U hU
  have hje := hle J (by omega)
  have hwe := hle (LightColorParametersCosts.width n) hwidth
  have hone := hle 1 ha
  change _≤1000*a^2*(q+1)
  rw [Nat.mul_assoc]
  change _≤1000*e
  unfold LightTernaryColorPreparationProof.space arenaFree work oMatrix positions carry cMatrix bMatrix headerAt
  change _≤1000*e
  dsimp only [q] at hprod hqp hnq hnqp
  nlinarith only [hprod,hqp,hnq,hnqp,hne,hue,hje,hwe,hone,hq]

theorem preparation_space (M b n U : ℕ) :
    LightTernaryColorPreparationProof.space 0 n (LightTernaryDimensions.J M b n U) U≤
      preparationCells M b n U := preparation_space_general n U _

private theorem poly_of_uniform (M : ℕ) (f : ℕ→ℕ→Need)
    (h : Uniform M (fun n U _=>(f n U).word+(f n U).cells+(f n U).depth)) : PolyNeed f := by
  unfold Uniform at h
  obtain ⟨D,E,h⟩ := h
  refine ⟨Nat.size D,E,fun n U=>?_⟩
  have hd := (Nat.lt_size_self D).le
  have hp := Nat.pow_le_pow_left (show n+U+1≤(n+1)*(U+1) by nlinarith) E
  have hh := (h n U 0 (Nat.zero_le _)).trans (Nat.mul_le_mul hd hp)
  have hpoly : polyBound (Nat.size D) E [n,U]=2^(Nat.size D)*((n+1)*(U+1))^E := by
    simp [polyBound]
  rw [←hpoly] at hh
  dsimp only at hh
  exact ⟨by omega,by omega,by omega⟩

theorem polyNeed {maps : Fin F→Weight m p} {τ cap M b K H drift scale : ℕ}
    (Alloc : Allocation maps τ cap M b K H drift scale) (hM : 1<M) (hb : 1<b) :
    PolyNeed (need Alloc) := by
  have hn := inputN M
  have hU := inputU M
  have hJ := digits hM hb
  have hq := carries hM hb
  have hc : Uniform M (fun n U _=>capacity Alloc.D Alloc.E (n+U)) := by
    dsimp only [capacity]
    arena_poly
  have hprep : Uniform M (fun n U _=>preparationCells M b n U) := by
    dsimp only [preparationCells]
    arena_poly
  have hcol : Uniform M (fun n U _=>LightTernaryColorPrelude.word n U) := by
    refine (((Uniform.const M 1000).mul (hn.succ)).mul (hU.succ)).mono ?_
    intro n U j hj
    exact TernaryColorPreludeResources.word_bound n U
  have hmat : Uniform M (fun n U _=>LightTernarySignedMatrix.word U b (LightTernaryDimensions.J M b n U)) := by
    dsimp only [LightTernarySignedMatrix.word,LightTernarySignedRow.word,LightOutputDecodeDigits.word]
    arena_poly
  have hcarry : Uniform M (fun n U _=>LightTernaryCarryCodes.word (LightTernaryDimensions.J M b n U)
      (2^(LightTernaryDimensions.J M b n U))) := by
    dsimp only [LightTernaryCarryCodes.word,LightOutputDecodeDigits.word]
    arena_poly
  have hdim : Uniform M (fun n U _=>LightTernaryDimensions.word M b p K n U) := by
    have hh : Uniform M (fun n U _=>LightTernaryDimensions.coefficient M b p K*(n+1)^2*(U+1)) := by arena_poly
    apply hh.mono
    intro n U j hj
    exact LightTernaryDimensions.word_polynomial hM hb n U
  have hdepth : Uniform M (fun n _ _=>LightTernaryColorPrelude.depth n) := by
    refine (((Uniform.const M 3).mul hn).add (Uniform.const M 20)).mono ?_
    intro n U j hj
    have hd := TernaryColorPreludeResources.depth_bound n
    have hw := TernaryColorPreludeResources.width_le n
    omega
  apply poly_of_uniform M
  dsimp only [need,TernaryArenaAllocationResources.need]
  arena_poly

theorem preparation_bounds {maps : Fin F→Weight m p} {τ cap M b K H drift scale n U free d : ℕ}
    (Alloc : Allocation maps τ cap M b K H drift scale) {lim : Limits}
    (h : (need Alloc n U).Ok lim free d) :
    LightTernaryColorPreparationProof.Bounds lim b n U (LightTernaryDimensions.J M b n U) (d+1) := by
  have hw := h.word
  have hd := h.depth
  dsimp only [need] at hw hd
  refine ⟨h.space,?_,?_,?_,by omega,by omega⟩
  all_goals apply (fun x (hx : x≤(need Alloc n U).word)=> (Int.ofNat_le.mpr hx).trans h.word)
  all_goals dsimp only [need]
  all_goals omega

 theorem preparation_fits {maps : Fin F→Weight m p} {τ cap M b K H drift scale n U free d : ℕ}
    (Alloc : Allocation maps τ cap M b K H drift scale) {lim : Limits}
    (h : (need Alloc n U).Ok lim free d) :
    LightTernaryColorPreparationProof.space free n (LightTernaryDimensions.J M b n U) U≤lim.space := by
  have hh := preparation_space M b n U
  rw [space_translate]
  have hc := h.cells
  dsimp only [need] at hc
  omega

theorem arena_ok {maps : Fin F→Weight m p} {τ cap M b K H drift scale n U free d a bN c : ℕ}
    (Alloc : Allocation maps τ cap M b K H drift scale) {lim : Limits}
    (h : (need Alloc n U).Ok lim free d) (ha : a≤n) (hb : bN≤n) (hc : c≤n) :
    (TernaryArenaAllocationResources.need Alloc n U).Ok lim
      (arenaFree free n (LightColorParametersCosts.width n) a bN c (LightTernaryDimensions.J M b n U) U) (d+100) := by
  have hm := LightTernaryColorPreparationProof.arenaFree_mono free n (LightColorParametersCosts.width n)
    (LightTernaryDimensions.J M b n U) U a bN c ha hb hc
  have hp := preparation_space M b n U
  have hactual : arenaFree free n (LightColorParametersCosts.width n) a bN c
      (LightTernaryDimensions.J M b n U) U≤free+preparationCells M b n U := by
    calc
      _≤LightTernaryColorPreparationProof.space free n (LightTernaryDimensions.J M b n U) U := hm
      _=free+LightTernaryColorPreparationProof.space 0 n (LightTernaryDimensions.J M b n U) U := space_translate _ _ _ _
      _≤_ := Nat.add_le_add_left hp free
  apply h.mono
  · dsimp only [need]
    omega
  · dsimp only [need]
    change _≤free+(preparationCells M b n U+_)
    omega
  · dsimp only [need]
    omega

theorem dimension_words {maps : Fin F→Weight m p} {τ cap M b K H drift scale n U free d : ℕ}
    (Alloc : Allocation maps τ cap M b K H drift scale) {lim : Limits}
    (h : (need Alloc n U).Ok lim free d) :
    (LightTernaryDimensions.r M n:ℤ)≤lim.word ∧
    (LightTernaryDimensions.J M b n U:ℤ)≤lim.word ∧
    (LightTernaryDimensions.dim M b p K n U:ℤ)≤lim.word ∧
    ((p^(LightTernaryDimensions.dim M b p K n U):ℕ):ℤ)≤lim.word := by
  have hw : (LightTernaryDimensions.word M b p K n U:ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (show LightTernaryDimensions.word M b p K n U≤(need Alloc n U).word by
      dsimp only [need];omega)).trans h.word
  have hs (v : ℕ) (hv : v≤LightTernaryDimensions.word M b p K n U) : (v:ℤ)≤lim.word :=
    (Int.ofNat_le.mpr hv).trans hw
  refine ⟨hs _ ?_,hs _ ?_,hs _ ?_,hs _ ?_⟩
  all_goals unfold LightTernaryDimensions.word;omega

theorem initialization_constants {maps : Fin F→Weight m p} {τ cap M b K H drift scale : ℕ}
    (Alloc : Allocation maps τ cap M b K H drift scale) (n U : ℕ) :
    p+4^(fixedLength m)+F≤capacity Alloc.D Alloc.E (n+U) := by
  have hf := (Alloc.fits n U 0 (Nat.zero_le _)).sourceWord
  dsimp only [numbers] at hf
  omega

theorem initial_word {maps : Fin F→Weight m p} {τ cap M b K H drift scale : ℕ}
    (Alloc : Allocation maps τ cap M b K H drift scale) (n U nO : ℕ)
    (hnO : nO≤n*2^(LightTernaryDimensions.J M b n U)) :
    LightTernaryInitialBudgets.word K b (p^(2*K)) drift scale n
      (LightTernaryDimensions.J M b n U) nO≤capacity Alloc.D Alloc.E (n+U) := by
  have hf := (Alloc.fits n U 0 (Nat.zero_le _)).budgets
  have hm : LightTernaryInitialBudgets.word K b (p^(2*K)) drift scale n
      (LightTernaryDimensions.J M b n U) nO≤
    LightTernaryInitialBudgets.word K b (p^(2*K)) drift scale n
      (LightTernaryDimensions.J M b n U) (n*2^(LightTernaryDimensions.J M b n U)) := by
    unfold LightTernaryInitialBudgets.word LightTernaryInitialBudgets.initial
    gcongr
  change _+_*LightTernaryInitialBudgets.word K b (p^(2*K)) drift scale n
    (LightTernaryDimensions.J M b n U) (n*2^(LightTernaryDimensions.J M b n U))+_≤_ at hf
  simp only [pow_zero,one_mul] at hf
  omega

/-- The global prelude computes n^κ literally, so this substitution is
fixed in the final per-color need and remains polynomial. -/
def fixedNeed {maps : Fin F→Weight m p} {τ cap M b K H drift scale : ℕ}
    (Alloc : Allocation maps τ cap M b K H drift scale) (κ n _U : ℕ) : Need :=need Alloc n (n^κ)

 theorem polyNeed_power {f : ℕ→ℕ→Need} (hf : PolyNeed f) (κ : ℕ) :
    PolyNeed (fun n _U=>f n (n^κ)) := by
  obtain ⟨s,k,h⟩ := hf
  let E := (κ+1)*k
  refine ⟨s+k,E,fun n U=>?_⟩
  have hpow : n^κ≤(n+1)^κ := Nat.pow_le_pow_left (by omega) _
  have hone : 1≤(n+1)^κ := Nat.one_le_pow _ _ (by omega)
  have hb : (n+1)*(n^κ+1)≤2*(n+1)^(κ+1) := by
    have hh := Nat.mul_le_mul_left (n+1) (show n^κ+1≤2*(n+1)^κ by omega)
    simpa [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh
  have hm : polyBound s k [n,n^κ]≤polyBound (s+k) E [n,U] := by
    simp only [polyBound,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,Nat.mul_one]
    calc
      _≤2^s*(2*(n+1)^(κ+1))^k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb _)
      _=2^(s+k)*(n+1)^E := by simp only [E,mul_pow,←pow_mul,pow_add]; ring
      _≤_ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by omega)) E)
  exact ⟨(h n (n^κ)).1.trans hm,(h n (n^κ)).2.1.trans hm,(h n (n^κ)).2.2.trans hm⟩

theorem fixed_polyNeed {maps : Fin F→Weight m p} {τ cap M b K H drift scale : ℕ}
    (Alloc : Allocation maps τ cap M b K H drift scale) (hM : 1<M) (hb : 1<b) (κ : ℕ) :
    PolyNeed (fixedNeed Alloc κ) := polyNeed_power (polyNeed Alloc hM hb) κ

end ThreeSum.TernaryColoredSolverNeed
