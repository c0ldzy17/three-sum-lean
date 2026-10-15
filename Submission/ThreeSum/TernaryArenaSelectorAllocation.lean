import Submission.ThreeSum.TernaryArenaCandidateScoreBounds

noncomputable section
namespace ThreeSum.TernaryArenaSelectorAllocation
open Light TernaryArenaPrefixFootprints TernaryArenaAllocation TernaryArenaLayout
open TernaryCoverGoodMaps TernaryLocalParameters
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000

/-- The arena's fourth-power envelope pays the selector's genuine integer
cross products without replacing the score cap by the allocation size. -/
theorem word_envelope {T n score dB dC dP tB tC tP : ℕ}
    (hT : 1≤T) (hn : n≤T) (hs : score≤T)
    (hdB : dB≤T) (hdC : dC≤T) (hdP : dP≤T)
    (htB : tB≤T) (htC : tC≤T) (htP : tP≤T) :
    LightTernaryRowSelector.word n score dB dC dP tB tC tP≤(T+1)^4 := by
  have hm : score*(dB+dC+dP+1)≤T*(3*T+1) :=
    Nat.mul_le_mul hs (by omega)
  have h3 : T≤T^3 := by
    calc
      T≤T*T^2 := Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
      _=T^3 := by ring
  have h4 : 1≤T^4 := Nat.one_le_pow 4 T hT
  unfold LightTernaryRowSelector.word
  nlinarith

private theorem self_fits (A : Numbers) : Fits A.list.sum A := by
  intro v hv
  exact List.le_sum_of_mem hv

/-- Runtime thresholds use the actual requester count. The larger monotone
initial-word expression in the fixed footprint bounds this value. -/
theorem initial_le {K b n J nO nO' : ℕ} (hO : nO≤nO') (a drift scale : ℕ) :
    LightTernaryInitialBudgets.initial K b n J nO≤
      LightTernaryInitialBudgets.word K b a drift scale n J nO' := by
  have hh : LightTernaryInitialBudgets.initial K b n J nO≤
      LightTernaryInitialBudgets.initial K b n J nO' := by
    unfold LightTernaryInitialBudgets.initial
    gcongr
  apply hh.trans
  unfold LightTernaryInitialBudgets.word
  omega

theorem controls (maps : Fin F→Weight m p) (τ cap M b K H drift scale n U j nO : ℕ)
    (hO : nO≤n*2^(LightTernaryDimensions.J M b n U)) :
    let T := total maps τ cap M b K H drift scale n U j
    1≤T ∧ p^j≤T ∧ (p^(2*K))^j≤T ∧ 9^j*n^2≤T ∧
    (drift*scale)^j*LightTernaryInitialBudgets.initial K b n
      (LightTernaryDimensions.J M b n U) nO≤T ∧
    (numbers maps τ cap M b K H drift scale n U j).candidateScore≤T ∧
    (p^(LightTernaryDimensions.dim M b p K n U))^2≤T := by
  let A := numbers maps τ cap M b K H drift scale n U j
  have HF : Fits (total maps τ cap M b K H drift scale n U j) A := self_fits A
  have hlocal := HF.localSize
  have hsource := HF.sourceWord
  have hbudget := HF.budgets
  have hscore := HF.candidateScore
  have hmenu := HF.menuCells
  have hi := initial_le (K := K) (b := b) (n := n)
    (J := LightTernaryDimensions.J M b n U) hO (p^(2*K)) drift scale
  have hmul := Nat.mul_le_mul_left ((drift*scale)^j) hi
  have hq := TernaryExtensionEncoding.menu_field_upper (p := p)
    (LightTernaryDimensions.J M b n U+2) K
  have hq' : p^(LightTernaryDimensions.dim M b p K n U)≤
      8*p^(4*K+1)*(LightTernaryDimensions.J M b n U+3) := by
    simpa only [LightTernaryDimensions.dim,show LightTernaryDimensions.J M b n U+2+1=
      LightTernaryDimensions.J M b n U+3 by omega] using hq
  have hq2 := Nat.pow_le_pow_left hq' 2
  have hq3 : (8*p^(4*K+1)*(LightTernaryDimensions.J M b n U+3))^2≤
      (8*p^(4*K+1)*(LightTernaryDimensions.J M b n U+3))^2*
        (LightTernaryDimensions.J M b n U+2) := Nat.le_mul_of_pos_right _ (by omega)
  dsimp only [A,numbers] at hlocal hsource hbudget hmenu
  have hRcast : (0 : ℤ)≤(((4 : ℕ) : ℤ)^fixedLength m) := by positivity
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,hscore,?_⟩
  all_goals omega

/-- Every actual selector input is covered by the single fixed arena need. -/
theorem selector {lim : Limits} {depth : ℕ}
    (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (Alloc : Allocation maps τ cap M b K H drift scale)
    (n U j nO free : ℕ) (hj : j≤Nat.clog M (n^2))
    (hO : nO≤n*2^(LightTernaryDimensions.J M b n U))
    (hok : (TernaryArenaAllocationResources.need Alloc n U).Ok lim free depth) :
    (LightTernaryRowSelector.word
      ((p^(LightTernaryDimensions.dim M b p K n U))^2)
      ((numbers maps τ cap M b K H drift scale n U j).candidateScore)
      (p^j) (p^j) ((p^(2*K))^j)
      (9^j*n^2) (9^j*n^2)
      ((drift*scale)^j*LightTernaryInitialBudgets.initial K b n
        (LightTernaryDimensions.J M b n U) nO) : ℤ)≤lim.word := by
  obtain ⟨hT,hd,hp,ht,hinit,hscore,hmenu⟩ := controls maps τ cap M b K H drift scale n U j nO hO
  have hh := word_envelope hT hmenu hscore hd hd hp ht ht hinit
  have he := Alloc.bound n U j hj
  have hc : LightTernaryRowSelector.word
      ((p^(LightTernaryDimensions.dim M b p K n U))^2)
      ((numbers maps τ cap M b K H drift scale n U j).candidateScore)
      (p^j) (p^j) ((p^(2*K))^j) (9^j*n^2) (9^j*n^2)
      ((drift*scale)^j*LightTernaryInitialBudgets.initial K b n
        (LightTernaryDimensions.J M b n U) nO)≤capacity Alloc.D Alloc.E (n+U) :=
    hh.trans he
  exact (Int.ofNat_le.mpr hc).trans (TernaryArenaAllocationResources.ok Alloc hok).2.1

end ThreeSum.TernaryArenaSelectorAllocation
