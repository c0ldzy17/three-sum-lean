import Submission.ThreeSumApsp.Lang.Lib.Emod
import Submission.ThreeSum.LightArray

/-!
# Costed signed residue conversion

This loop uses the benchmark's proved division-free remainder procedure.
Its sign argument supports either an ordinary histogram or a histogram of
the negated original integers. All source multiplicities are retained.
The logarithmic scratch region is reused for each input element.
-/

namespace ThreeSum.LightResidues

open Light

variable {lim : Limits} {P : Program} {d : ℕ}

def residue (p : ℕ) (c x : ℤ) : ℕ := ((c * x) % (p : ℤ)).toNat

theorem residue_cast {p : ℕ} (hp : 0 < p) (c x : ℤ) :
    (residue p c x : ℤ) = (c * x) % (p : ℤ) := by
  apply Int.toNat_of_nonneg
  exact Int.emod_nonneg _ (by exact_mod_cast hp.ne')

theorem residue_lt {p : ℕ} (hp : 0 < p) (c x : ℤ) : residue p c x < p := by
  have h := Int.emod_lt_of_pos (c * x) (by exact_mod_cast hp : (0 : ℤ) < p)
  rw [← residue_cast hp] at h
  exact_mod_cast h

/-- Arguments are source, destination, count, modulus, scratch, sign.
The last two locals are the loop counter and the returned residue. -/
def residuesBody (pEmod : ℕ) : Stmt :=
  .for 6 (v 2) (
    .call pEmod [v 5 *' M (v 0 +' v 6), v 3, v 4] 7 ;;
    .store (v 1 +' v 6) (v 7))

def residueBudget (U : ℕ) : ℕ := 43 * (Nat.log 2 (U + 1) + 1) + 34

def residuesTime (n U : ℕ) : ℕ := n * (residueBudget U + 30) + 6

theorem emodTime_le {x : ℤ} {p U : ℕ} (hx : |x| ≤ (U : ℤ)) :
    emodTime x.natAbs p ≤ residueBudget U := by
  have hU : x.natAbs ≤ U := by simpa only [← Int.natCast_natAbs, Nat.cast_le] using hx
  have h := emodRounds_le (M := p) hU
  unfold emodTime residueBudget
  omega

def Inv (μ : ℕ → ℤ) (src dst n p work : ℕ) (c : ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [src, dst, n, p, work, c, i, r], μ'⟩ ∧
    (∀ j < i, μ' (dst + j) = (residue p c (μ (src + j)) : ℤ)) ∧
    KeptBut μ μ' work dst n

/-- Every call uses the same scratch region; only the destination can change
below it. The source and destination are disjoint. -/
theorem residues_ends {pEmod : ℕ}
    (hem : P[pEmod]? = some emodBody)
    {μ : ℕ → ℤ} {src dst n p work U : ℕ} {c : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hp : 0 < p) (hsrc : src + n ≤ work) (hdst : dst + n ≤ work)
    (hspace : work + (Nat.log 2 (U + 1) + 2) ≤ lim.space)
    (hsep : Apart src n dst n) (hc : |c| ≤ 1)
    (hword : (4 * U + 4 * p + 16 : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src + i)| ≤ (U : ℤ)) :
    Ends lim P d (residuesBody pEmod) ⟨frame [src, dst, n, p, work, c], μ⟩
      (residuesTime n U) fun σ' =>
        (∀ i < n, σ'.mem (dst + i) = (residue p c (μ (src + i)) : ℤ)) ∧
          KeptBut μ σ'.mem work dst n := by
  have hpre : Emod.Pre lim p U work := ⟨hp, hw, hword, hspace⟩
  have hprod : ∀ i < n, |c * μ (src + i)| ≤ (U : ℤ) := by
    intro i hi
    rw [abs_mul]
    exact (mul_le_mul hc (hvalues i hi) (abs_nonneg _) (by omega)).trans (by simp)
  unfold residuesBody residuesTime
  refine Ends.for (Inv μ src dst n p work c) n (residueBudget U + 22)
    ?start ?round ?done ?bound
  case start =>
    refine ⟨0, μ, ?_, ?_, fun _ _ => rfl⟩
    · exact congrArg (fun loc => (⟨loc, μ⟩ : State))
        ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro j hj
      omega
  case round =>
    rintro i _ hi _ ⟨r, μ', rfl, written, kept⟩
    have hread : μ' (src + i) = μ (src + i) := kept _ ⟨by omega, by omega⟩
    have hproduct := hprod i hi
    have hmul := abs_le.mp hproduct
    have hval := abs_le.mp (hvalues i hi)
    have hsign := abs_le.mp hc
    have htime := emodTime_le (p := p) hproduct
    unfold emodTime residueBudget at htime
    have hlog : Nat.log 2 (1 + U) = Nat.log 2 (U + 1) := by rw [Nat.add_comm]
    have hmodlt := residue_lt hp c (μ (src + i))
    light_call (emod_meets (x := c * μ (src + i)) hem hpre hproduct)
      using hread, residueBudget with _ μ₁ ⟨hresult, hkept⟩
    rw [← residue_cast hp] at hresult
    subst_vars
    light_store (dst + i) (residue p c (μ (src + i)) : ℕ) using residueBudget
    refine ⟨by simp, residue p c (μ (src + i)),
      Function.update μ₁ (dst + i) (residue p c (μ (src + i)) : ℕ),
      by simp [update_frame_setLocal], ?_, ?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega)]
        exact (hkept _ (by omega)).trans (written j hj)
      · simp
    · intro a ⟨ha, hout⟩
      rw [Function.update_of_ne (by omega)]
      exact (hkept a ha).trans (kept a ⟨ha, hout⟩)
  case done =>
    rintro _ _ ⟨r, μ', rfl, written, kept⟩
    exact ⟨written, kept⟩
  case bound =>
    rintro i _ _ _ ⟨r, μ', rfl, _, _⟩
    simp

theorem residues_meets {pResidues pEmod : ℕ}
    (hres : P[pResidues]? = some (residuesBody pEmod))
    (hem : P[pEmod]? = some emodBody)
    {μ : ℕ → ℤ} {src dst n p work U : ℕ} {c : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hp : 0 < p) (hsrc : src + n ≤ work) (hdst : dst + n ≤ work)
    (hspace : work + (Nat.log 2 (U + 1) + 2) ≤ lim.space)
    (hsep : Apart src n dst n) (hc : |c| ≤ 1)
    (hword : (4 * U + 4 * p + 16 : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src + i)| ≤ (U : ℤ)) :
    Meets lim P pResidues d [src, dst, n, p, work, c] μ (residuesTime n U)
      fun _ μ' =>
        (∀ i < n, μ' (dst + i) = (residue p c (μ (src + i)) : ℤ)) ∧
          KeptBut μ μ' work dst n := by
  exact Meets.of_body hres (residues_ends hem hw hd hp hsrc hdst hspace hsep hc hword hvalues)

end ThreeSum.LightResidues
