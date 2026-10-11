import Submission.ThreeSum.LightOneHot

/-!
# Evaluating a whole list of one-hot mask hashes

This wrapper builds the powers table itself, hashes each stored mask, and
writes the raw nonnegative values. It is shared by the local-cover matrix
construction and input-source encoding. The cost is linear in the number
of masks times their width; no evaluation oracle is assumed.
-/

namespace ThreeSum.LightMaskHashes

open Light LightSubsetAddress

set_option maxHeartbeats 1000000

def loopBody (pHash : ℕ) : Stmt :=
  .for 7 (v 3) (
    .call pHash [v 0,M (v 1 +' v 7),v 0,v 6,v 4,v 5] 8 ;;
    .store (v 2 +' v 7) (v 8))

def body (pPowers pHash : ℕ) : Stmt :=
  .call pPowers [v 6,v 0 +' k 1,k 2] 8 ;;
  loopBody pHash

def time (L n : ℕ) : ℕ := powTableTime (L+1)+n*(LightOneHot.time L+70)+50

def Inv (μ : ℕ → ℤ) (mask w0 w1 : ℕ → ℕ)
    (L masks dst n src0 src1 work i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [L,masks,dst,n,src0,src1,work,i,r],μ'⟩ ∧
    (∀ j < i, μ' (dst+j) = (OneHotMask.eval w0 w1 L (mask j) : ℤ)) ∧
    Powers μ' work L ∧ KeptBut μ μ' work dst n

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain pPowers pHash : ℕ}
    (hmain : P[pMain]? = some (body pPowers pHash))
    (hpowers : P[pPowers]? = some powTableBody)
    (hhash : P[pHash]? = some (LightOneHot.body pHash))
    {μ : ℕ → ℤ} {L masks dst n src0 src1 work U : ℕ}
    (mask w0 w1 : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+1 ≤ lim.depth)
    (hspace : work+(L+1) ≤ lim.space)
    (hmasks : masks+n ≤ dst) (hsrc0 : src0+L ≤ dst) (hsrc1 : src1+L ≤ dst)
    (hdst : dst+n ≤ work)
    (hword : (LightOneHot.word L U : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^L)
    (hread0 : ∀ i < L, μ (src0+i) = (w0 i : ℤ))
    (hread1 : ∀ i < L, μ (src1+i) = (w1 i : ℤ))
    (hbound0 : ∀ i < L, w0 i ≤ U) (hbound1 : ∀ i < L, w1 i ≤ U) :
    Meets lim P pMain d [L,masks,dst,n,src0,src1,work] μ (time L n)
      (fun _ μ' => (∀ i < n, μ' (dst+i) = (OneHotMask.eval w0 w1 L (mask i) : ℤ)) ∧
        Powers μ' work L ∧ KeptBut μ μ' work dst n) := by
  have hpWord : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : 2^(L+1) ≤ LightOneHot.word L U := by unfold LightOneHot.word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have htwo : (2 : ℤ) ≤ lim.word := by
    have hh : (2^1 : ℕ) ≤ 2^(L+1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (by exact_mod_cast hh : (2 : ℤ) ≤ ((2^(L+1) : ℕ) : ℤ)).trans hpWord
  have hvalWord : ((L*U : ℕ) : ℤ) ≤ lim.word := by
    have hh : L*U ≤ LightOneHot.word L U := by
      unfold LightOneHot.word
      exact (Nat.mul_le_mul_right U (Nat.le_succ L)).trans (Nat.le_add_left _ _)
    exact (Int.ofNat_le.mpr hh).trans hword
  apply Meets.of_body hmain
  unfold body time
  have hp := powTable_meets (d := d+1) (μ := μ) (dst := work) (L := L+1) (b := 2)
    hpowers hw hspace (by
      intro j hj
      exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) (by omega))).trans hpWord)
  light_call hp using LightOneHot.time with r μ₁ ⟨hpow,hkept⟩
  have hpow' : Powers μ₁ work L := powers_of_segment hpow
  unfold loopBody
  refine Ends.for (Inv μ mask w0 w1 L masks dst n src0 src1 work) n (LightOneHot.time L+62)
    ?_ ?_ ?_ ?_
  · refine ⟨r,μ₁,?_,?_,hpow',?_⟩
    · simp [update_frame_setLocal]
    · intro i hi
      omega
    · intro a ⟨ha,hout⟩
      exact hkept a (Or.inl ha)
  · rintro i _ hi _ ⟨r,μ',rfl,written,pows,kept⟩
    have hmr : μ' (masks+i) = (mask i : ℤ) :=
      (kept _ ⟨by omega,Or.inl (by omega)⟩).trans (hmaskRead i hi)
    have h0 : ∀ j < L, μ' (src0+j) = (w0 j : ℤ) := by
      intro j hj
      exact (kept _ ⟨by omega,Or.inl (by omega)⟩).trans (hread0 j hj)
    have h1 : ∀ j < L, μ' (src1+j) = (w1 j : ℤ) := by
      intro j hj
      exact (kept _ ⟨by omega,Or.inl (by omega)⟩).trans (hread1 j hj)
    have he := OneHotMask.eval_le (m := mask i) hbound0 hbound1
    have heWord : (OneHotMask.eval w0 w1 L (mask i) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr he).trans hvalWord
    have hh := LightOneHot.meets (W := L) (powers := work) (src0 := src0) (src1 := src1)
      (U := U) hhash μ' w0 w1 hw hspace (by omega) (by omega) hword pows h0 h1 hbound0 hbound1
      L (mask i) le_rfl (hmaskLt i hi) (d+1) (by omega)
    light_call hh using hmr,LightOneHot.time with v μ₂ ⟨hv,hmem⟩
    subst μ₂
    light_store (dst+i) (OneHotMask.eval w0 w1 L (mask i) : ℕ) using hv,LightOneHot.time
    refine ⟨by simp,v,Function.update μ' (dst+i) (OneHotMask.eval w0 w1 L (mask i) : ℤ),
      by simp [update_frame_setLocal],?_,?_,?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega)]
        exact written j hj
      · simp
    · intro j hj
      rw [Function.update_of_ne (by omega)]
      exact pows j hj
    · intro a ⟨ha,hout⟩
      rw [Function.update_of_ne (by omega)]
      exact kept a ⟨ha,hout⟩
  · rintro _ _ ⟨r,μ',rfl,written,pows,kept⟩
    exact ⟨written,pows,kept⟩
  · rintro i _ _ _ ⟨r,μ',rfl,_,_,_⟩
    simp

def program : Program := [body 1 2,powTableBody,LightOneHot.body 2]

theorem program_meets
    {μ : ℕ → ℤ} {L masks dst n src0 src1 work U : ℕ}
    (mask w0 w1 : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+1 ≤ lim.depth)
    (hspace : work+(L+1) ≤ lim.space)
    (hmasks : masks+n ≤ dst) (hsrc0 : src0+L ≤ dst) (hsrc1 : src1+L ≤ dst)
    (hdst : dst+n ≤ work)
    (hword : (LightOneHot.word L U : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^L)
    (hread0 : ∀ i < L, μ (src0+i) = (w0 i : ℤ))
    (hread1 : ∀ i < L, μ (src1+i) = (w1 i : ℤ))
    (hbound0 : ∀ i < L, w0 i ≤ U) (hbound1 : ∀ i < L, w1 i ≤ U) :
    Meets lim program 0 d [L,masks,dst,n,src0,src1,work] μ (time L n)
      (fun _ μ' => (∀ i < n, μ' (dst+i) = (OneHotMask.eval w0 w1 L (mask i) : ℤ)) ∧
        Powers μ' work L ∧ KeptBut μ μ' work dst n) :=
  meets rfl rfl rfl mask w0 w1 hw hd hspace hmasks hsrc0 hsrc1 hdst hword
    hmaskRead hmaskLt hread0 hread1 hbound0 hbound1

theorem time_bound (L n : ℕ) : time L n ≤ 300*(L+1)*(n+1) := by
  unfold time powTableTime LightOneHot.time
  nlinarith

end ThreeSum.LightMaskHashes
