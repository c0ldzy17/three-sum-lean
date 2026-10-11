import Submission.ThreeSum.LightMaskBits

/-! # Constructing all Boolean coordinate rows for an enumerated mask list -/

namespace ThreeSum.LightMaskBitTable

open Light

set_option maxHeartbeats 1000000

def body (pBits : ℕ) : Stmt :=
  .for 5 (v 3) (.call pBits [v 0,M (v 1 +' v 5),v 2 +' v 5 *' v 0,v 4] 6)

def time (L n : ℕ) : ℕ := n*(LightMaskBits.time L+70)+6

def Inv (μ : ℕ → ℤ) (mask : ℕ → ℕ)
    (L masks dst n work i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [L,masks,dst,n,work,i,r],μ'⟩ ∧
    (∀ j < i, ∀ a < L, μ' (dst+j*L+a) = (LightMaskBits.bit L (mask j) a : ℤ)) ∧
    KeptBut μ μ' work dst (n*L)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain pBits pPowers pErase : ℕ}
    (hmain : P[pMain]? = some (body pBits))
    (hbits : P[pBits]? = some (LightMaskBits.body pPowers pErase))
    (hpowers : P[pPowers]? = some powTableBody)
    (herase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L masks dst n work : ℕ} (mask : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+2 ≤ lim.depth)
    (hspace : work+(L+1) ≤ lim.space)
    (hmasks : masks+n ≤ dst) (hdst : dst+n*L ≤ work)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^L) :
    Meets lim P pMain d [L,masks,dst,n,work] μ (time L n)
      (fun _ μ' =>
        (∀ i < n, ∀ a < L, μ' (dst+i*L+a) = (LightMaskBits.bit L (mask i) a : ℤ)) ∧
        KeptBut μ μ' work dst (n*L)) := by
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ mask L masks dst n work) n (LightMaskBits.time L+62) ?_ ?_ ?_ ?_
  · refine ⟨0,μ,?_,?_,fun _ _ => rfl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : State))
        ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro j hj; omega
  · rintro i _ hi _ ⟨r,μ',rfl,written,kept⟩
    have hmr : μ' (masks+i) = (mask i : ℤ) :=
      (kept _ ⟨by omega,Or.inl (by omega)⟩).trans (hread i hi)
    have himul : (i+1)*L ≤ n*L := Nat.mul_le_mul_right L (by omega)
    have hrowCap : dst+i*L+L ≤ dst+n*L := by nlinarith
    have hrow : dst+i*L+L ≤ work := by nlinarith
    have hmulWord : ((i*L : ℕ) : ℤ) ≤ lim.word := by
      have hh : i*L ≤ lim.space := by omega
      exact (Int.ofNat_le.mpr hh).trans hw
    have haddr : ((dst : ℤ)+(i : ℤ)*L).toNat = dst+i*L := by
      rw [← Nat.cast_mul,← Nat.cast_add,Int.toNat_natCast]
    have hc := LightMaskBits.meets (d := d+1) (μ := μ') (L := L) (m := mask i)
      (dst := dst+i*L) (work := work) hbits hpowers herase hw (by omega)
      hspace hrow hword (hmaskLt i hi)
    light_call hc using hmr,haddr,LightMaskBits.time,LightMaskErase.time
      with v μ₁ ⟨hrowValues,_,hkeep₁⟩
    have hkeepRow : KeptBut μ' μ₁ work (dst+i*L) L := hkeep₁
    refine ⟨by simp,v,μ₁,by simp [update_frame_setLocal],?_,?_⟩
    · intro j hj a ha
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · have hjmul : (j+1)*L ≤ i*L := Nat.mul_le_mul_right L (by omega)
        have hbefore : dst+j*L+a < dst+i*L := by nlinarith
        rw [hkeep₁ _ ⟨by omega,Or.inl hbefore⟩]
        exact written j hj a ha
      · exact hrowValues a ha
    · intro a ⟨ha,hout⟩
      rw [hkeepRow _ ⟨ha,by omega⟩]
      exact kept a ⟨ha,hout⟩
  · rintro _ _ ⟨r,μ',rfl,written,kept⟩
    exact ⟨written,kept⟩
  · rintro i _ _ _ ⟨r,μ',rfl,_,_⟩
    simp

def program : Program := [body 1,LightMaskBits.body 2 3,powTableBody,LightMaskErase.body 3]

end ThreeSum.LightMaskBitTable
