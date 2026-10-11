import Submission.ThreeSum.BlockSourceEncoding

/-!
# Residue-indexed source lookup and independent trimming

Each endpoint is reduced by the global modulus and its original-input
histogram count is gathered. The already constructed independent endpoint
flag selects that count or zero. No search through the original inputs is
performed for individual subset masks.
-/

namespace ThreeSum.LightSourceGather

open Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

def value (m : ℕ) (endpoint : ℕ → ℤ) (flag hist : ℕ → ℕ) (i : ℕ) : ℕ :=
  if flag i = 1 then hist (LightResidues.residue m 1 (endpoint i)) else 0

theorem value_le {m B : ℕ} (hm : 0 < m) (endpoint : ℕ → ℤ) (flag hist : ℕ → ℕ)
    (hhist : ∀ r < m, hist r ≤ B) (i : ℕ) : value m endpoint flag hist i ≤ B := by
  unfold value
  split
  · exact hhist _ (LightResidues.residue_lt hm 1 _)
  · omega

/-- Arguments: raw endpoints, independent flags, source histogram, output,
number of masks, global modulus, and reusable remainder scratch. -/
def body (pEmod : ℕ) : Stmt :=
  .for 7 (v 4) (
    .call pEmod [M (v 0 +' v 7),v 5,v 6] 8 ;;
    .ite (M (v 1 +' v 7) =' k 1)
      (.store (v 3 +' v 7) (M (v 2 +' v 8)))
      (.store (v 3 +' v 7) (k 0)))

def time (n U : ℕ) : ℕ := n*(LightResidues.residueBudget U+80)+6

def Inv (μ : ℕ → ℤ) (raw flags table dst n m work : ℕ)
    (endpoint : ℕ → ℤ) (flag hist : ℕ → ℕ) (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ), σ = ⟨frame [raw,flags,table,dst,n,m,work,i,r],ν⟩ ∧
    (∀ j < i, ν (dst+j) = (value m endpoint flag hist j : ℤ)) ∧
    KeptBut μ ν work dst n

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain pEmod : ℕ}
    (hmain : P[pMain]? = some (body pEmod)) (hem : P[pEmod]? = some emodBody)
    {μ : ℕ → ℤ} {raw flags table dst n m work U B : ℕ}
    (endpoint : ℕ → ℤ) (flag hist : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hm : 0 < m)
    (hraw : raw+n ≤ dst) (hflags : flags+n ≤ dst) (htable : table+m ≤ dst)
    (hdst : dst+n ≤ work) (hspace : work+(Nat.log 2 (U+1)+2) ≤ lim.space)
    (hword : (4*U+4*m+16 : ℤ) ≤ lim.word) (hcountWord : (B : ℤ) ≤ lim.word)
    (hrawRead : ∀ i < n, μ (raw+i) = endpoint i)
    (hrawBound : ∀ i < n, |endpoint i| ≤ (U : ℤ))
    (hflagRead : ∀ i < n, μ (flags+i) = (flag i : ℤ))
    (hflagBound : ∀ i < n, flag i ≤ 1)
    (hhistRead : ∀ r < m, μ (table+r) = (hist r : ℤ))
    (hhistBound : ∀ r < m, hist r ≤ B) :
    Meets lim P pMain d [raw,flags,table,dst,n,m,work] μ (time n U)
      (fun _ ν => (∀ i < n, ν (dst+i) = (value m endpoint flag hist i : ℤ)) ∧
        KeptBut μ ν work dst n) := by
  have hpre : Emod.Pre lim m U work := ⟨hm,hw,hword,hspace⟩
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ raw flags table dst n m work endpoint flag hist) n
    (LightResidues.residueBudget U+72) ?start ?round ?done ?bound
  case start =>
    refine ⟨0,μ,?_,?_,fun _ _ => rfl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : State))
        ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro j hj; omega
  case round =>
    rintro i _ hi _ ⟨r,ν,rfl,written,kept⟩
    have hread : ν (raw+i) = endpoint i :=
      (kept _ ⟨by omega,Or.inl (by omega)⟩).trans (hrawRead i hi)
    have hx := hrawBound i hi
    have hx' := abs_le.mp hx
    have hbudget := LightResidues.emodTime_le (p := m) hx
    unfold emodTime LightResidues.residueBudget at hbudget
    have hlog : Nat.log 2 (1+U) = Nat.log 2 (U+1) := by rw [Nat.add_comm]
    light_call (emod_meets (x := endpoint i) hem hpre hx)
      using hread,LightResidues.residueBudget with q ν₁ ⟨hresult,hkeep⟩
    have hcast := LightResidues.residue_cast hm 1 (endpoint i)
    simp only [one_mul] at hcast
    rw [← hcast] at hresult
    subst q
    have hkeyLt := LightResidues.residue_lt hm 1 (endpoint i)
    have hflag : ν₁ (flags+i) = (flag i : ℤ) :=
      (hkeep _ (by omega)).trans
        ((kept _ ⟨by omega,Or.inl (by omega)⟩).trans (hflagRead i hi))
    have hflagB := hflagBound i hi
    have hhist : ν₁ (table+LightResidues.residue m 1 (endpoint i)) =
        (hist (LightResidues.residue m 1 (endpoint i)) : ℤ) :=
      (hkeep _ (by omega)).trans
        ((kept _ ⟨by omega,Or.inl (by omega)⟩).trans (hhistRead _ hkeyLt))
    have hvalue : (hist (LightResidues.residue m 1 (endpoint i)) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (hhistBound _ hkeyLt)).trans hcountWord
    light_if hy hn : (flag i : ℤ)=1 using hflag,LightResidues.residueBudget
    · have he : flag i=1 := by exact_mod_cast hy
      light_store (dst+i) (hist (LightResidues.residue m 1 (endpoint i)) : ℕ)
        using hhist,LightResidues.residueBudget
      refine ⟨by simp,(LightResidues.residue m 1 (endpoint i) : ℤ),
        Function.update ν₁ (dst+i) (hist (LightResidues.residue m 1 (endpoint i)) : ℕ),
        by simp [update_frame_setLocal],?_,?_⟩
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · rw [Function.update_of_ne (by omega)]
          exact (hkeep _ (by omega)).trans (written j hj)
        · simp [value,he]
      · intro a ⟨ha,hout⟩
        rw [Function.update_of_ne (by omega)]
        exact (hkeep a ha).trans (kept a ⟨ha,hout⟩)
    · have he : flag i≠1 := by exact_mod_cast hn
      light_store (dst+i) (0 : ℕ) using LightResidues.residueBudget
      refine ⟨by simp,(LightResidues.residue m 1 (endpoint i) : ℤ),
        Function.update ν₁ (dst+i) 0,by simp [update_frame_setLocal],?_,?_⟩
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · rw [Function.update_of_ne (by omega)]
          exact (hkeep _ (by omega)).trans (written j hj)
        · simp [value,he]
      · intro a ⟨ha,hout⟩
        rw [Function.update_of_ne (by omega)]
        exact (hkeep a ha).trans (kept a ⟨ha,hout⟩)
  case done =>
    rintro _ _ ⟨r,ν,rfl,written,kept⟩
    exact ⟨written,kept⟩
  case bound =>
    rintro i _ _ _ ⟨r,ν,rfl,_,_⟩
    simp

def program : Program := [body 1,emodBody]

theorem program_meets
    {μ : ℕ → ℤ} {raw flags table dst n m work U B : ℕ}
    (endpoint : ℕ → ℤ) (flag hist : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hm : 0 < m)
    (hraw : raw+n ≤ dst) (hflags : flags+n ≤ dst) (htable : table+m ≤ dst)
    (hdst : dst+n ≤ work) (hspace : work+(Nat.log 2 (U+1)+2) ≤ lim.space)
    (hword : (4*U+4*m+16 : ℤ) ≤ lim.word) (hcountWord : (B : ℤ) ≤ lim.word)
    (hrawRead : ∀ i < n, μ (raw+i) = endpoint i)
    (hrawBound : ∀ i < n, |endpoint i| ≤ (U : ℤ))
    (hflagRead : ∀ i < n, μ (flags+i) = (flag i : ℤ))
    (hflagBound : ∀ i < n, flag i ≤ 1)
    (hhistRead : ∀ r < m, μ (table+r) = (hist r : ℤ))
    (hhistBound : ∀ r < m, hist r ≤ B) :
    Meets lim program 0 d [raw,flags,table,dst,n,m,work] μ (time n U)
      (fun _ ν => (∀ i < n, ν (dst+i) = (value m endpoint flag hist i : ℤ)) ∧
        KeptBut μ ν work dst n) := by
  exact meets rfl rfl endpoint flag hist hw hd hm hraw hflags htable hdst hspace
    hword hcountWord hrawRead hrawBound hflagRead hflagBound hhistRead hhistBound

theorem time_bound (n U : ℕ) : time n U ≤ 157*n*(Nat.log 2 (U+1)+1)+6 := by
  unfold time LightResidues.residueBudget
  nlinarith

end ThreeSum.LightSourceGather
