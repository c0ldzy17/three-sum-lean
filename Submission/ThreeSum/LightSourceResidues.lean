import Submission.ThreeSum.LightResidues

/-!
# Original-input residue keys with a carry offset

The source histogram uses `(x % p + shift) % m`, with two independently
chosen moduli. This procedure computes both remainders from each original
signed input and retains every incidence, including duplicate values.
-/

namespace ThreeSum.LightSourceResidues

open Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

def key (p m : ℕ) (shift x : ℤ) : ℕ := ((x % (p : ℤ) + shift) % (m : ℤ)).toNat

theorem key_cast {p m : ℕ} (hm : 0 < m) (shift x : ℤ) :
    (key p m shift x : ℤ) = (x % (p : ℤ) + shift) % (m : ℤ) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm.ne'))

theorem key_lt {p m : ℕ} (hm : 0 < m) (shift x : ℤ) : key p m shift x < m := by
  have h := Int.emod_lt_of_pos (x % (p : ℤ) + shift)
    (by exact_mod_cast hm : (0 : ℤ) < m)
  rw [← key_cast hm] at h
  exact_mod_cast h

/-- Arguments: source, destination, count, first modulus, second modulus,
scratch, and signed carry offset. The two remainder calls share scratch. -/
def body (pEmod : ℕ) : Stmt :=
  .for 7 (v 2) (
    .call pEmod [M (v 0 +' v 7),v 3,v 5] 8 ;;
    .call pEmod [v 8 +' v 6,v 4,v 5] 9 ;;
    .store (v 1 +' v 7) (v 9))

def time (n p U D : ℕ) : ℕ :=
  n * (LightResidues.residueBudget U + LightResidues.residueBudget (p+D) + 100) + 6

def word (p m U D : ℕ) : ℕ := 4*U+8*p+4*D+4*m+32

def space (work p U D : ℕ) : ℕ :=
  work + max (Nat.log 2 (U+1)+2) (Nat.log 2 (p+D+1)+2)

def Inv (μ : ℕ → ℤ) (src dst n p m work : ℕ) (shift : ℤ) (i : ℕ)
    (σ : State) : Prop :=
  ∃ (r0 r1 : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [src,dst,n,p,m,work,shift,i,r0,r1],ν⟩ ∧
    (∀ j < i, ν (dst+j) = (key p m shift (μ (src+j)) : ℤ)) ∧
    KeptBut μ ν work dst n

variable {lim : Limits} {P : Program} {d : ℕ}

theorem ends {pEmod : ℕ} (hem : P[pEmod]? = some emodBody)
    {μ : ℕ → ℤ} {src dst n p m work U D : ℕ} {shift : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hp : 0 < p) (hm : 0 < m)
    (hsrc : src+n ≤ work) (hdst : dst+n ≤ work)
    (hspace : space work p U D ≤ lim.space) (hsep : Apart src n dst n)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (word p m U D : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src+i)| ≤ (U : ℤ)) :
    Ends lim P d (body pEmod) ⟨frame [src,dst,n,p,m,work,shift],μ⟩
      (time n p U D) (fun σ =>
        (∀ i < n, σ.mem (dst+i) = (key p m shift (μ (src+i)) : ℤ)) ∧
        KeptBut μ σ.mem work dst n) := by
  have hspace0 : work+(Nat.log 2 (U+1)+2) ≤ lim.space :=
    (Nat.add_le_add_left (le_max_left _ _) work).trans hspace
  have hspace1 : work+(Nat.log 2 (p+D+1)+2) ≤ lim.space :=
    (Nat.add_le_add_left (le_max_right _ _) work).trans hspace
  have hword0 : (4*U+4*p+16 : ℤ) ≤ lim.word := by
    have hb : 4*U+4*p+16 ≤ word p m U D := by unfold word; omega
    exact (by exact_mod_cast hb : (4*U+4*p+16 : ℤ) ≤ (word p m U D : ℤ)).trans hword
  have hword1 : (4*(p+D)+4*m+16 : ℤ) ≤ lim.word := by
    have hb : 4*(p+D)+4*m+16 ≤ word p m U D := by unfold word; omega
    exact (by exact_mod_cast hb : (4*(p+D)+4*m+16 : ℤ) ≤ (word p m U D : ℤ)).trans hword
  have hpre0 : Emod.Pre lim p U work := ⟨hp,hw,hword0,hspace0⟩
  have hpre1 : Emod.Pre lim m (p+D) work := ⟨hm,hw,hword1,hspace1⟩
  have hshift' := abs_le.mp hshift
  unfold body time
  refine Ends.for (Inv μ src dst n p m work shift) n
    (LightResidues.residueBudget U + LightResidues.residueBudget (p+D) + 92)
    ?start ?round ?done ?bound
  case start =>
    refine ⟨0,0,μ,?_,?_,fun _ _ => rfl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : State))
        ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 2).symm)
    · intro j hj
      omega
  case round =>
    rintro i _ hi _ ⟨r0,r1,ν,rfl,written,kept⟩
    have hread : ν (src+i) = μ (src+i) := kept _ ⟨by omega,by omega⟩
    have hx := hvalues i hi
    have hx' := abs_le.mp hx
    have hmod0 : 0 ≤ μ (src+i) % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
    have hmodp : μ (src+i) % (p : ℤ) < (p : ℤ) :=
      Int.emod_lt_of_pos _ (by exact_mod_cast hp)
    have hsum : |μ (src+i) % (p : ℤ) + shift| ≤ ((p+D : ℕ) : ℤ) := by
      rw [Nat.cast_add]
      exact abs_le.mpr ⟨by omega,by omega⟩
    have hsum' := abs_le.mp hsum
    have htime0 := LightResidues.emodTime_le (p := p) hx
    have htime1 := LightResidues.emodTime_le (p := m) hsum
    unfold emodTime LightResidues.residueBudget at htime0 htime1
    have hlog0 : Nat.log 2 (1+U) = Nat.log 2 (U+1) := by rw [Nat.add_comm]
    have hlog1 : Nat.log 2 (1+(p+D)) = Nat.log 2 (p+D+1) := by rw [Nat.add_comm]
    light_call (emod_meets (x := μ (src+i)) hem hpre0 hx)
      using hread,LightResidues.residueBudget with q0 ν₁ ⟨hresult0,hkeep0⟩
    subst q0
    light_call (emod_meets (x := μ (src+i) % (p : ℤ) + shift) hem hpre1 hsum)
      using LightResidues.residueBudget with q1 ν₂ ⟨hresult1,hkeep1⟩
    rw [← key_cast hm] at hresult1
    subst q1
    have hlt := key_lt (p := p) hm shift (μ (src+i))
    light_store (dst+i) (key p m shift (μ (src+i)) : ℕ) using LightResidues.residueBudget
    refine ⟨by simp,μ (src+i) % (p : ℤ),(key p m shift (μ (src+i)) : ℤ),
      Function.update ν₂ (dst+i) (key p m shift (μ (src+i)) : ℕ),
      by simp [update_frame_setLocal],?_,?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega)]
        exact (hkeep1 _ (by omega)).trans ((hkeep0 _ (by omega)).trans (written j hj))
      · simp
    · intro a ⟨ha,hout⟩
      rw [Function.update_of_ne (by omega)]
      exact (hkeep1 a ha).trans ((hkeep0 a ha).trans (kept a ⟨ha,hout⟩))
  case done =>
    rintro _ _ ⟨r0,r1,ν,rfl,written,kept⟩
    exact ⟨written,kept⟩
  case bound =>
    rintro i _ _ _ ⟨r0,r1,ν,rfl,_,_⟩
    simp

theorem meets {pMain pEmod : ℕ}
    (hmain : P[pMain]? = some (body pEmod)) (hem : P[pEmod]? = some emodBody)
    {μ : ℕ → ℤ} {src dst n p m work U D : ℕ} {shift : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hp : 0 < p) (hm : 0 < m) (hsrc : src+n ≤ work) (hdst : dst+n ≤ work)
    (hspace : space work p U D ≤ lim.space) (hsep : Apart src n dst n)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (word p m U D : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src+i)| ≤ (U : ℤ)) :
    Meets lim P pMain d [src,dst,n,p,m,work,shift] μ (time n p U D) (fun _ ν =>
      (∀ i < n, ν (dst+i) = (key p m shift (μ (src+i)) : ℤ)) ∧
      KeptBut μ ν work dst n) := by
  exact Meets.of_body hmain (ends hem hw hd hp hm hsrc hdst hspace hsep hshift hword hvalues)

def program : Program := [body 1,emodBody]

theorem program_meets
    {μ : ℕ → ℤ} {src dst n p m work U D : ℕ} {shift : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hp : 0 < p) (hm : 0 < m) (hsrc : src+n ≤ work) (hdst : dst+n ≤ work)
    (hspace : space work p U D ≤ lim.space) (hsep : Apart src n dst n)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (word p m U D : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src+i)| ≤ (U : ℤ)) :
    Meets lim program 0 d [src,dst,n,p,m,work,shift] μ (time n p U D) (fun _ ν =>
      (∀ i < n, ν (dst+i) = (key p m shift (μ (src+i)) : ℤ)) ∧
      KeptBut μ ν work dst n) := by
  exact meets rfl rfl hw hd hp hm hsrc hdst hspace hsep hshift hword hvalues

theorem time_bound (n p U D : ℕ) :
    time n p U D ≤
      254*n*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+6 := by
  unfold time LightResidues.residueBudget
  nlinarith

end ThreeSum.LightSourceResidues
