import Submission.ThreeSum.LightTernaryBankCoordinate

/-! Actual ascending coordinate sweep, retaining every compact bank stage. -/
namespace ThreeSum.LightTernaryBankSweep
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}

def roundBody (pCoord : ℕ) : Stmt :=
  .call pCoord [v 0,k 2 *' (v 0 -' (v 7 +' k 1)),k 2 *' (v 0 -' (v 7 +' k 1)) +' k 1,
    v 1,v 2,v 3,v 4,v 5,v 6 +' v 7 *' v 2,v 6 +' (v 7 +' k 1) *' v 2] 8

def body (pCoord : ℕ) : Stmt := .for 7 (v 0) (roundBody pCoord)

def time (N L n : ℕ) : ℕ :=N*(LightTernaryBankCoordinate.time N L n+100)+100

def Preserved (μ μ' : ℕ→ℤ) (keyBase n base N : ℕ) : Prop :=
  ∀ x, (x<keyBase ∨ keyBase+4*n≤x) → (x<base+n ∨ base+(N+1)*n≤x) → μ' x=μ x

def Stages {N T n : ℕ} (E : Enumeration N T n) (φ : ℕ→TritWord N→ℤ)
    (base : ℕ) (k : ℕ) (μ : ℕ→ℤ) : Prop :=
  ∀ s≤k, ∀ j<n, μ (base+s*n+j)=φ s (E.word j)

def Inv {N T n : ℕ} (E : Enumeration N T n) (φ : ℕ→TritWord N→ℤ)
    (μ : ℕ→ℤ) (a powers L keyBase base : ℕ) (k : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ→ℤ), σ=⟨frame [N,a,n,powers,L,keyBase,base,k,r],μ'⟩ ∧
    Stages E φ base k μ' ∧ Preserved μ μ' keyBase n base N ∧
    Powers μ' powers (2*N)

/-- Generic loop rule; its coordinate premise is instantiated by the real
metadata/pass routine in the concrete zeta and inverse sweep theorems. -/
theorem meets_core {N T n pMain pCoord a powers L keyBase base d : ℕ}
    (hmain : P[pMain]?=some (body pCoord))
    (E : Enumeration N T n) (φ : ℕ→TritWord N→ℤ) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+n≤keyBase) (hmeta : keyBase+4*n≤powers)
    (hpows : powers+(2*N+1)≤base) (hspace : base+(N+1)*n≤lim.space)
    (hNword : 2*(N : ℤ)+3≤lim.word) (hL : L≤2*N)
    (hcodes : ∀ j<n, μ (a+j)=(address (E.word j) : ℤ))
    (hsource : ∀ j<n, μ (base+j)=φ 0 (E.word j))
    (hpowers : Powers μ powers (2*N))
    (hd : d+1≤lim.depth)
    (hcoord : ∀ k (hk : k<N), ∀ μ' : ℕ→ℤ,
      (∀ j<n, μ' (a+j)=(address (E.word j) : ℤ)) → Powers μ' powers (2*N) →
      (∀ j<n, μ' (base+k*n+j)=φ k (E.word j)) →
      Meets lim P pCoord (d+1)
        [N,low (⟨k,hk⟩ : Fin N),high (⟨k,hk⟩ : Fin N),a,n,powers,L,keyBase,
          base+k*n,base+(k+1)*n] μ' (LightTernaryBankCoordinate.time N L n)
        (fun _ μ'' => (∀ j<n, μ'' (base+(k+1)*n+j)=φ (k+1) (E.word j)) ∧
          LightTernaryBankCoordinate.Preserved μ' μ'' keyBase n (base+(k+1)*n))) :
    Meets lim P pMain d [N,a,n,powers,L,keyBase,base] μ (time N L n)
      (fun _ μ' => Stages E φ base N μ' ∧ Preserved μ μ' keyBase n base N ∧ Powers μ' powers (2*N)) := by
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv E φ μ a powers L keyBase base) N
    (LightTernaryBankCoordinate.time N L n+80) ?start ?round ?done ?bound (hT := by light_time)
  case start =>
    refine ⟨0,μ,?_,?_,?_,hpowers⟩
    · simp only [update_frame_setLocal]
      congr 1
      simp only [setLocal, List.length_cons, List.length_nil, List.set_cons_succ, List.set_nil, List.replicate_zero, List.append_nil]
      change frame [(N : ℤ),a,n,powers,L,keyBase,base,0]=
        frame ([(N : ℤ),a,n,powers,L,keyBase,base,0]++[0])
      exact (frame_append_zeros _ 1).symm
    · intro s hs j hj
      have hz : s=0 := by omega
      subst s
      simpa using hsource j hj
    · intro x _ _
      rfl
  case round =>
    rintro k _ hk _ ⟨r,μ',rfl,hstages,hkeep,hp⟩
    have hcm : ∀ j<n, μ' (a+j)=(address (E.word j) : ℤ) := by
      intro j hj
      exact (hkeep _ (Or.inl (by omega)) (Or.inl (by omega))).trans (hcodes j hj)
    have hc := hcoord k hk μ' hcm hp (hstages k le_rfl)
    have hlow := low_step hk
    have hhigh := high_step hk
    have hsub : (N : ℤ)-((k : ℤ)+1)=((N-(k+1) : ℕ) : ℤ) := by omega
    have hnext : base+(k+1)*n+n≤base+(N+1)*n := by
      have hm := Nat.mul_le_mul_right n (show k+2≤N+1 by omega)
      rw [Nat.add_mul] at hm
      nlinarith
    have hsrcWord : ((base+k*n : ℕ) : ℤ)≤lim.word := by
      have hm := Nat.mul_le_mul_right n (show k≤N+1 by omega)
      exact (Int.ofNat_le.mpr (show base+k*n≤lim.space by omega)).trans hw
    have hdstWord : ((base+(k+1)*n : ℕ) : ℤ)≤lim.word := by
      have hm := Nat.mul_le_mul_right n (show k+1≤N+1 by omega)
      exact (Int.ofNat_le.mpr (show base+(k+1)*n≤lim.space by omega)).trans hw
    have hmulWord : (k : ℤ)*(n : ℤ)≤lim.word := by
      have hm := Nat.mul_le_mul_right n (show k≤N+1 by omega)
      exact (by exact_mod_cast (show k*n≤lim.space by omega) : (k : ℤ)*(n : ℤ)≤(lim.space : ℤ)).trans hw
    have hmulNextWord : ((k : ℤ)+1)*(n : ℤ)≤lim.word := by
      have hm := Nat.mul_le_mul_right n (show k+1≤N+1 by omega)
      exact (by exact_mod_cast (show (k+1)*n≤lim.space by omega) : ((k : ℤ)+1)*(n : ℤ)≤(lim.space : ℤ)).trans hw
    have hdstWord' : (base : ℤ)+((k : ℤ)+1)*(n : ℤ)≤lim.word := by
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one] using hdstWord
    have hmulNextNonneg : 0≤((k : ℤ)+1)*(n : ℤ) := mul_nonneg (by omega) (by omega)
    unfold roundBody
    light_call hc using hlow,hhigh,hsub,LightTernaryBankCoordinate.time with out μ'' ⟨hout,hcoordKeep⟩
    refine ⟨by simp,out,μ'',?_,?_,?_,?_⟩
    · simp [Inv,update_frame_setLocal]
    · intro s hs j hj
      by_cases he : s=k+1
      · subst s
        exact hout j hj
      · have hsk : s≤k := by omega
        have hm := Nat.mul_le_mul_right n hsk
        have hpres := hcoordKeep (base+s*n+j) (Or.inr (by omega)) (Or.inl (by
          rw [Nat.succ_mul]
          omega))
        exact hpres.trans (hstages s hsk j hj)
    · intro x hxMeta hxStages
      have hxOut : x<base+(k+1)*n ∨ base+(k+1)*n+n≤x := by
        rcases hxStages with hx|hx
        · left
          rw [Nat.succ_mul]
          omega
        · right
          omega
      exact (hcoordKeep x hxMeta hxOut).trans (hkeep x hxMeta hxStages)
    · intro j hj
      exact (hcoordKeep (powers+j) (Or.inr (by omega)) (Or.inl (by
        rw [Nat.succ_mul]
        omega))).trans (hp j hj)
  case done =>
    rintro _ _ ⟨r,μ',rfl,hstages,hkeep,hp⟩
    exact ⟨hstages,hkeep,hp⟩
  case bound =>
    rintro k _ hk _ ⟨r,μ',rfl,hstages,hkeep,hp⟩
    light_side

end ThreeSum.LightTernaryBankSweep
