import Submission.ThreeSum.LightTernaryRank

/-! Actual canonical query digits and all-active Euler flags. -/
namespace ThreeSum.LightTernaryNearDigits
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryCodeSemantics

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def roundBody (pDigit : ℕ) : Stmt :=
  .set 6 (k 2 *' (v 0 -' k 1 -' v 5)) ;;
  .set 7 (v 6 +' k 1) ;;
  .call pDigit [k 2 *' v 0,v 6,v 7,v 1,v 2] 8 ;;
  .store (v 3 +' v 5) (v 8) ;;
  .store (v 4 +' v 5) (k 1)

def body (pDigit : ℕ) : Stmt := .for 5 (v 0) (roundBody pDigit)
def time (N : ℕ) : ℕ := N*(LightTernaryCodes.digitTime (2*N)+200)+20

def Inv (μ : ℕ → ℤ) (N m powers caps active j : ℕ) (σ : State) : Prop :=
  ∃ lo hi dig : ℤ, ∃ ν : ℕ → ℤ,
    σ=⟨frame [N,m,powers,caps,active,j,lo,hi,dig],ν⟩ ∧
    SameOutside μ ν caps (active+N-caps) ∧
    (∀ i<j, ν (caps+i)=(LightTernaryRank.digitAt N m i : ℤ)) ∧
    (∀ i<j, ν (active+i)=1)

variable {lim : Limits} {P : Program}

theorem meets {pMain pDigit pErase N m powers caps active d : ℕ}
    (hmain : P[pMain]?=some (body pDigit))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (μ : ℕ → ℤ) (hw : (lim.space : ℤ)≤lim.word)
    (hspace : powers+(2*N+1)≤lim.space)
    (hword : ((2^(2*N+1) : ℕ) : ℤ)≤lim.word)
    (hm : m<2^(2*N)) (hcaps : caps+N≤active) (hactive : active+N≤powers)
    (hpowers : Powers μ powers (2*N)) (hd : d+2*N+2≤lim.depth) :
    Meets lim P pMain d [N,m,powers,caps,active] μ (time N)
      (fun _ ν => (∀ i<N, ν (caps+i)=(LightTernaryRank.digitAt N m i : ℤ)) ∧
        (∀ i<N, ν (active+i)=1) ∧ SameOutside μ ν caps (active+N-caps)) := by
  have hcapLe : caps≤active+N := by omega
  have hspan : caps+(active+N-caps)=active+N := Nat.add_sub_of_le hcapLe
  have htwoword : (2 : ℤ)≤lim.word := by omega
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ N m powers caps active) N (LightTernaryCodes.digitTime (2*N)+180)
    ?start ?round ?done ?bound (hT := by light_time)
  case start =>
    refine ⟨0,0,0,μ,?_,SameOn.refl,?_,?_⟩
    · simp [update_frame_setLocal]
      change frame [(N : ℤ),m,powers,caps,active,0]=
        frame ([(N : ℤ),m,powers,caps,active,0]++[0,0,0])
      exact (frame_append_zeros _ 3).symm
    all_goals intro i hi; omega
  case round =>
    rintro j _ hj _ ⟨lo,hi,dig,ν,rfl,H,hcapsRead,hactiveRead⟩
    have hPowers : Powers ν powers (2*N) := by
      intro i hi
      rw [H _ (Or.inr (by omega))]
      exact hpowers i hi
    have hl : 2*(N-1-j)≤2*N := by omega
    have hh : 2*(N-1-j)+1≤2*N := by omega
    have hlo : 2*((N : ℤ)-1-(j : ℤ))=((2*(N-1-j) : ℕ) : ℤ) := by omega
    have hdigitBound := LightTernaryCodes.digit_le_two (2*N) (2*(N-1-j)) (2*(N-1-j)+1) m
    have hdigitEq : LightTernaryCodes.digit (2*N) (2*(N-1-j)) (2*(N-1-j)+1) m=
      LightTernaryRank.digitAt N m j := rfl
    have hc := LightTernaryCodes.digit_meets (d := d+1) hdigit herase ν hw hspace hword hPowers hl hh hm (by omega) htwoword
    unfold roundBody
    light_set (2*(N-1-j) : ℕ) using hlo,LightTernaryCodes.digitTime
    light_set (2*(N-1-j)+1 : ℕ) using LightTernaryCodes.digitTime
    light_call hc using LightTernaryCodes.digitTime
      with r ξ ⟨hr,hmem⟩
    subst ξ
    light_store (caps+j) (LightTernaryRank.digitAt N m j : ℕ) using hr,hdigitEq,LightTernaryCodes.digitTime
    light_store (active+j) (1 : ℕ) using LightTernaryCodes.digitTime
    refine ⟨by simp,(2*(N-1-j) : ℕ),(2*(N-1-j)+1 : ℕ),r,
      Function.update (Function.update ν (caps+j) (LightTernaryRank.digitAt N m j : ℤ)) (active+j) 1,?_,?_,?_,?_⟩
    · simp [update_frame_setLocal]
    · intro x hx
      simp only [Function.update_of_ne (by omega : x≠active+j),Function.update_of_ne (by omega : x≠caps+j)]
      exact H x hx
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | he
      · rw [Function.update_of_ne (by omega : caps+i≠active+j),Function.update_of_ne (by omega : caps+i≠caps+j)]
        exact hcapsRead i hi
      · subst i
        simp [Function.update_of_ne (by omega : caps+j≠active+j)]
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | he
      · rw [Function.update_of_ne (by omega : active+i≠active+j),Function.update_of_ne (by omega : active+i≠caps+j)]
        exact hactiveRead i hi
      · subst i
        simp
  case done =>
    rintro _ _ ⟨lo,hi,dig,ν,rfl,H,hcapsRead,hactiveRead⟩
    exact ⟨hcapsRead,hactiveRead,H⟩
  case bound =>
    rintro j _ hj _ ⟨lo,hi,dig,ν,rfl,H,hcapsRead,hactiveRead⟩
    light_side

end ThreeSum.LightTernaryNearDigits
