import Submission.ThreeSum.TernaryCodeSemantics

/-! # Actual rank computation from a canonical compressed address -/

namespace ThreeSum.LightTernaryRank

open Light Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.LightSubsetAddress

def digitAt (N m i : ℕ) : ℕ := LightTernaryCodes.digit (2*N)
  (2*(N-1-i)) (2*(N-1-i)+1) m

def partialRank (N m j : ℕ) : ℕ := ∑ i ∈ range j, digitAt N m i

theorem partialRank_succ (N m j : ℕ) :
    partialRank N m (j+1)=partialRank N m j+digitAt N m j := sum_range_succ _ _

theorem partialRank_le (N m j : ℕ) : partialRank N m j ≤ 2*j := by
  unfold partialRank
  calc
    _ ≤ ∑ _i ∈ range j, 2 := by
      apply sum_le_sum
      intro i hi
      exact LightTernaryCodes.digit_le_two _ _ _ _
    _ = 2*j := by simp; omega

theorem partialRank_address {N : ℕ} (w : TritWord N) : partialRank N (address w) N=rank w := by
  unfold partialRank rank
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i hi
  exact digit_eq w i

def roundBody (pDigit : ℕ) : Stmt :=
  .set 5 (k 2 *' (v 0 -' k 1 -' v 4)) ;;
  .call pDigit [k 2 *' v 0,v 5,v 5 +' k 1,v 1,v 2] 6 ;;
  .set 3 (v 3 +' v 6)

def body (pDigit : ℕ) : Stmt :=
  .set 3 (k 0) ;; .for 4 (v 0) (roundBody pDigit) ;; .set 0 (v 3)

def time (N : ℕ) : ℕ := N*(LightTernaryCodes.digitTime (2*N)+150)+100

def Inv (N m powers : ℕ) (μ : ℕ → ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ lo res : ℤ, σ=⟨frame [N,m,powers,partialRank N m j,j,lo,res],μ⟩

variable {lim : Limits} {P : Program}

theorem meets {pMain pDigit pErase N m powers d : ℕ}
    (hmain : P[pMain]?=some (body pDigit))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(2*N+1) ≤ lim.space)
    (hword : ((2^(2*N+1) : ℕ) : ℤ) ≤ lim.word)
    (hscalar : ((2*N+16 : ℕ) : ℤ) ≤ lim.word)
    (hpowers : Powers μ powers (2*N)) (hm : m < 2^(2*N))
    (hdepth : d+2*N+2 ≤ lim.depth) :
    Meets lim P pMain d [N,m,powers] μ (time N)
      (fun r ν => r=(partialRank N m N : ℤ) ∧ ν=μ) := by
  have hnword : (N : ℤ) ≤ lim.word := by omega
  have htwoword : (2 : ℤ) ≤ lim.word := by omega
  apply Meets.of_body hmain
  unfold body time
  light_set 0
  refine Ends.pieceThen (Ends.for (T := N*(LightTernaryCodes.digitTime (2*N)+140)+20)
    (Q := Inv N m powers μ N) (Inv N m powers μ) N
    (LightTernaryCodes.digitTime (2*N)+120) ?_ ?_ ?_ ?_ (hT := by light_time)) ?_
  · refine ⟨0,0,?_⟩
    simp only [partialRank,sum_range_zero,update_frame_setLocal]
    change State.mk (frame [(N : ℤ),m,powers,0,0]) μ =
      State.mk (frame ([(N : ℤ),m,powers,0,0] ++ List.replicate 2 0)) μ
    exact congrArg (fun loc => State.mk loc μ)
      (frame_append_zeros [(N : ℤ),m,powers,0,0] 2).symm
  · rintro j _ hj _ ⟨lo,res,rfl⟩
    let lowJ := 2*(N-1-j)
    have hlo : lowJ < 2*N := by dsimp [lowJ]; omega
    have hhi : lowJ+1 < 2*N := by dsimp [lowJ]; omega
    have hlowWord : (lowJ : ℤ) ≤ lim.word := by omega
    have hhighWord : ((lowJ+1 : ℕ) : ℤ) ≤ lim.word := by omega
    have hcast : 2*((N : ℤ)-1-(j : ℤ))=(lowJ : ℤ) := by dsimp [lowJ]; omega
    have hcall := LightTernaryCodes.digit_meets (d := d+1) hdigit herase μ hw
      hspace hword hpowers (Nat.le_of_lt hlo) (Nat.le_of_lt hhi) hm (by omega) htwoword
    have hsum := partialRank_le N m (j+1)
    have hsumWord : ((partialRank N m (j+1) : ℕ) : ℤ) ≤ lim.word := by omega
    have hsumCast : (partialRank N m j : ℤ)+(digitAt N m j : ℤ)=(partialRank N m (j+1) : ℤ) := by
      rw [partialRank_succ,Nat.cast_add]
    unfold roundBody
    light_set lowJ using hcast
    light_call hcall using hcast,LightTernaryCodes.digitTime
      with result ν ⟨hr,hmem⟩
    subst ν
    have hres : result=(digitAt N m j : ℤ) := by simpa [digitAt,lowJ] using hr
    light_set (partialRank N m (j+1) : ℕ) using hres,hsumCast
    constructor
    · simp [update_frame_setLocal]
    · refine ⟨lowJ,result,?_⟩
      simp [Inv,update_frame_setLocal,Nat.cast_add]
  · intro σ hc hI
    exact hI
  · rintro j _ hj _ ⟨lo,res,rfl⟩
    light_side
  · rintro σ ⟨lo,res,rfl⟩
    have hsum := partialRank_le N m N
    have hsumWord : (partialRank N m N : ℤ) ≤ lim.word := by omega
    light_set (partialRank N m N : ℕ)
    exact ⟨rfl,rfl⟩

def program : Program :=
  [body 1,LightTernaryCodes.digitBody 2,LightMaskErase.body 2]

theorem program_meets {N m powers d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(2*N+1) ≤ lim.space)
    (hword : ((2^(2*N+1) : ℕ) : ℤ) ≤ lim.word)
    (hscalar : ((2*N+16 : ℕ) : ℤ) ≤ lim.word)
    (hpowers : Powers μ powers (2*N)) (hm : m < 2^(2*N))
    (hdepth : d+2*N+2 ≤ lim.depth) :
    Meets lim program 0 d [N,m,powers] μ (time N)
      (fun r ν => r=(partialRank N m N : ℤ) ∧ ν=μ) :=
  meets rfl rfl rfl μ hw hspace hword hscalar hpowers hm hdepth

end ThreeSum.LightTernaryRank
