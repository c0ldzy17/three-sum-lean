import Submission.ThreeSum.LightResidues
import Mathlib.Data.Nat.Prime.Basic

/-!
# A costed elementary primality test

For `2 ≤ n`, this fixed program tests the integers from 2 through `n-1`
using the verified division-free remainder procedure. The deliberately
elementary running time is suitable for a subpolynomial prime window.
-/

namespace ThreeSum.LightPrimality

open Light LightResidues

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def flag (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | i+1 => if i+2 ∣ n then 0 else flag n i

theorem flag_zero_or_one (n i : ℕ) : flag n i = 0 ∨ flag n i = 1 := by
  induction i with
  | zero => simp [flag]
  | succ i ih =>
      unfold flag
      split
      · exact Or.inl rfl
      · exact ih

theorem flag_le_one (n i : ℕ) : flag n i ≤ 1 := by
  rcases flag_zero_or_one n i with h | h <;> omega

theorem flag_eq_one_iff (n i : ℕ) : flag n i = 1 ↔ ∀ j < i, ¬ j+2 ∣ n := by
  induction i with
  | zero => simp [flag]
  | succ i ih =>
      by_cases hd : i+2 ∣ n
      · simp only [flag,if_pos hd,zero_ne_one,false_iff]
        intro h
        exact h i (by omega) hd
      · rw [flag,if_neg hd,ih]
        constructor
        · intro h j hj
          by_cases hji : j < i
          · exact h j hji
          · have heq : j = i := by omega
            simpa only [heq] using hd
        · intro h j hj
          exact h j (by omega)

theorem prime_iff_flag_eq_one {n : ℕ} (hn : 2 ≤ n) :
    Nat.Prime n ↔ flag n (n-2) = 1 := by
  rw [Nat.prime_def_lt',flag_eq_one_iff]
  constructor
  · intro h j hj
    exact h.2 (j+2) (by omega) (by omega)
  · intro h
    refine ⟨hn,?_⟩
    intro m hm2 hmn
    have hh := h (m-2) (by omega)
    simpa only [Nat.sub_add_cancel hm2] using hh

def answer (n : ℕ) : ℕ := if Nat.Prime n then 1 else 0

theorem flag_eq_answer {n : ℕ} (hn : 2 ≤ n) : flag n (n-2) = answer n := by
  by_cases hp : Nat.Prime n
  · simp [answer,hp,(prime_iff_flag_eq_one hn).mp hp]
  · have hne := mt (prime_iff_flag_eq_one hn).mpr hp
    have hf := flag_zero_or_one n (n-2)
    simp only [answer,if_neg hp]
    omega

/-- Arguments: the integer to test and a scratch pointer. -/
def body (pEmod : ℕ) : Stmt :=
  .set 2 (k 1) ;;
  .for 3 (v 0 -' k 2) (
    .call pEmod [v 0,v 3 +' k 2,v 1] 4 ;;
    .ite (v 4 =' k 0) (.set 2 (k 0)) .skip) ;;
  .set 0 (v 2)

def time (n maxValue : ℕ) : ℕ := (n-2)*(residueBudget maxValue+70)+70

theorem time_le_uniform {n maxValue : ℕ} (hn : n ≤ maxValue) :
    time n maxValue ≤ time maxValue maxValue := by
  unfold time
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hn 2)) _

def Inv (μ : ℕ → ℤ) (n free i : ℕ) (σ : State) : Prop :=
  ∃ (rval : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [(n : ℤ),free,flag n i,i,rval],ν⟩ ∧ Kept μ ν free

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain pEmod : ℕ}
    (hmain : P[pMain]? = some (body pEmod))
    (hem : P[pEmod]? = some emodBody)
    {μ : ℕ → ℤ} {n free maxValue : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hn : 2 ≤ n) (hmax : n ≤ maxValue)
    (hspace : free+(Nat.log 2 (maxValue+1)+2) ≤ lim.space)
    (hword : (8*maxValue+16 : ℕ) ≤ lim.word) :
    Meets lim P pMain d [n,free] μ (time n maxValue)
      (fun r μ' => r = (answer n : ℤ) ∧ Kept μ μ' free) := by
  have hwordZ : (8*(maxValue : ℤ)+16) ≤ lim.word := by exact_mod_cast hword
  have hnWord : (n : ℤ) ≤ lim.word := by omega
  have hrounds : ((n-2 : ℕ) : ℤ) = (n : ℤ)-2 := by omega
  have hx : |(n : ℤ)| ≤ (maxValue : ℤ) := by simpa using Int.ofNat_le.mpr hmax
  apply Meets.of_body hmain
  unfold body time
  light_set 1
  refine Ends.pieceThen (Ends.for (T := (n-2)*(residueBudget maxValue+70)+20)
    (Q := Inv μ n free (n-2)) (Inv μ n free) (n-2) (residueBudget maxValue+50)
    ?_ ?_ ?_ ?_ (hT := by light_time)) ?_
  · refine ⟨0,μ,?_,fun _ _ => rfl⟩
    simp only [flag,update_frame_setLocal]
    exact congrArg (fun loc => (⟨loc,μ⟩ : State)) (frame_append_zeros _ 1).symm
  · rintro i _ hi _ ⟨rval,ν,rfl,hkept⟩
    have hm : i+2 ≤ maxValue := by omega
    have hmWord : ((i+2 : ℕ) : ℤ) ≤ lim.word := by omega
    have hf := flag_le_one n i
    have hpre : Emod.Pre lim (i+2) maxValue free := ⟨by omega,hw,by push_cast; omega,hspace⟩
    have ht := emodTime_le (p := i+2) hx
    simp only [Int.natAbs_natCast] at ht
    unfold emodTime residueBudget at ht
    have hlog : Nat.log 2 (1+maxValue) = Nat.log 2 (maxValue+1) := by rw [Nat.add_comm]
    light_call (emod_meets (d := d+1) (x := (n : ℤ)) hem hpre hx)
      using residueBudget with result ν₁ ⟨hresult,hkeep₁⟩
    subst result
    have hkept₁ : Kept μ ν₁ free := fun j hj => (hkeep₁ j hj).trans (hkept j hj)
    refine Ends.iteLast (fun hdiv => ?_) (fun hnot => ?_) (by light_side)
      (hT := by light_time [residueBudget])
    · have hdiv' : i+2 ∣ n := by
        have hh : (n : ℤ) % ((i+2 : ℕ) : ℤ) = 0 := by simpa using hdiv
        exact Int.natCast_dvd_natCast.mp (Int.dvd_of_emod_eq_zero hh)
      light_set 0 using residueBudget
      refine ⟨by simp,(n : ℤ)%((i+2 : ℕ) : ℤ),ν₁,?_,hkept₁⟩
      simp [flag,hdiv',update_frame_setLocal]
    · have hnot' : ¬ i+2 ∣ n := by
        intro hh
        apply hnot
        have he := Int.emod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mpr hh)
        simpa using he
      apply Ends.skip
      refine ⟨by simp,(n : ℤ)%((i+2 : ℕ) : ℤ),ν₁,?_,hkept₁⟩
      simp [flag,hnot',update_frame_setLocal]
  · intro σ _ hI
    exact hI
  · rintro i _ hi _ ⟨rval,ν,rfl,hkept⟩
    light_side
  · rintro σ ⟨rval,ν,rfl,hkept⟩
    have hf := flag_le_one n (n-2)
    light_set (flag n (n-2))
    exact ⟨by simp [flag_eq_answer hn],hkept⟩

structure Procs (P : Program) (pMain : ℕ) where
  pEmod : ℕ
  main : P[pMain]? = some (body pEmod)
  emod : P[pEmod]? = some emodBody

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {n free maxValue : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hn : 2 ≤ n) (hmax : n ≤ maxValue)
    (hspace : free+(Nat.log 2 (maxValue+1)+2) ≤ lim.space)
    (hword : (8*maxValue+16 : ℕ) ≤ lim.word) :
    Meets lim P pMain d [n,free] μ (time maxValue maxValue)
      (fun r μ' => r = (answer n : ℤ) ∧ Kept μ μ' free) := by
  exact (LightPrimality.meets S.main S.emod hw hd hn hmax hspace hword).mono
    (time_le_uniform hmax) (fun _ _ h => h)

def program : Program := [body 1,emodBody]

def program_procs : Procs program 0 where
  pEmod := 1
  main := rfl
  emod := rfl

theorem program_meets
    {μ : ℕ → ℤ} {n free maxValue : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hn : 2 ≤ n) (hmax : n ≤ maxValue)
    (hspace : free+(Nat.log 2 (maxValue+1)+2) ≤ lim.space)
    (hword : (8*maxValue+16 : ℕ) ≤ lim.word) :
    Meets lim program 0 d [n,free] μ (time maxValue maxValue)
      (fun r μ' => r = (answer n : ℤ) ∧ Kept μ μ' free) :=
  program_procs.meets hw hd hn hmax hspace hword

end ThreeSum.LightPrimality
