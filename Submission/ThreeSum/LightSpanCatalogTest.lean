import Submission.ThreeSum.LightSpanCatalogStep
import Submission.ThreeSum.TernaryOriginalSpanCatalog

/-! Actual coordinate comparisons against every stored span vector. -/
noncomputable section
namespace ThreeSum.LightSpanRowEqual
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000

def flag (f g : ℕ → ℤ) (j : ℕ) : ℕ := if ∀ i<j, f i=g i then 1 else 0

theorem prefix_succ (f g : ℕ → ℤ) (j : ℕ) :
    (∀ i<j+1, f i=g i) ↔ (∀ i<j, f i=g i) ∧ f j=g j := by
  constructor
  · intro h; exact ⟨fun i hi => h i (by omega),h j (by omega)⟩
  · rintro ⟨h,he⟩ i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact h i hi
    · exact he

theorem flag_le_one (f g : ℕ → ℤ) (j : ℕ) : flag f g j≤1 := by unfold flag; split <;> omega

def roundBody : Stmt := .ite (M (v 0 +' v 4) =' M (v 1 +' v 4)) .skip (.set 3 (k 0))
def body : Stmt := .set 3 (k 1) ;; .for 4 (v 2) roundBody ;; .set 0 (v 3)
def time (J : ℕ) : ℕ := 60*J+50

variable {lim : Limits} {P : Program}

theorem meets {pMain a b J d : ℕ} (hmain : P[pMain]?=some body)
    (μ : ℕ → ℤ) (f g : ℕ → ℤ) (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+J≤lim.space) (hb : b+J≤lim.space) (hone : (1 : ℤ)≤lim.word)
    (hf : ∀ i<J, |f i|≤lim.word) (hg : ∀ i<J, |g i|≤lim.word)
    (hreadA : ∀ i<J, μ (a+i)=f i) (hreadB : ∀ i<J, μ (b+i)=g i) :
    Meets lim P pMain d [a,b,J] μ (time J)
      (fun r ν => r=(flag f g J : ℤ) ∧ ν=μ) := by
  apply Meets.of_body hmain
  unfold body time
  light_set 1
  refine Ends.pieceThen (Ends.for (T := 60*J+20)
    (Q := fun σ => σ=⟨frame [a,b,J,flag f g J,J],μ⟩)
    (fun j σ => σ=⟨frame [a,b,J,flag f g j,j],μ⟩) J 40
    ?start ?round ?done ?bound (hT := by light_time)) ?after (hT := by light_time)
  case start => simp [update_frame_setLocal,flag]
  case round =>
    rintro j _ hj _ rfl
    have hReadA := hreadA j hj
    have hReadB := hreadB j hj
    have hF := abs_le.mp (hf j hj)
    have hG := abs_le.mp (hg j hj)
    have hFlag := flag_le_one f g j
    unfold roundBody
    light_if he hne : f j=g j using hReadA,hReadB
    · have hNext : flag f g (j+1)=flag f g j := by simp only [flag,prefix_succ,he,and_true]
      refine Ends.skip ⟨by simp,?_⟩
      simp [update_frame_setLocal,hNext]
    · have hNext : flag f g (j+1)=0 := by simp only [flag,prefix_succ,hne,and_false,if_false]
      light_set 0
      refine ⟨by simp,?_⟩
      simp [update_frame_setLocal,hNext]
  case done => intro σ _ h; exact h
  case bound => rintro j _ hj _ rfl; light_side
  case after =>
    rintro _ rfl
    have hFlag := flag_le_one f g J
    light_set (flag f g J : ℕ)
    exact ⟨by simp,rfl⟩

end ThreeSum.LightSpanRowEqual

namespace ThreeSum.LightSpanCatalogTest
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def Present (f : ℕ → ℕ → ℤ) (row : ℕ → ℤ) (J n : ℕ) : Prop := ∃ k<n, ∀ i<J, f k i=row i

def flag (f : ℕ → ℕ → ℤ) (row : ℕ → ℤ) (J n : ℕ) : ℕ := if Present f row J n then 0 else 1

theorem present_succ (f : ℕ → ℕ → ℤ) (row : ℕ → ℤ) (J n : ℕ) :
    Present f row J (n+1) ↔ Present f row J n ∨ ∀ i<J, f n i=row i := by
  constructor
  · rintro ⟨k,hk,he⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact Or.inl ⟨k,hk,he⟩
    · exact Or.inr he
  · rintro (⟨k,hk,he⟩ | he)
    · exact ⟨k,by omega,he⟩
    · exact ⟨n,by omega,he⟩

theorem flag_le_one (f : ℕ → ℕ → ℤ) (row : ℕ → ℤ) (J n : ℕ) : flag f row J n≤1 := by
  unfold flag; split <;> omega

def roundBody (pEq : ℕ) : Stmt :=
  .call pEq [v 0 +' v 2 *' v 5,v 3,v 2] 6 ;;
  .ite (v 6 =' k 1) (.set 4 (k 0)) .skip

def body (pEq : ℕ) : Stmt := .set 4 (k 1) ;; .for 5 (v 1) (roundBody pEq) ;; .set 0 (v 4)
def time (J n : ℕ) : ℕ := n*(LightSpanRowEqual.time J+150)+100

def Inv (μ : ℕ → ℤ) (catalog n J candidate : ℕ) (f : ℕ → ℕ → ℤ) (row : ℕ → ℤ) (k : ℕ) (σ : State) : Prop :=
  ∃ result : ℤ, σ=⟨frame [catalog,n,J,candidate,flag f row J k,k,result],μ⟩

variable {lim : Limits} {P : Program}

theorem meets {pMain pEq catalog n J candidate d : ℕ}
    (hmain : P[pMain]?=some (body pEq)) (heq : P[pEq]?=some LightSpanRowEqual.body)
    (μ : ℕ → ℤ) (f : ℕ → ℕ → ℤ) (row : ℕ → ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hcat : catalog+J*n≤lim.space) (hrow : candidate+J≤lim.space)
    (hone : (1 : ℤ)≤lim.word) (hcontrols : ((n+J+16 : ℕ) : ℤ)≤lim.word)
    (hf : ∀ k<n, ∀ i<J, |f k i|≤lim.word) (hr : ∀ i<J, |row i|≤lim.word)
    (hread : ∀ k<n, ∀ i<J, μ (catalog+J*k+i)=f k i)
    (hreadRow : ∀ i<J, μ (candidate+i)=row i) (hd : d+1≤lim.depth) :
    Meets lim P pMain d [catalog,n,J,candidate] μ (time J n)
      (fun r ν => r=(flag f row J n : ℤ) ∧ ν=μ) := by
  apply Meets.of_body hmain
  unfold body time
  light_set 1 using LightSpanRowEqual.time
  refine Ends.pieceThen (Ends.for (T := n*(LightSpanRowEqual.time J+150)+20)
    (Q := Inv μ catalog n J candidate f row n) (Inv μ catalog n J candidate f row)
    n (LightSpanRowEqual.time J+100) ?start ?round ?done ?bound (hT := by light_time)) ?after (hT := by light_time)
  case start =>
    refine ⟨0,?_⟩
    simp [update_frame_setLocal,flag,Present]
    change frame [(catalog : ℤ),n,J,candidate,1,0]=frame ([(catalog : ℤ),n,J,candidate,1,0]++[0])
    exact (frame_append_zeros _ 1).symm
  case round =>
    rintro k _ hk _ ⟨result,rfl⟩
    have hkn : J*k+J≤J*n := by
      have hh := Nat.mul_le_mul_left J (show k+1≤n by omega)
      simpa only [Nat.mul_add,Nat.mul_one] using hh
    have hread' : ∀ i<J, μ (catalog+J*k+i)=f k i := hread k hk
    have hc := LightSpanRowEqual.meets (d := d+1) (a := catalog+J*k) heq μ (f k) row hw
      (by omega) hrow hone (hf k hk) hr hread' hreadRow
    have hFlag := flag_le_one f row J k
    unfold roundBody
    light_call hc using LightSpanRowEqual.time
      with out ν ⟨hout,hmem⟩
    subst ν
    have hEqFlag := LightSpanRowEqual.flag_le_one (f k) row J
    light_if he hne : LightSpanRowEqual.flag (f k) row J=1 using hout,LightSpanRowEqual.time
    · have hcurrent : ∀ i<J, f k i=row i := by
        by_contra hh
        simp [LightSpanRowEqual.flag,hh] at he
      have hNext : flag f row J (k+1)=0 := by
        unfold flag
        rw [if_pos ((present_succ f row J k).mpr (Or.inr hcurrent))]
      light_set 0 using LightSpanRowEqual.time
      refine ⟨by simp,out,?_⟩
      simp [update_frame_setLocal,hNext]
    · have hcurrent : ¬∀ i<J, f k i=row i := by
        intro hh
        apply hne
        unfold LightSpanRowEqual.flag
        rw [if_pos hh]
      have hNext : flag f row J (k+1)=flag f row J k := by
        have hp : Present f row J (k+1) ↔ Present f row J k := by
          constructor
          · intro h
            rcases (present_succ f row J k).mp h with h | h
            · exact h
            · exact False.elim (hcurrent h)
          · intro h
            exact (present_succ f row J k).mpr (Or.inl h)
        unfold flag
        rw [hp]
      refine Ends.skip ⟨by simp,out,?_⟩
      simp [update_frame_setLocal,hNext]
  case done => intro σ _ h; exact h
  case bound => rintro k _ hk _ ⟨result,rfl⟩; light_side
  case after =>
    rintro _ ⟨result,rfl⟩
    have hFlag := flag_le_one f row J n
    light_set (flag f row J n : ℕ)
    exact ⟨by simp,rfl⟩

theorem time_bound (J n : ℕ) : time J n≤300*(n+1)*(J+1) := by
  unfold time LightSpanRowEqual.time
  nlinarith

def program : Program := [body 1,LightSpanRowEqual.body]

end ThreeSum.LightSpanCatalogTest
