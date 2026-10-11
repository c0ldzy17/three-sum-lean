import Submission.ThreeSumApsp.Lang.Lib.Logs

/-!
# Exact natural quotient by a small counting loop

This helper is used for size parameters whose numerator is logarithmic in
the original input length. Its time is linear in the quotient, explicitly
charged below. A zero divisor returns zero, matching natural division.
-/

namespace ThreeSum.LightSmallDivide

open Light

variable {lim : Limits} {P : Program} {d : ℕ}

def body : Stmt :=
  .ite (k 0 <' v 1)
    (.set 2 (k 0) ;;
      .while ((v 2 +' k 1) *' v 1 ≤' v 0) (.set 2 (v 2 +' k 1)) ;;
      .set 0 (v 2))
    (.set 0 (k 0))

def time (a b : ℕ) : ℕ := 20*(a/b+1)+20

theorem meets {p a b : ℕ} (hp : P[p]? = some body) (μ : ℕ → ℤ)
    (hword : ((a+b+2 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [a,b] μ (time a b)
      (fun r μ' => r = ((a/b : ℕ) : ℤ) ∧ μ' = μ) := by
  have hdiv : a/b ≤ a := Nat.div_le_self a b
  apply Meets.of_body hp
  unfold body time
  refine Ends.iteLast (fun hbZ => ?_) (fun hzeroZ => ?_)
  · have hbp : (0 : ℤ) < (b : ℤ) := by simpa using hbZ
    have hb : 0 < b := by exact_mod_cast hbp
    have hlast : a < (a/b+1)*b := by
      have hmod := Nat.mod_lt a hb
      have hsum := Nat.mod_add_div a b
      nlinarith
    have hprod : ∀ i ≤ a/b, (i+1)*b ≤ a+b := by
      intro i hi
      have hmul := Nat.mul_le_mul_right b hi
      have hh := Nat.div_mul_le_self a b
      nlinarith
    light_set (0 : ℕ)
    refine Ends.next _ (Ends.whileBlock
      (fun i σ => σ = ⟨frame [a,b,i],μ⟩) (a/b) (by simp)
      ?round ?done le_rfl)
    case round =>
      rintro i _ hi rfl
      have hc : (i+1)*b ≤ a := by
        have hmul := Nat.mul_le_mul_right b (show i+1 ≤ a/b by omega)
        exact hmul.trans (Nat.div_mul_le_self a b)
      have hcZ : ((i : ℤ)+1)*(b : ℤ) ≤ (a : ℤ) := by exact_mod_cast hc
      have hnonneg : (0 : ℤ) ≤ ((i : ℤ)+1)*(b : ℤ) := by positivity
      exact ⟨by light_side,by light_side,by light_side,
        by simp [update_frame_setLocal]⟩
    case done =>
      rintro _ rfl
      have hstop : (a : ℤ) < ((a : ℤ)/(b : ℤ)+1)*(b : ℤ) := by exact_mod_cast hlast
      have hfit : (((a/b : ℕ) : ℤ)+1)*(b : ℤ) ≤ (a : ℤ)+(b : ℤ) := by
        exact_mod_cast hprod (a/b) le_rfl
      have hnonneg : (0 : ℤ) ≤ (((a/b : ℕ) : ℤ)+1)*(b : ℤ) := by positivity
      have hqnonneg : (0 : ℤ) ≤ (a : ℤ)/(b : ℤ) := by
        rw [← Int.natCast_ediv]
        exact Int.natCast_nonneg _
      have hfitInt : ((a : ℤ)/(b : ℤ)+1)*(b : ℤ) ≤ (a : ℤ)+(b : ℤ) := by
        exact_mod_cast hprod (a/b) le_rfl
      refine ⟨by light_side,by light_side,?_⟩
      light_set (a/b : ℕ)
      exact ⟨rfl,rfl⟩
  · have hbp : ¬(0 : ℤ) < (b : ℤ) := by simpa using hzeroZ
    have hb : b=0 := by omega
    subst b
    light_set (0 : ℕ)
    exact ⟨by simp,rfl⟩

def program : Program := [body]

theorem program_meets {a b : ℕ} (μ : ℕ → ℤ)
    (hword : ((a+b+2 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim program 0 d [a,b] μ (time a b)
      (fun r μ' => r = ((a/b : ℕ) : ℤ) ∧ μ' = μ) :=
  meets rfl μ hword

theorem time_bound (a b : ℕ) : time a b ≤ 20*a+40 := by
  have h := Nat.div_le_self a b
  unfold time
  omega

end ThreeSum.LightSmallDivide
