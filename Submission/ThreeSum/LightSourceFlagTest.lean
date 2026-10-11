import Submission.ThreeSum.LightArray

/-! # Independent cardinality-and-bucket trimming test -/

namespace ThreeSum.LightSourceFlagTest

open Light

def flag (card required count cap : ℕ) : ℕ :=
  if card=required ∧ count≤cap then 1 else 0

theorem flag_le (card required count cap : ℕ) : flag card required count cap ≤ 1 := by
  unfold flag
  split <;> omega

theorem flag_eq_one (card required count cap : ℕ) :
    flag card required count cap=1 ↔ card=required ∧ count≤cap := by
  unfold flag
  split <;> simp_all

def body : Stmt :=
  .ite (v 0 =' v 1)
    (.ite (v 2 ≤' v 3) (.set 0 (k 1)) (.set 0 (k 0)))
    (.set 0 (k 0))

def time : ℕ := 25

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {p card required count cap : ℕ} (hp : P[p]? = some body) (μ : ℕ → ℤ)
    (hword : ((card+required+count+cap+2 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [card,required,count,cap] μ time
      (fun r ν => r = (flag card required count cap : ℤ) ∧ ν=μ) := by
  apply Meets.of_body hp
  unfold body time
  light_if hc hn : (card : ℤ)=(required : ℤ)
  · have he : card=required := by exact_mod_cast hc
    light_if ht hnt : (count : ℤ)≤(cap : ℤ)
    · have hle : count≤cap := by exact_mod_cast ht
      light_set 1
      exact ⟨by simp [flag,he,hle],rfl⟩
    · have hle : ¬count≤cap := by exact_mod_cast hnt
      light_set 0
      exact ⟨by simp [flag,he,hle],rfl⟩
  · have he : card≠required := by exact_mod_cast hn
    light_set 0
    exact ⟨by simp [flag,he],rfl⟩

def program : Program := [body]

end ThreeSum.LightSourceFlagTest
