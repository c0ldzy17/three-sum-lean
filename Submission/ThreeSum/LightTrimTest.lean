import Submission.ThreeSum.LightArray

/-! # The exact local retained-edge test -/

namespace ThreeSum.LightTrimTest

open Light

def flag (overlap leftCount rightCount cap : ℕ) : ℕ :=
  if overlap=0 ∧ leftCount≤cap ∧ rightCount≤cap then 1 else 0

theorem flag_le (overlap leftCount rightCount cap : ℕ) : flag overlap leftCount rightCount cap ≤ 1 := by
  unfold flag
  split <;> omega

theorem flag_eq_one (overlap leftCount rightCount cap : ℕ) :
    flag overlap leftCount rightCount cap=1 ↔ overlap=0 ∧ leftCount≤cap ∧ rightCount≤cap := by
  unfold flag
  split <;> simp_all

def body : Stmt :=
  .ite (v 0 =' k 0)
    (.ite (v 1 ≤' v 3)
      (.ite (v 2 ≤' v 3) (.set 0 (k 1)) (.set 0 (k 0)))
      (.set 0 (k 0)))
    (.set 0 (k 0))

def time : ℕ := 30

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {p x l r b : ℕ} (hp : P[p]? = some body) (μ : ℕ → ℤ)
    (hword : (1 : ℤ) ≤ lim.word) (hcap : ((b+1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [x,l,r,b] μ time
      (fun v μ' => v=(flag x l r b : ℤ) ∧ μ'=μ) := by
  apply Meets.of_body hp
  unfold body time
  light_if hxZ hnxZ : (x : ℤ)=0
  · have hx : x=0 := by exact_mod_cast hxZ
    light_if hlZ hnlZ : (l : ℤ)≤b
    · have hl : l≤b := by exact_mod_cast hlZ
      light_if hrZ hnrZ : (r : ℤ)≤b
      · have hr : r≤b := by exact_mod_cast hrZ
        light_set 1
        exact ⟨by simp [flag,hx,hl,hr],rfl⟩
      · have hr : ¬r≤b := by exact_mod_cast hnrZ
        light_set 0
        exact ⟨by simp [flag,hx,hl,hr],rfl⟩
    · have hl : ¬l≤b := by exact_mod_cast hnlZ
      light_set 0
      exact ⟨by simp [flag,hx,hl],rfl⟩
  · have hx : x≠0 := by exact_mod_cast hnxZ
    light_set 0
    exact ⟨by simp [flag,hx],rfl⟩

def program : Program := [body]

end ThreeSum.LightTrimTest
