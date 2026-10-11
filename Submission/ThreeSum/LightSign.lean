import Submission.ThreeSum.LightArray

/-! # Exact alternating signs by a bounded coordinate-count loop -/

namespace ThreeSum.LightSign

open Light

variable {lim : Limits} {P : Program}

/-- Arguments: signed value and a nonnegative exponent. -/
def body : Stmt := .for 2 (v 1) (.set 0 (k 0 -' v 0))

def time (e : ℕ) : ℕ := 20*e+20

def Inv (μ : ℕ → ℤ) (x : ℤ) (e j : ℕ) (σ : State) : Prop :=
  σ = ⟨frame [(-1 : ℤ)^j*x,e,j],μ⟩

theorem meets {pMain e d : ℕ} {x : ℤ} {μ : ℕ → ℤ}
    (hmain : P[pMain]? = some body)
    (hw : (lim.space : ℤ) ≤ lim.word) (he : e ≤ lim.space)
    (hvalue : |x| ≤ lim.word) :
    Meets lim P pMain d [x,e] μ (time e)
      (fun r μ' => r = (-1 : ℤ)^e*x ∧ μ' = μ) := by
  have hb (j : ℕ) : |(-1 : ℤ)^j*x| ≤ lim.word := by
    simpa only [abs_mul,abs_neg_one_pow,one_mul] using hvalue
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ x e) e 10 ?start ?round ?done ?bound (hT := by light_time)
  case start =>
    simp [Inv,update_frame_setLocal]
  case round =>
    rintro j _ hj _ rfl
    have hnext := abs_le.mp (hb (j+1))
    have htoggle : (0 : ℤ)-((-1 : ℤ)^j*x) = (-1 : ℤ)^(j+1)*x := by
      rw [pow_succ]
      ring
    light_set ((-1 : ℤ)^(j+1)*x) using htoggle
    constructor
    · simp
    · simp [Inv,update_frame_setLocal]
  case done =>
    rintro _ _ rfl
    exact ⟨by simp,rfl⟩
  case bound =>
    rintro j _ hj _ rfl
    light_side

def program : Program := [body]

theorem program_meets {e d : ℕ} {x : ℤ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (he : e ≤ lim.space)
    (hvalue : |x| ≤ lim.word) :
    Meets lim program 0 d [x,e] μ (time e)
      (fun r μ' => r = (-1 : ℤ)^e*x ∧ μ' = μ) :=
  meets rfl hw he hvalue

end ThreeSum.LightSign
