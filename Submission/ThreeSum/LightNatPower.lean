import Submission.ThreeSumApsp.Lang.Lib.Logs

/-!
# Scalar integer powers in the benchmark language

The exponent is a size parameter, so a loop of that many multiplications
has polynomial-logarithmic cost in the applications below. No power table
or auxiliary memory is required.
-/

namespace ThreeSum.LightNatPower

open Light

variable {lim : Limits} {P : Program} {d : ℕ}

def body : Stmt :=
  .set 2 (k 1) ;;
  .for 3 (v 1) (.set 2 (v 2 *' v 0)) ;;
  .set 0 (v 2)

def time (e : ℕ) : ℕ := 20*e+20

theorem meets {p b e : ℕ} (hp : P[p]? = some body) (μ : ℕ → ℤ)
    (he : (e : ℤ) ≤ lim.word)
    (hpow : ∀ i ≤ e, ((b^i : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [b,e] μ (time e)
      (fun r μ' => r = ((b^e : ℕ) : ℤ) ∧ μ' = μ) := by
  have h1 : (1 : ℤ) ≤ lim.word := by simpa using hpow 0 (Nat.zero_le _)
  apply Meets.of_body hp
  unfold body time
  light_set (1 : ℕ)
  refine Ends.pieceThen (Ends.for (T := 14*e+6)
    (Q := fun σ => σ = ⟨frame [b,e,(b^e : ℕ),e],μ⟩)
    (fun i σ => σ = ⟨frame [b,e,(b^i : ℕ),i],μ⟩) e 4
    ?start ?round ?done ?bound (hT := by light_time)) ?after
  case start =>
    simp [update_frame_setLocal]
  case round =>
    rintro i _ hi _ rfl
    have hfit : (b : ℤ)^(i+1) ≤ lim.word := by exact_mod_cast hpow (i+1) (by omega)
    have hnonneg : (0 : ℤ) ≤ (b : ℤ)^(i+1) := by positivity
    have hmul : (b : ℤ)^i*(b : ℤ) = (b : ℤ)^(i+1) := (pow_succ _ _).symm
    refine Ends.setLast ?_ (hs := by light_side [hmul]) (hT := by light_time)
    simp [update_frame_setLocal,pow_succ]
  case done =>
    intro σ _ hI
    exact hI
  case bound =>
    rintro i _ hi _ rfl
    light_side
  case after =>
    rintro _ rfl
    have hfit := hpow e le_rfl
    light_set (b^e : ℕ)
    exact ⟨rfl,rfl⟩

theorem bounded_meets {p b e : ℕ} (hp : P[p]? = some body) (μ : ℕ → ℤ)
    (he : (e : ℤ) ≤ lim.word)
    (hword : (((b+1)^(e+1) : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [b,e] μ (time e)
      (fun r μ' => r = ((b^e : ℕ) : ℤ) ∧ μ' = μ) := by
  apply meets hp μ he
  intro i hi
  have hbase := Nat.pow_le_pow_left (show b ≤ b+1 by omega) i
  have hexp : (b+1)^i ≤ (b+1)^(e+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hz : ((b^i : ℕ) : ℤ) ≤ (((b+1)^(e+1) : ℕ) : ℤ) := by
    exact_mod_cast hbase.trans hexp
  exact hz.trans hword

def program : Program := [body]

theorem program_meets {b e : ℕ} (μ : ℕ → ℤ)
    (he : (e : ℤ) ≤ lim.word)
    (hpow : ∀ i ≤ e, ((b^i : ℕ) : ℤ) ≤ lim.word) :
    Meets lim program 0 d [b,e] μ (time e)
      (fun r μ' => r = ((b^e : ℕ) : ℤ) ∧ μ' = μ) :=
  meets rfl μ he hpow

end ThreeSum.LightNatPower
