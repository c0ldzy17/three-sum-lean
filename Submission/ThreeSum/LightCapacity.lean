import Submission.ThreeSum.KaratsubaInterface

/-!
# Computing the polynomial capacity in the benchmark language

This is the doubling loop used by the upstream `clog2` procedure, with its
power returned instead of its exponent. The actual machine therefore computes
the requested power-of-two capacity; the capacity is not supplied as advice.
-/

namespace ThreeSum.LightCapacity

open Light ThreeSum.KaratsubaInterface

variable {lim : Limits} {P : Program} {d : ℕ}

def body : Stmt :=
  .set 1 (k 0) ;;
  .set 2 (k 1) ;;
  .while (v 2 <' v 0) (
    .set 2 (v 2 +' v 2) ;;
    .set 1 (v 1 +' k 1)) ;;
  .set 0 (v 2)

def time (p : ℕ) : ℕ := 12 * Nat.clog 2 p + 10

theorem meets {pMain p : ℕ} (hmain : P[pMain]? = some body)
    (μ : ℕ → ℤ) (hp : 0 < p)
    (hword : ((2*p+1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P pMain d [p] μ (time p)
      (fun r μ' => r = (capacity p : ℤ) ∧ μ' = μ) := by
  have hle := le_capacity p
  have hcap : (capacity p : ℤ) ≤ lim.word := by
    have hh : capacity p ≤ 2*p+1 := by have := capacity_lt_twice hp; omega
    have hhZ : (capacity p : ℤ) ≤ ((2*p+1 : ℕ) : ℤ) := by exact_mod_cast hh
    exact hhZ.trans hword
  unfold capacity at hle hcap ⊢
  refine Meets.of_body hmain ?_
  unfold body time
  light_set 0
  light_set 1
  refine Ends.next _ (Ends.whileBlock
    (fun i σ => σ = ⟨frame [p, i, (2^i : ℕ)], μ⟩)
    (Nat.clog 2 p) (by simp) ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    have hlt : 2^i < p := (Nat.lt_clog_iff_pow_lt (by norm_num)).1 hi
    have hip : i < p := lt_trans (Nat.lt_pow_self (by norm_num)) hlt
    rw [show 2^(i+1) = 2^i + 2^i by ring]
    generalize 2^i = q at hlt
    exact ⟨by light_side, by light_side, by light_side,
      by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    generalize 2^Nat.clog 2 p = q at hle hcap ⊢
    refine ⟨by light_side, by light_side, ?_⟩
    light_set (q : ℕ)
    exact ⟨rfl, rfl⟩

def program : Program := [body]

theorem program_meets {p : ℕ} (μ : ℕ → ℤ) (hp : 0 < p)
    (hword : ((2*p+1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim program 0 d [p] μ (time p)
      (fun r μ' => r = (capacity p : ℤ) ∧ μ' = μ) :=
  meets rfl μ hp hword

end ThreeSum.LightCapacity
