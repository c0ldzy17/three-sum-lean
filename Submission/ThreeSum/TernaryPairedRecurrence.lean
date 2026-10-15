import Mathlib.Tactic

/-! Exact division-free iteration of the selected paired and collision
contraction bounds. Integer positivity forces the final paired score to zero
once its proved upper bound falls below one. -/

namespace ThreeSum.TernaryPairedRecurrence

theorem iterate_bound (a b : ℕ) (score : ℕ → ℕ)
    (hstep : ∀ j, a*score (j+1) ≤ b*score j) (r : ℕ) :
    a^r*score r ≤ b^r*score 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
    calc
      _ = a^r*(a*score (r+1)) := by rw [pow_succ]; ring
      _ ≤ a^r*(b*score r) := Nat.mul_le_mul_left _ (hstep r)
      _ = b*(a^r*score r) := by ring
      _ ≤ b*(b^r*score 0) := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [pow_succ]; ring

theorem zero_of_iterated_bound (a b : ℕ) (score : ℕ → ℕ)
    (hstep : ∀ j, a*score (j+1) ≤ b*score j) (r : ℕ)
    (hsmall : b^r*score 0 < a^r) : score r=0 := by
  have hh := iterate_bound a b score hstep r
  by_contra hn
  have hp : 1 ≤ score r := Nat.pos_of_ne_zero hn
  have hm := Nat.mul_le_mul_left (a^r) hp
  simp only [mul_one] at hm
  omega

theorem weighted_iteration (a b c : ℕ) (ha : 0<a) (score : ℕ → ℕ)
    (hstep : ∀ j, a*score (j+1)≤b*score j) (hbudget : b*c≤a) (r : ℕ) :
    c^r*score r≤score 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
    apply Nat.le_of_mul_le_mul_left (c := a) ?_ ha
    calc
      _ = c^r*c*(a*score (r+1)) := by rw [pow_succ]; ring
      _ ≤ c^r*c*(b*score r) := Nat.mul_le_mul_left _ (hstep r)
      _ = (b*c)*(c^r*score r) := by ring
      _ ≤ a*(c^r*score r) := Nat.mul_le_mul_right _ hbudget
      _ ≤ _ := Nat.mul_le_mul_left _ ih

/-- A fixed strict oversize margin pays the initial `n^(2K+1)` score,
all carries, and every logarithmic minor factor. -/
theorem paired_fourth_power_bound (K M a b : ℕ) (ha : 0<a) (score : ℕ → ℕ)
    (hstep : ∀ j, a*score (j+1)≤b*score j)
    (hbudget : b^4*M^(4*K+3)≤a^4) (r : ℕ) :
    M^(r*(4*K+3))*(score r)^4≤(score 0)^4 := by
  have hs (j : ℕ) : a^4*(score (j+1))^4≤b^4*(score j)^4 := by
    simpa only [mul_pow] using Nat.pow_le_pow_left (hstep j) 4
  have hh := weighted_iteration (a^4) (b^4) (M^(4*K+3)) (pow_pos ha 4)
    (fun j => (score j)^4) hs hbudget r
  simpa only [←pow_mul,mul_comm (4*K+3) r] using hh

theorem paired_zero_of_initial_budget (K M a b n C : ℕ) (ha : 0<a)
    (score : ℕ → ℕ) (hstep : ∀ j, a*score (j+1)≤b*score j)
    (hbudget : b^4*M^(4*K+3)≤a^4) (r : ℕ)
    (hcover : n^2≤M^r) (hinit : (score 0)^4≤C*n^(8*K+5)) (hn : C<n) :
    score r=0 := by
  have hnpos : 0<n := by omega
  have hbound := paired_fourth_power_bound K M a b ha score hstep hbudget r
  have hbase : n^(8*K+6)≤M^(r*(4*K+3)) := by
    have hh := Nat.pow_le_pow_left hcover (4*K+3)
    simpa only [←pow_mul,show 2*(4*K+3)=8*K+6 by ring] using hh
  have hstrict : C*n^(8*K+5)<n^(8*K+6) := by
    have hh := Nat.mul_lt_mul_of_pos_right hn (pow_pos hnpos (8*K+5))
    convert hh using 1 <;> rw [show 8*K+6=(8*K+5)+1 by omega,pow_succ] <;> ring
  by_contra hz
  have hp : 1≤(score r)^4 := Nat.one_le_pow 4 (score r) (Nat.pos_of_ne_zero hz)
  have hm := Nat.mul_le_mul_left (M^(r*(4*K+3))) hp
  simp only [mul_one] at hm
  omega

/-- The physical query tensor may carry a positive common factorial
scale at each prefix. Integer cross multiplication removes both scales. -/
theorem scaled_step_iff (a b old next sOld sNext : ℕ)
    (hOld : 0<sOld) (hNext : 0<sNext) :
    a*sOld*(sNext*next)≤b*sNext*(sOld*old) ↔ a*next≤b*old := by
  have heL : a*sOld*(sNext*next)=(sOld*sNext)*(a*next) := by ring
  have heR : b*sNext*(sOld*old)=(sOld*sNext)*(b*old) := by ring
  rw [heL,heR]
  constructor
  · intro h
    exact Nat.le_of_mul_le_mul_left h (Nat.mul_pos hOld hNext)
  · intro h
    exact Nat.mul_le_mul_left _ h

end ThreeSum.TernaryPairedRecurrence
