import Submission.ThreeSum.LightKaratsuba
import Mathlib.Data.Nat.Log

/-!
# Arbitrary-length interface for the verified multiplication routine

These exact inequalities convert a requested positive coefficient length
to its power-of-two capacity. Polynomial padding preserves the represented
product. The fifth-power bounds include any fixed linear preparation and
folding overhead, so no real-exponent oracle is needed for the time bound.
-/

namespace ThreeSum.KaratsubaInterface

open ThreeSum.Karatsuba ThreeSum.LightKaratsuba Polynomial

def capacity (p : ℕ) : ℕ := 2 ^ Nat.clog 2 p

theorem le_capacity (p : ℕ) : p ≤ capacity p := Nat.le_pow_clog (by decide) p

theorem capacity_lt_twice {p : ℕ} (hp : 0 < p) : capacity p < 2 * p := by
  by_cases h1 : p = 1
  · subst p
    norm_num [capacity]
  have hp1 : 1 < p := by omega
  have hk : 0 < Nat.clog 2 p := Nat.clog_pos (by decide) hp1
  have hpred := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hp1
  rw [Nat.pred_eq_sub_one] at hpred
  calc
    capacity p = 2 * 2 ^ (Nat.clog 2 p - 1) := by
      unfold capacity
      conv_lhs =>
        rw [show Nat.clog 2 p = (Nat.clog 2 p - 1) + 1 by omega, pow_succ]
      rw [Nat.mul_comm]
    _ < 2 * p := Nat.mul_lt_mul_of_pos_left hpred (by decide)

theorem capacity_pos (p : ℕ) : 0 < capacity p := Nat.pow_pos (by decide)

theorem time_with_linear_bound (k c : ℕ) :
    time k + c * 2 ^ k + c ≤ (2530 + 2 * c) * 3 ^ k := by
  have ht := time_le k
  have hn : (2 : ℕ) ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by decide) k
  have hmc := Nat.mul_le_mul_left c hn
  have hc := Nat.mul_le_mul_left c (Nat.one_le_pow k 3 (by decide))
  nlinarith

theorem time_with_linear_fifth_power (k c : ℕ) :
    (time k + c * 2 ^ k + c) ^ 5 ≤ (2530 + 2 * c) ^ 5 * (2 ^ k) ^ 8 := by
  have ht := Nat.pow_le_pow_left (time_with_linear_bound k c) 5
  have hp := Nat.pow_le_pow_left (show (3 : ℕ) ^ 5 ≤ 2 ^ 8 by norm_num) k
  calc
    _ ≤ ((2530 + 2 * c) * 3 ^ k) ^ 5 := ht
    _ = (2530 + 2 * c) ^ 5 * (3 ^ 5) ^ k := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm k 5, pow_mul]
    _ ≤ (2530 + 2 * c) ^ 5 * (2 ^ 8) ^ k := Nat.mul_le_mul_left _ hp
    _ = _ := by rw [← pow_mul, Nat.mul_comm 8 k, pow_mul]

/-- The exact exponent certificate for length `p`: time to the fifth power
is bounded by a fixed constant times `p^8`, including linear overhead. -/
theorem rounded_time_fifth_power {p : ℕ} (hp : 0 < p) (c : ℕ) :
    (time (Nat.clog 2 p) + c * capacity p + c) ^ 5 ≤
      ((2530 + 2 * c) ^ 5 * 2 ^ 8) * p ^ 8 := by
  have ht := time_with_linear_fifth_power (Nat.clog 2 p) c
  have hn := Nat.pow_le_pow_left (capacity_lt_twice hp).le 8
  calc
    _ ≤ (2530 + 2 * c) ^ 5 * capacity p ^ 8 := ht
    _ ≤ (2530 + 2 * c) ^ 5 * (2 * p) ^ 8 := Nat.mul_le_mul_left _ hn
    _ = _ := by rw [mul_pow, mul_assoc]

theorem rounded_word_bound {p : ℕ} (hp : 0 < p) (U : ℕ) :
    wordBound (capacity p) U ≤ 1024 * p ^ 3 * (U + 1) ^ 2 := by
  have hn := Nat.pow_le_pow_left (capacity_lt_twice hp).le 3
  unfold wordBound
  calc
    _ ≤ 128 * (2 * p) ^ 3 * (U + 1) ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hn)
    _ = _ := by ring

def pad (n : ℕ) (as : List ℤ) : List ℤ := as ++ List.replicate (n - as.length) 0

theorem pad_length {n : ℕ} {as : List ℤ} (ha : as.length ≤ n) : (pad n as).length = n := by
  simp only [pad, List.length_append, List.length_replicate]
  omega

theorem polynomial_append (as bs : List ℤ) :
    asPolynomial (as ++ bs) = asPolynomial as + X ^ as.length * asPolynomial bs := by
  induction as with
  | nil => simp [asPolynomial]
  | cons a as ih =>
    simp only [List.cons_append, asPolynomial, List.length_cons, ih, pow_succ]
    ring

theorem polynomial_replicate_zero (n : ℕ) : asPolynomial (List.replicate n (0 : ℤ)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, asPolynomial, map_zero, ih, mul_zero, add_zero]

theorem polynomial_pad (n : ℕ) (as : List ℤ) : asPolynomial (pad n as) = asPolynomial as := by
  rw [pad, polynomial_append, polynomial_replicate_zero, mul_zero, add_zero]

theorem pad_bound {n : ℕ} {as : List ℤ} {U : ℤ} (hA : CoeffBound as U) :
    CoeffBound (pad n as) U := by
  intro j
  rw [← asPolynomial_coeff, polynomial_pad, asPolynomial_coeff]
  exact hA j

end ThreeSum.KaratsubaInterface
