import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Dense integer Karatsuba multiplication

This file implements a dense, low-coefficient-first list algorithm. Its
correctness theorem is an equality of integer polynomials. The instrumented
work model counts list traversal and scalar arithmetic primitives; it is a
separate obligation to compile this implementation to `Light` and prove the
benchmark's word-RAM step and word-size bounds.
-/

namespace ThreeSum.Karatsuba

open Polynomial

/-- Low-degree-first coefficient semantics, retaining padding zeros. -/
noncomputable def asPolynomial : List ℤ → Polynomial ℤ
  | [] => 0
  | a :: as => C a + X * asPolynomial as

/-- Linear dense addition; unequal inputs are implicitly padded by zeros. -/
def plus : List ℤ → List ℤ → List ℤ
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a + b) :: plus as bs

def negate (as : List ℤ) : List ℤ := as.map (fun a => -a)
def minus (as bs : List ℤ) : List ℤ := plus as (negate bs)
def shift (n : ℕ) (as : List ℤ) : List ℤ := List.replicate n 0 ++ as

@[simp] theorem length_plus (as bs : List ℤ) :
    (plus as bs).length = max as.length bs.length := by
  induction as generalizing bs with
  | nil => simp [plus]
  | cons a as ih =>
    cases bs with
    | nil => simp [plus]
    | cons b bs => simpa [plus, Nat.succ_max_succ] using congrArg Nat.succ (ih bs)

@[simp] theorem length_negate (as : List ℤ) : (negate as).length = as.length := by
  simp [negate]

@[simp] theorem length_minus (as bs : List ℤ) :
    (minus as bs).length = max as.length bs.length := by
  simp [minus]

@[simp] theorem length_shift (n : ℕ) (as : List ℤ) :
    (shift n as).length = n + as.length := by
  simp [shift]

@[simp] theorem asPolynomial_plus (as bs : List ℤ) :
    asPolynomial (plus as bs) = asPolynomial as + asPolynomial bs := by
  induction as generalizing bs with
  | nil => simp [plus, asPolynomial]
  | cons a as ih =>
    cases bs with
    | nil => simp [plus, asPolynomial]
    | cons b bs =>
      simp only [plus, asPolynomial, ih, map_add]
      ring

@[simp] theorem asPolynomial_negate (as : List ℤ) :
    asPolynomial (negate as) = -asPolynomial as := by
  induction as with
  | nil => simp [negate, asPolynomial]
  | cons a as ih =>
    simp only [negate, List.map_cons, asPolynomial, map_neg]
    change -C a + X * asPolynomial (negate as) = _
    rw [ih]
    ring

@[simp] theorem asPolynomial_minus (as bs : List ℤ) :
    asPolynomial (minus as bs) = asPolynomial as - asPolynomial bs := by
  simp [minus, sub_eq_add_neg]

@[simp] theorem asPolynomial_shift (n : ℕ) (as : List ℤ) :
    asPolynomial (shift n as) = X ^ n * asPolynomial as := by
  induction n with
  | zero => simp [shift]
  | succ n ih =>
    simp only [shift, List.replicate_succ, List.cons_append, asPolynomial, map_zero,
      zero_add]
    change X * asPolynomial (shift n as) = _
    rw [ih, pow_succ]
    ring

/-- Splitting at a coefficient boundary is exact, also for padded short lists. -/
theorem asPolynomial_split (n : ℕ) (as : List ℤ) :
    asPolynomial as = asPolynomial (as.take n) + X ^ n * asPolynomial (as.drop n) := by
  induction n generalizing as with
  | zero => simp [asPolynomial]
  | succ n ih =>
    cases as with
    | nil => simp [asPolynomial]
    | cons a as =>
      simp only [List.take_succ_cons, List.drop_succ_cons, asPolynomial, pow_succ]
      rw [ih as]
      ring

theorem asPolynomial_head {as : List ℤ} (h : as.length ≤ 1) :
    asPolynomial as = C (as.headD 0) := by
  cases as with
  | nil => simp [asPolynomial]
  | cons a as =>
    have hz : as.length = 0 := by simpa using h
    have he : as = [] := List.length_eq_zero_iff.mp hz
    subst as
    simp [asPolynomial]

/-- Karatsuba multiplication at a fixed power-of-two capacity. Both input
lists must have length at most `2^k` for the correctness theorem. -/
def multiply : ℕ → List ℤ → List ℤ → List ℤ
  | 0, as, bs => [as.headD 0 * bs.headD 0]
  | k + 1, as, bs =>
    let n := 2 ^ k
    let a0 := as.take n
    let a1 := as.drop n
    let b0 := bs.take n
    let b1 := bs.drop n
    let z0 := multiply k a0 b0
    let z2 := multiply k a1 b1
    let z1 := minus (minus (multiply k (plus a0 a1) (plus b0 b1)) z0) z2
    plus z0 (shift n (plus z1 (shift n z2)))

theorem length_multiply (k : ℕ) (as bs : List ℤ) :
    (multiply k as bs).length ≤ 2 * 2 ^ k := by
  induction k generalizing as bs with
  | zero => simp [multiply]
  | succ k ih =>
    simp only [multiply, length_plus, length_shift, length_minus, pow_succ]
    have h0 := ih (as.take (2 ^ k)) (bs.take (2 ^ k))
    have h2 := ih (as.drop (2 ^ k)) (bs.drop (2 ^ k))
    have h1 := ih (plus (as.take (2 ^ k)) (as.drop (2 ^ k)))
      (plus (bs.take (2 ^ k)) (bs.drop (2 ^ k)))
    omega

/-- All coefficients of the computed product are correct. -/
theorem multiply_correct (k : ℕ) (as bs : List ℤ)
    (ha : as.length ≤ 2 ^ k) (hb : bs.length ≤ 2 ^ k) :
    asPolynomial (multiply k as bs) = asPolynomial as * asPolynomial bs := by
  induction k generalizing as bs with
  | zero =>
    simp only [pow_zero] at ha hb
    simp only [multiply, asPolynomial, mul_zero, add_zero]
    rw [asPolynomial_head ha, asPolynomial_head hb, map_mul]
  | succ k ih =>
    have ha0 : (as.take (2 ^ k)).length ≤ 2 ^ k := by simp
    have hb0 : (bs.take (2 ^ k)).length ≤ 2 ^ k := by simp
    have ha1 : (as.drop (2 ^ k)).length ≤ 2 ^ k := by
      simp only [List.length_drop]
      simp only [pow_succ] at ha
      omega
    have hb1 : (bs.drop (2 ^ k)).length ≤ 2 ^ k := by
      simp only [List.length_drop]
      simp only [pow_succ] at hb
      omega
    have hap : (plus (as.take (2 ^ k)) (as.drop (2 ^ k))).length ≤ 2 ^ k := by
      simpa using max_le ha0 ha1
    have hbp : (plus (bs.take (2 ^ k)) (bs.drop (2 ^ k))).length ≤ 2 ^ k := by
      simpa using max_le hb0 hb1
    simp only [multiply, asPolynomial_plus, asPolynomial_shift, asPolynomial_minus]
    rw [ih _ _ ha0 hb0, ih _ _ ha1 hb1, ih _ _ hap hbp,
      asPolynomial_plus, asPolynomial_plus]
    conv_rhs => rw [asPolynomial_split (2 ^ k) as, asPolynomial_split (2 ^ k) bs]
    ring

/-- The algorithm's output has the ordinary convolution coefficient at
every index, not merely the same value at a selected evaluation point. -/
theorem coefficient_correct (k : ℕ) (as bs : List ℤ)
    (ha : as.length ≤ 2 ^ k) (hb : bs.length ≤ 2 ^ k) (j : ℕ) :
    (asPolynomial (multiply k as bs)).coeff j =
      ∑ p ∈ Finset.antidiagonal j,
        (asPolynomial as).coeff p.1 * (asPolynomial bs).coeff p.2 := by
  rw [multiply_correct k as bs ha hb, Polynomial.coeff_mul]

/-! ## Explicit traversal/arithmetic work model

The following charges reflect the operations in the executable list code:
two units per matched coefficient of `plus`; two per mapped coefficient of
`negate`; two per generated/concatenated zero of `shift`; and the two scans
used by `take` and `drop`. The fixed per-call charges include list tests.
They are a conventional unit-cost list/arithmetic model, **not** a theorem
about the benchmark machine or Lean's runtime system.

The recursive charge below uses the actual intermediate list sizes. The
uniform three-subcall recurrence is proved from those sizes; it is not an
assumption that the desired multiplication bound already holds.
-/

def plusWork (as bs : List ℤ) : ℕ := 2 * min as.length bs.length + 1
def negateWork (as : List ℤ) : ℕ := 2 * as.length + 1
def minusWork (as bs : List ℤ) : ℕ := negateWork bs + plusWork as (negate bs) + 1
def shiftWork (n : ℕ) : ℕ := 2 * n + 1
def splitWork (n : ℕ) (as : List ℤ) : ℕ := 2 * min n as.length + 2

/-- The nonrecursive charge for one exact Karatsuba node. -/
def nodeWork (k : ℕ) (as bs : List ℤ) : ℕ :=
  let n := 2 ^ k
  let a0 := as.take n
  let a1 := as.drop n
  let b0 := bs.take n
  let b1 := bs.drop n
  let z0 := multiply k a0 b0
  let z2 := multiply k a1 b1
  let p := multiply k (plus a0 a1) (plus b0 b1)
  let q := minus p z0
  let z1 := minus q z2
  splitWork n as + splitWork n bs + plusWork a0 a1 + plusWork b0 b1 +
    minusWork p z0 + minusWork q z2 + shiftWork n + plusWork z1 (shift n z2) +
    shiftWork n + plusWork z0 (shift n (plus z1 (shift n z2))) + 2 * k + 20

/-- Work of the recursion with the same three recursive operands as the
algorithm. Computing this audit function is not part of the multiplier. -/
def multiplyWork : ℕ → List ℤ → List ℤ → ℕ
  | 0, _, _ => 3
  | k + 1, as, bs =>
    let n := 2 ^ k
    multiplyWork k (as.take n) (bs.take n) +
      multiplyWork k (as.drop n) (bs.drop n) +
      multiplyWork k (plus (as.take n) (as.drop n))
        (plus (bs.take n) (bs.drop n)) + nodeWork k as bs

theorem plusWork_le_left (as bs : List ℤ) : plusWork as bs ≤ 2 * as.length + 1 := by
  unfold plusWork
  omega

theorem nodeWork_le (k : ℕ) (as bs : List ℤ) : nodeWork k as bs ≤ 80 * 2 ^ k := by
  have h0 := length_multiply k (as.take (2 ^ k)) (bs.take (2 ^ k))
  have h2 := length_multiply k (as.drop (2 ^ k)) (bs.drop (2 ^ k))
  have h1 := length_multiply k (plus (as.take (2 ^ k)) (as.drop (2 ^ k)))
    (plus (bs.take (2 ^ k)) (bs.drop (2 ^ k)))
  have hpow : k < 2 ^ k := Nat.lt_two_pow_self
  have hn : 0 < (2 : ℕ) ^ k := pow_pos (by decide) _
  have hat : (as.take (2 ^ k)).length ≤ 2 ^ k := by simp
  have hbt : (bs.take (2 ^ k)).length ≤ 2 ^ k := by simp
  simp only [nodeWork, splitWork, plusWork, minusWork, negateWork, shiftWork,
    length_negate, length_minus, length_shift, length_plus]
  omega

/-- Solving the actual operand-dependent recurrence, uniformly in both lists. -/
theorem multiplyWork_bound (k : ℕ) (as bs : List ℤ) :
    multiplyWork k as bs + 80 * 2 ^ k ≤ 83 * 3 ^ k := by
  induction k generalizing as bs with
  | zero => simp [multiplyWork]
  | succ k ih =>
    have h0 := ih (as.take (2 ^ k)) (bs.take (2 ^ k))
    have h2 := ih (as.drop (2 ^ k)) (bs.drop (2 ^ k))
    have h1 := ih (plus (as.take (2 ^ k)) (as.drop (2 ^ k)))
      (plus (bs.take (2 ^ k)) (bs.drop (2 ^ k)))
    have hw := nodeWork_le k as bs
    simp only [multiplyWork, pow_succ]
    omega

theorem multiplyWork_le (k : ℕ) (as bs : List ℤ) :
    multiplyWork k as bs ≤ 83 * 3 ^ k := by
  have h := multiplyWork_bound k as bs
  omega

/-- A log-free `O(N^(8/5))` certificate at capacity `N=2^k`.
This uses `3^5 < 2^8`, not floating-point logarithms. -/
theorem multiplyWork_fifth_power (k : ℕ) (as bs : List ℤ) :
    multiplyWork k as bs ^ 5 ≤ 83 ^ 5 * (2 ^ k) ^ 8 := by
  have hw := Nat.pow_le_pow_left (multiplyWork_le k as bs) 5
  have hbase : (3 : ℕ) ^ 5 ≤ 2 ^ 8 := by norm_num
  have hp := Nat.pow_le_pow_left hbase k
  have hp' : (3 ^ k) ^ 5 ≤ (2 ^ k) ^ 8 := by
    simpa only [← pow_mul, Nat.mul_comm] using hp
  calc
    multiplyWork k as bs ^ 5 ≤ (83 * 3 ^ k) ^ 5 := hw
    _ = 83 ^ 5 * (3 ^ k) ^ 5 := by rw [mul_pow]
    _ ≤ 83 ^ 5 * (2 ^ k) ^ 8 := Nat.mul_le_mul_left _ hp'

end ThreeSum.Karatsuba
