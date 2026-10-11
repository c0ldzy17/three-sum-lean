import Submission.ThreeSum.Arithmetic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.List.MinMax
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring

/-! # Exact deterministic contraction of the weighted modular score -/

namespace ThreeSum.PrimeChain

open Finset
open scoped BigOperators

variable {ι : Type*}

def score (T : Finset ι) (difference : ι → ℤ) (weight : ℤ → ℕ) (q : ℕ) : ℕ :=
  ∑ i ∈ T, if q ∣ (difference i).natAbs then weight (difference i) else 0

theorem score_eq_weightedFalseCount (T : Finset ι) (difference : ι → ℤ)
    (L : Finset ℤ) (q : ℕ) :
    score T difference (Arithmetic.missWeight L) q =
      Arithmetic.weightedFalseCount T difference L (q : ℤ) := by
  simp only [score, Arithmetic.weightedFalseCount, Int.natCast_dvd]

/-- A nonzero integer cannot have too many distinct prime divisors above y. -/
theorem prime_divisors_card_le_log (C : Finset ℕ) (y : ℕ) (hy : 1 < y)
    (hprime : ∀ p ∈ C, Nat.Prime p) (hmin : ∀ p ∈ C, y ≤ p)
    (z : ℤ) (hz : z ≠ 0) :
    (C.filter fun p => p ∣ z.natAbs).card ≤ Nat.log y z.natAbs := by
  let hits := C.filter fun p => p ∣ z.natAbs
  have hcop : (hits : Set ℕ).Pairwise (fun p q => IsRelPrime p q) := by
    intro p hp q hq hne
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hprime p (mem_filter.mp hp).1)
        (hprime q (mem_filter.mp hq).1)).mpr hne)
  have hdiv : (∏ p ∈ hits, p) ∣ z.natAbs :=
    prod_dvd_of_isRelPrime hcop (fun p hp => (mem_filter.mp hp).2)
  have hlow : y ^ hits.card ≤ ∏ p ∈ hits, p := by
    calc
      y ^ hits.card = ∏ _p ∈ hits, y := by simp
      _ ≤ ∏ p ∈ hits, p := prod_le_prod' (fun p hp => hmin p (mem_filter.mp hp).1)
  have habs : 0 < z.natAbs := Int.natAbs_pos.mpr hz
  exact (Nat.le_log_iff_pow_le hy (by omega)).mpr
    (hlow.trans (Nat.le_of_dvd habs hdiv))

theorem sum_scores (T : Finset ι) (difference : ι → ℤ) (weight : ℤ → ℕ)
    (C : Finset ℕ) (q : ℕ) :
    (∑ p ∈ C, score T difference weight (q * p)) =
      ∑ i ∈ T, (C.filter fun p => q * p ∣ (difference i).natAbs).card *
        weight (difference i) := by
  unfold score
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [← sum_filter]
  simp

/-- The finite averaging estimate is valid on YES instances too: zero
differences are removed by their zero weight. -/
theorem sum_scores_le (T : Finset ι) (difference : ι → ℤ) (weight : ℤ → ℕ)
    (hzero : weight 0 = 0) (C : Finset ℕ) (q K : ℕ)
    (hdivisors : ∀ i ∈ T, difference i ≠ 0 →
      (C.filter fun p => p ∣ (difference i).natAbs).card ≤ K) :
    (∑ p ∈ C, score T difference weight (q * p)) ≤ K * score T difference weight q := by
  rw [sum_scores, score, mul_sum]
  apply sum_le_sum
  intro i hi
  by_cases hz : difference i = 0
  · simp [hz, hzero]
  by_cases hq : q ∣ (difference i).natAbs
  · rw [if_pos hq]
    apply Nat.mul_le_mul_right
    apply le_trans (card_le_card ?_) (hdivisors i hi hz)
    intro p hp
    exact mem_filter.mpr ⟨(mem_filter.mp hp).1,
      dvd_trans (dvd_mul_left p q) (mem_filter.mp hp).2⟩
  · rw [if_neg hq, mul_zero]
    have hempty : (C.filter fun p => q * p ∣ (difference i).natAbs) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hq (dvd_trans (dvd_mul_right q p) (mem_filter.mp hp).2)
    simp [hempty]

theorem sum_scores_le_log (T : Finset ι) (difference : ι → ℤ) (weight : ℤ → ℕ)
    (hzero : weight 0 = 0) (C : Finset ℕ) (q y M : ℕ) (hy : 1 < y)
    (hprime : ∀ p ∈ C, Nat.Prime p) (hmin : ∀ p ∈ C, y ≤ p)
    (hbound : ∀ i ∈ T, (difference i).natAbs ≤ M) :
    (∑ p ∈ C, score T difference weight (q * p)) ≤
      Nat.log y M * score T difference weight q := by
  apply sum_scores_le T difference weight hzero C q (Nat.log y M)
  intro i hi hz
  exact (prime_divisors_card_le_log C y hy hprime hmin (difference i) hz).trans
    (Nat.log_mono_right (hbound i hi))

theorem exists_contracting_prime (T : Finset ι) (difference : ι → ℤ)
    (weight : ℤ → ℕ) (C : Finset ℕ) (hC : C.Nonempty) (q K : ℕ)
    (havg : (∑ p ∈ C, score T difference weight (q * p)) ≤
      K * score T difference weight q) :
    ∃ p ∈ C, C.card * score T difference weight (q * p) ≤
      K * score T difference weight q := by
  obtain ⟨p, hp, hmin⟩ := C.exists_min_image (fun p => score T difference weight (q * p)) hC
  refine ⟨p, hp, le_trans ?_ havg⟩
  simpa [nsmul_eq_mul] using C.card_nsmul_le_sum
    (fun p => score T difference weight (q * p)) _ hmin

/-- Concrete minimum search; no random prime is sampled. -/
def selectPrime (candidates : List ℕ) (T : Finset ι) (difference : ι → ℤ)
    (weight : ℤ → ℕ) (q : ℕ) : ℕ :=
  (candidates.argmin fun p => score T difference weight (q * p)).getD 0

theorem selectPrime_mem (candidates : List ℕ) (hne : candidates ≠ [])
    (T : Finset ι) (difference : ι → ℤ) (weight : ℤ → ℕ) (q : ℕ) :
    selectPrime candidates T difference weight q ∈ candidates := by
  unfold selectPrime
  cases h : candidates.argmin (fun p => score T difference weight (q * p)) with
  | none => exact False.elim (hne (List.argmin_eq_none.mp h))
  | some p =>
    simp only [Option.getD_some]
    exact List.argmin_mem (f := fun p => score T difference weight (q * p))
      (by simpa only [Option.mem_def] using h)

theorem selectPrime_min (candidates : List ℕ) (T : Finset ι) (difference : ι → ℤ)
    (weight : ℤ → ℕ) (q : ℕ) {p : ℕ} (hp : p ∈ candidates) :
    score T difference weight (q * selectPrime candidates T difference weight q) ≤
      score T difference weight (q * p) := by
  unfold selectPrime
  cases h : candidates.argmin (fun p => score T difference weight (q * p)) with
  | none => have := List.argmin_eq_none.mp h; simp_all
  | some p =>
    simp only [Option.getD_some]
    exact List.le_of_mem_argmin (f := fun p => score T difference weight (q * p)) hp
      (by simpa only [Option.mem_def] using h)

def modulus (candidates : List ℕ) (T : Finset ι) (difference : ι → ℤ)
    (weight : ℤ → ℕ) : ℕ → ℕ
  | 0 => 1
  | r + 1 =>
    let q := modulus candidates T difference weight r
    q * selectPrime candidates T difference weight q

theorem modulus_bounds (candidates : List ℕ) (hne : candidates ≠ [])
    (T : Finset ι) (difference : ι → ℤ) (weight : ℤ → ℕ) (y Y r : ℕ)
    (hlo : ∀ p ∈ candidates, y ≤ p) (hhi : ∀ p ∈ candidates, p ≤ Y) :
    y ^ r ≤ modulus candidates T difference weight r ∧
      modulus candidates T difference weight r ≤ Y ^ r := by
  induction r with
  | zero => simp [modulus]
  | succ r ih =>
    have hmem := selectPrime_mem candidates hne T difference weight
      (modulus candidates T difference weight r)
    constructor
    · simpa [modulus, pow_succ] using Nat.mul_le_mul ih.1 (hlo _ hmem)
    · simpa [modulus, pow_succ] using Nat.mul_le_mul ih.2 (hhi _ hmem)

/-- The exact iterated contraction, retaining the computed integer score. -/
theorem modulus_score_bound (candidates : List ℕ) (C : Finset ℕ)
    (hC : C.Nonempty) (hall : ∀ p ∈ C, p ∈ candidates)
    (T : Finset ι) (difference : ι → ℤ) (weight : ℤ → ℕ) (K r : ℕ)
    (havg : ∀ q, (∑ p ∈ C, score T difference weight (q * p)) ≤
      K * score T difference weight q) :
    C.card ^ r * score T difference weight (modulus candidates T difference weight r) ≤
      K ^ r * score T difference weight 1 := by
  induction r with
  | zero => simp [modulus]
  | succ r ih =>
    let q := modulus candidates T difference weight r
    obtain ⟨p, hp, hcontract⟩ := exists_contracting_prime T difference weight C hC q K (havg q)
    have hselected := selectPrime_min candidates T difference weight q (hall p hp)
    have hstep : C.card * score T difference weight (q * selectPrime candidates T difference weight q) ≤
        K * score T difference weight q :=
      (Nat.mul_le_mul_left _ hselected).trans hcontract
    calc
      C.card ^ (r + 1) * score T difference weight (modulus candidates T difference weight (r + 1)) =
          C.card ^ r * (C.card * score T difference weight
            (q * selectPrime candidates T difference weight q)) := by simp only [modulus, q]; ring
      _ ≤ C.card ^ r * (K * score T difference weight q) := Nat.mul_le_mul_left _ hstep
      _ = K * (C.card ^ r * score T difference weight q) := by ring
      _ ≤ K * (K ^ r * score T difference weight 1) := Nat.mul_le_mul_left _ ih
      _ = K ^ (r + 1) * score T difference weight 1 := by ring

end ThreeSum.PrimeChain
