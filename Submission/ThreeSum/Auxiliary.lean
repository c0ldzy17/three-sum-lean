import Submission.ThreeSum.PrimeChain
import Submission.ThreeSum.PrimeDensity
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Exact auxiliary tests from the same finite prime pool

The prime pool used for deterministic contraction supplies enough distinct
primes to separate bounded nonzero differences. To use this same pool in
the weighted counting identity, the joint modulus must account for a prime
that already divides the current modulus; see `WeightedModuli.lean`.
-/

namespace ThreeSum.Auxiliary

open Finset
open scoped BigOperators

def moduli (C : Finset ℕ) : Finset ℤ := C.image (fun p : ℕ => (p : ℤ))

theorem moduli_card (C : Finset ℕ) : (moduli C).card = C.card := by
  exact card_image_of_injective C (show Function.Injective (fun p : ℕ => (p : ℤ)) from Nat.cast_injective)

theorem prime_product_lower (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p) :
    2 ^ C.card ≤ ∏ p ∈ C, p := by
  calc
    2 ^ C.card = ∏ _p ∈ C, 2 := by simp
    _ ≤ ∏ p ∈ C, p := prod_le_prod' (fun p hp => (hC p hp).two_le)

theorem product_gt_of_card (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p)
    (M : ℕ) (hcard : Nat.log 2 M < C.card) : M < ∏ p ∈ C, p := by
  exact (Nat.lt_pow_succ_log_self (by decide : 1 < 2) M).trans_le
    ((Nat.pow_le_pow_right (by decide : 1 ≤ 2) hcard).trans (prime_product_lower C hC))

theorem moduli_product (C : Finset ℕ) :
    (∏ p ∈ moduli C, p) = (∏ p ∈ C, p : ℕ) := by
  rw [moduli, Finset.prod_image]
  · simp
  · intro p hp q hq hpq
    exact Nat.cast_injective hpq

theorem moduli_pairwise_coprime (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p) :
    (moduli C : Set ℤ).Pairwise (fun a b => IsCoprime a b) := by
  intro a ha b hb hne
  obtain ⟨p, hp, rfl⟩ := mem_image.mp ha
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hb
  have hpq : p ≠ q := by intro h; subst q; exact hne rfl
  have hc : p.Coprime q := (Nat.coprime_primes (hC p hp) (hC q hq)).mpr hpq
  exact hc.isCoprime

theorem separates_nonzero (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p)
    {M : ℕ} (hprod : M < ∏ p ∈ C, p)
    {z : ℤ} (hz : z ≠ 0) (hbound : z.natAbs ≤ M) :
    ∃ p ∈ moduli C, ¬p ∣ z := by
  apply Arithmetic.exists_aux_not_dvd_of_prod_bound (moduli C) z
    (moduli_pairwise_coprime C hC) hz
  rw [moduli_product, Int.natAbs_natCast]
  exact hbound.trans_lt hprod

theorem missWeight_bounds (C : Finset ℕ) (z : ℤ) :
    Arithmetic.missWeight (moduli C) z ≤ C.card := by
  unfold Arithmetic.missWeight
  calc
    _ ≤ ∑ _p ∈ moduli C, 1 := by
      apply sum_le_sum
      intro p hp
      split <;> omega
    _ = C.card := by simp [moduli_card]

theorem missWeight_positive (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p)
    {M : ℕ} (hprod : M < ∏ p ∈ C, p)
    {z : ℤ} (hz : z ≠ 0) (hbound : z.natAbs ≤ M) :
    1 ≤ Arithmetic.missWeight (moduli C) z := by
  obtain ⟨p, hp, hpz⟩ := separates_nonzero C hC hprod hz hbound
  exact Arithmetic.missWeight_pos_of_witness hp hpz

theorem candidate_pool_separates (y M : ℕ)
    (hcard : Nat.log 2 M < (PrimeDensity.candidates y).card)
    {z : ℤ} (hz : z ≠ 0) (hbound : z.natAbs ≤ M) :
    ∃ p ∈ moduli (PrimeDensity.candidates y), ¬p ∣ z := by
  have hprime : ∀ p ∈ PrimeDensity.candidates y, Nat.Prime p :=
    fun p hp => (PrimeDensity.mem_candidates.mp hp).1
  exact separates_nonzero _ hprime (product_gt_of_card _ hprime M hcard) hz hbound

end ThreeSum.Auxiliary
