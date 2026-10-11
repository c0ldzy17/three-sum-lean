import Submission.ThreeSum.Auxiliary

/-!
# Weighted counting with possibly shared prime factors

For prime `p`, simultaneous divisibility by `q` and `p` is tested at `q`
when `p ∣ q`, and at `q*p` otherwise. This executable branch permits one
finite prime pool to supply both contraction and auxiliary tests.
-/

namespace ThreeSum.WeightedModuli

open Finset Arithmetic
open scoped BigOperators

def joint (q p : ℕ) : ℕ := if p ∣ q then q else q * p

theorem joint_le_mul (q p : ℕ) (hp : 1 ≤ p) : joint q p ≤ q * p := by
  unfold joint
  split
  · exact Nat.le_mul_of_pos_right q hp
  · exact le_rfl

theorem joint_positive {q p : ℕ} (hq : 0 < q) (hp : Nat.Prime p) :
    0 < joint q p := by
  unfold joint
  split
  · exact hq
  · exact Nat.mul_pos hq hp.pos

theorem joint_dvd_iff (q p : ℕ) (hp : Nat.Prime p) (z : ℤ) :
    (joint q p : ℤ) ∣ z ↔ (q : ℤ) ∣ z ∧ (p : ℤ) ∣ z := by
  by_cases h : p ∣ q
  · simp only [joint, if_pos h]
    exact ⟨fun hz => ⟨hz, (Int.natCast_dvd_natCast.mpr h).trans hz⟩, fun hz => hz.1⟩
  · simp only [joint, if_neg h, Nat.cast_mul]
    have hc : IsCoprime (q : ℤ) (p : ℤ) :=
      ((hp.coprime_iff_not_dvd.mpr h).symm).isCoprime
    obtain ⟨u, v, huv⟩ := hc
    exact mul_dvd_iff_of_bezout ⟨u, v, huv⟩

theorem weighted_indicator (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p)
    (q : ℕ) (z : ℤ) :
    (if (q : ℤ) ∣ z then missWeight (Auxiliary.moduli C) z else 0) +
      (∑ p ∈ C, dividesIndicator (joint q p) z) =
      C.card * dividesIndicator q z := by
  have hmod : (∑ p ∈ C, dividesIndicator (p : ℤ) z) =
      ∑ p ∈ Auxiliary.moduli C, dividesIndicator p z := by
    rw [Auxiliary.moduli, Finset.sum_image]
    intro a ha b hb heq
    exact Nat.cast_injective heq
  by_cases hq : (q : ℤ) ∣ z
  · have hjoint : (∑ p ∈ C, dividesIndicator (joint q p) z) =
        ∑ p ∈ C, dividesIndicator (p : ℤ) z := by
      apply Finset.sum_congr rfl
      intro p hp
      simp [dividesIndicator, joint_dvd_iff q p (hC p hp), hq]
    rw [if_pos hq, hjoint, hmod]
    simpa [dividesIndicator, hq, Auxiliary.moduli_card] using
      missWeight_add_hits (Auxiliary.moduli C) z
  · have hjoint : (∑ p ∈ C, dividesIndicator (joint q p) z) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      simp [dividesIndicator, joint_dvd_iff q p (hC p hp), hq]
    rw [if_neg hq, hjoint]
    simp [dividesIndicator, hq]

theorem weighted_count_add {ι : Type*} (T : Finset ι) (difference : ι → ℤ)
    (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p) (q : ℕ) :
    weightedFalseCount T difference (Auxiliary.moduli C) q +
      (∑ p ∈ C, modCount T difference (joint q p)) =
      C.card * modCount T difference q := by
  unfold weightedFalseCount modCount
  calc
    _ = ∑ i ∈ T, ((if (q : ℤ) ∣ difference i then
        missWeight (Auxiliary.moduli C) (difference i) else 0) +
        ∑ p ∈ C, dividesIndicator (joint q p) (difference i)) := by
          rw [Finset.sum_add_distrib, Finset.sum_comm]
    _ = ∑ i ∈ T, C.card * dividesIndicator q (difference i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact weighted_indicator C hC q (difference i)
    _ = _ := by rw [Finset.mul_sum]

theorem weighted_count_eq {ι : Type*} (T : Finset ι) (difference : ι → ℤ)
    (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p) (q : ℕ) :
    weightedFalseCount T difference (Auxiliary.moduli C) q =
      C.card * modCount T difference q -
        (∑ p ∈ C, modCount T difference (joint q p)) := by
  have h := weighted_count_add T difference C hC q
  omega

end ThreeSum.WeightedModuli
