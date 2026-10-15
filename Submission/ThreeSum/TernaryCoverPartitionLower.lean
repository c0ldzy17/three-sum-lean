import Submission.ThreeSum.BinomialEntropy
import Submission.ThreeSum.LocalCoverBounds

/-! # Elementary finite lower bounds for balanced local partitions -/

namespace ThreeSum.TernaryCoverPartitionLower

open BinomialEntropy LocalCoverBounds

theorem three_pow_le_weighted_choose (s : ℕ) :
    3 ^ (3*s) ≤ (3*s+1) * (3*s).choose s * 2 ^ (2*s) := by
  by_cases hs : s = 0
  · subst s; norm_num
  have h := (weight_bounds (n := 3*s) (k := s) (by omega)).2
  have hsub : 3*s-s = 2*s := by omega
  unfold weight at h
  rw [hsub] at h
  have hn : (3*s) ^ (3*s) ≤ (3*s+1) * ((3*s).choose s * s^s * (2*s)^(2*s)) := by
    exact_mod_cast h
  have he : s^s*s^(2*s) = s^(3*s) := by rw [← pow_add]; congr 1; omega
  have ht : 3^(3*s)*s^(3*s) ≤ ((3*s+1)*(3*s).choose s*2^(2*s))*s^(3*s) := by
    calc
      _ = (3*s)^(3*s) := (mul_pow _ _ _).symm
      _ ≤ (3*s+1)*(3*s).choose s*s^s*(2*s)^(2*s) := by simpa [Nat.mul_assoc] using hn
      _ = _ := by rw [mul_pow]; rw [← he]; ring
  exact Nat.le_of_mul_le_mul_right ht (Nat.pow_pos (Nat.pos_of_ne_zero hs))

theorem three_pow_le_balanced_partitions (s : ℕ) :
    3 ^ (3*s) ≤ (3*s+1)*(2*s+1)*((3*s).choose s*(2*s).choose s) := by
  have h2 := groupSize_lower s
  have h3 := three_pow_le_weighted_choose s
  calc
    _ ≤ (3*s+1)*(3*s).choose s*2^(2*s) := h3
    _ ≤ (3*s+1)*(3*s).choose s*((2*s+1)*(2*s).choose s) :=
      Nat.mul_le_mul_left _ h2
    _ = _ := by ring

theorem partitionCap_le_poly_mul_group (r s : ℕ) :
    2 ^ (2*r) * 3 ^ (3*s) ≤
      (2*r+1)*(3*s+1)*(2*s+1)*
        ((2*r).choose r * (3*s).choose s * (2*s).choose s) := by
  have h := Nat.mul_le_mul (groupSize_lower r) (three_pow_le_balanced_partitions s)
  simpa [groupSize, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

end ThreeSum.TernaryCoverPartitionLower
