import Submission.ThreeSum.BoxStages

/-! # Derived integer bounds for signed sparse-box sums -/

namespace ThreeSum.BoxBounds

open Finset ThreeSum.SubsetAddress

theorem boxSum_abs_le {L cut U : ℕ} (flags free : Finset (Fin L))
    (weight : Finset (Fin L) → ℤ) (hflags : flags.card ≤ cut)
    (hweight : ∀ S, S.card ≤ cut → |weight S| ≤ U) :
    |SparseBoxes.boxSum flags free weight| ≤ ((2^L*U : ℕ) : ℤ) := by
  have hwidth := (subsetMask_isMask flags).le_width
  have hpow := Nat.pow_le_pow_right (show 1 ≤ (2 : ℕ) by decide) hwidth
  have hmul := Nat.mul_le_mul_right U hpow
  unfold SparseBoxes.boxSum
  calc
    _ ≤ ∑ leaf ∈ flags.powerset, |if flags \ free ⊆ leaf then weight leaf else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _leaf ∈ flags.powerset, (U : ℤ) := by
      apply Finset.sum_le_sum
      intro leaf hl
      have hcard := (Finset.card_le_card (Finset.mem_powerset.mp hl)).trans hflags
      split
      · exact hweight leaf hcard
      · simp
    _ = ((2^flags.card*U : ℕ) : ℤ) := by simp
    _ ≤ _ := by exact_mod_cast hmul

end ThreeSum.BoxBounds
