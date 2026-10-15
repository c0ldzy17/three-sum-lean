import Submission.ThreeSum.TernaryCoverActualMoment
import Submission.ThreeSum.Cover

/-! # Actual global raw-cap pruning

The bad-map test ranges over every ordered target pair.  The loss of retained
first moment is charged by the actual `B²` endpoint cap before the moment
order and raw threshold are selected.
-/

noncomputable section
namespace ThreeSum.TernaryCoverGoodMaps

open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open TernaryLocalParameters TernaryCoverActualMoment TernaryCoverMoments
open scoped BigOperators

abbrev Weight (m p : ℕ) := Coordinate (Fin (fixedLength m)) → ZMod p
abbrev ActualEdge (m : ℕ) := LocalEdge (fixedLength m) (fixedAlpha m) (fixedPi m)

variable (m p : ℕ) [Fact p.Prime]

def rawBadMaps (τ : ℕ) : Finset (Weight m p) :=
  badMaps (fun w (t : ZMod p × ZMod p) => TernaryCoverFibers.rawPairCount
    (leftHash (α := fixedAlpha m) (π := fixedPi m) w) (rightHash w) t.1 t.2) τ

def prunedHit (B τ : ℕ) (w : Weight m p) (a b : ZMod p) : ℕ := by
  classical
  exact if w ∈ rawBadMaps m p τ then 0 else hitCount (fixedAlpha m) (fixedPi m) B w a b

theorem rawBadMaps_count_bound (hp : 4 < p)
    (hP : (vertices (fixedLength m) (fixedPi m)).card *
      (2 ^ (fixedPi m 1) * 3 ^ (fixedPi m 2)) ≤ p ^ 2) (k τ : ℕ) :
    τ ^ k * (rawBadMaps m p τ).card ≤ p ^ 2 * 3 ^ (4*k^2) * Fintype.card (Weight m p) := by
  have h := badMaps_count_bound
    (fun w (t : ZMod p × ZMod p) => TernaryCoverFibers.rawPairCount
      (leftHash (α := fixedAlpha m) (π := fixedPi m) w) (rightHash w) t.1 t.2)
    k τ (3 ^ (4*k^2)) (fun t => actual_high_moment m p hp hP k t.1 t.2)
  simpa [rawBadMaps, Weight, pow_two, Nat.mul_assoc] using h

theorem pruned_first_moment (hp : 4 < p)
    (hP : (vertices (fixedLength m) (fixedPi m)).card *
      (2 ^ (fixedPi m 1) * 3 ^ (fixedPi m 2)) ≤ p ^ 2)
    (B k τ : ℕ) (hτ : 0 < τ)
    (hB : 8 * (p + (fieldVertices (fixedLength m) p (fixedAlpha m)).card) ≤ B * p)
    (hguard : 16*p^4*B^2*3^(4*k^2) ≤ τ^k*Fintype.card (ActualEdge m))
    (a b : ZMod p) :
    Fintype.card (ActualEdge m) * Fintype.card (Weight m p) ≤
      2 * p ^ 2 * ∑ w, prunedHit m p B τ w a b := by
  classical
  have hbad := rawBadMaps_count_bound m p hp hP k τ
  have hloss : 16*p^2*B^2*(rawBadMaps m p τ).card ≤
      Fintype.card (ActualEdge m)*Fintype.card (Weight m p) := by
    apply Nat.le_of_mul_le_mul_left (c := τ^k) ?_ (Nat.pow_pos hτ)
    calc
      _ = 16*p^2*B^2*(τ^k*(rawBadMaps m p τ).card) := by ring
      _ ≤ 16*p^2*B^2*(p^2*3^(4*k^2)*Fintype.card (Weight m p)) :=
        Nat.mul_le_mul_left _ hbad
      _ = (16*p^4*B^2*3^(4*k^2))*Fintype.card (Weight m p) := by ring
      _ ≤ (τ^k*Fintype.card (ActualEdge m))*Fintype.card (Weight m p) :=
        Nat.mul_le_mul_right _ hguard
      _ = _ := by ring
  have hremoved := removed_mass_bound
    (fun w : Weight m p => hitCount (fixedAlpha m) (fixedPi m) B w a b)
    (rawBadMaps m p τ) B (fun w => hitCount_cap _ _ B w a b (by omega : 2 < p))
  have hsum : (∑ w : Weight m p, hitCount (fixedAlpha m) (fixedPi m) B w a b) =
      (∑ w, prunedHit m p B τ w a b) +
        ∑ w ∈ rawBadMaps m p τ, hitCount (fixedAlpha m) (fixedPi m) B w a b := by
    have heq : (univ : Finset (Weight m p)).filter (fun w => w ∈ rawBadMaps m p τ) =
        rawBadMaps m p τ := by ext w; simp
    rw [← heq, sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro w _
    by_cases hw : w ∈ rawBadMaps m p τ <;> simp [prunedHit, hw]
  have hfirst := first_moment (L := fixedLength m) (p := p)
    (fixedAlpha m) (fixedPi m) B a b hB
  rw [hsum] at hfirst
  have hm := Nat.mul_le_mul_left (16*p^2) hremoved
  nlinarith

theorem prunedHit_le_raw (B τ : ℕ) (w : Weight m p) (a b : ZMod p) :
    prunedHit m p B τ w a b ≤ TernaryCoverFibers.rawPairCount
      (leftHash (α := fixedAlpha m) (π := fixedPi m) w) (rightHash w) a b := by
  classical
  unfold prunedHit
  split_ifs
  · exact Nat.zero_le _
  · apply card_le_card
    intro e he
    have ht := (mem_filter.mp he).2
    have hpair := (mem_filter.mp (mem_filter.mp ht).1).2
    exact mem_filter.mpr ⟨mem_univ _, hpair⟩

theorem pruned_second_moment (hp : 4 < p)
    (hP : (vertices (fixedLength m) (fixedPi m)).card *
      (2 ^ (fixedPi m 1) * 3 ^ (fixedPi m 2)) ≤ p ^ 2)
    (B τ : ℕ) (a b : ZMod p) :
    (∑ w : Weight m p, prunedHit m p B τ w a b ^ 2) ≤
      3 ^ 16 * Fintype.card (Weight m p) := by
  exact (sum_le_sum (fun w _ => Nat.pow_le_pow_left (prunedHit_le_raw m p B τ w a b) 2)).trans
    (by simpa using actual_high_moment m p hp hP 2 a b)

end ThreeSum.TernaryCoverGoodMaps
