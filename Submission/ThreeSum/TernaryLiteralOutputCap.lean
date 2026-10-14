import Submission.ThreeSum.TernaryPartitionCount
import Submission.ThreeSum.TernaryCoverFibers
import Mathlib.Tactic

noncomputable section
namespace ThreeSum.TernaryLiteralOutputCap
open Finset TernaryJointType TernaryCoverLocal TernaryCoverFibers TernaryPartitionCount

section Finite
variable {E Q K : Type*} [Fintype E] [Fintype Q] [Fintype K]
  [DecidableEq Q] [DecidableEq K] [AddCommGroup K]

theorem literal_output_lower_fiber_bound (output : E → Q) (outputHash : Q → K)
    (left right : E → K) (G τ : ℕ)
    (hfiber : ∀ q : Q, G ≤ (univ.filter fun e => output e = q).card)
    (hadd : ∀ e : E, left e+right e = outputHash (output e))
    (hraw : ∀ a b : K, rawPairCount left right a b ≤ τ) (o : K) :
    G*outputFiberCount outputHash o ≤ Fintype.card K*τ := by
  classical
  have hpartition := card_eq_sum_card_fiberwise
    (s := univ.filter fun e => left e+right e = o)
    (t := univ.filter fun q => outputHash q = o) (f := output)
    (by intro e he; apply mem_filter.mpr; exact ⟨mem_univ _,by rw [← hadd]; exact (mem_filter.mp he).2⟩)
  have hcount : G*outputFiberCount outputHash o ≤ (univ.filter fun e => left e+right e = o).card := by
    rw [hpartition]
    calc
      _ = ∑ _q ∈ univ.filter (fun q => outputHash q = o), G := by simp [outputFiberCount,Nat.mul_comm]
      _ ≤ _ := by
        apply sum_le_sum
        intro q hq
        have heq : ((univ.filter fun e => left e+right e = o).filter fun e => output e = q) =
            univ.filter (fun e => output e = q) := by
          ext e
          simp only [mem_filter,mem_univ,true_and]
          constructor
          · exact fun h => h.2
          · intro he
            refine ⟨?_,he⟩
            rw [hadd,he]
            exact (mem_filter.mp hq).2
        rw [heq]
        exact hfiber q
  rw [← sum_rawPairCount left right o] at hcount
  exact hcount.trans (by simpa using sum_le_sum (fun a (_ : a ∈ (univ : Finset K)) => hraw a (o-a)))
end Finite

section Actual
variable {p : ℕ} [Fact p.Prime]

def actualOutput {t r s : ℕ}
    (e : LocalEdge (t+2*r+3*s) (alphaType t r s) (piType t r s)) :
    {q // q ∈ vertices (t+2*r+3*s) (piType t r s)} := by
  classical
  exact ⟨output e,mem_filter.mpr ⟨mem_univ _,(edge_data e).2.2.1⟩⟩

def actualOutputHash {t r s : ℕ}
    (w : TernaryCoverHashes.Coordinate (Fin (t+2*r+3*s)) → ZMod p)
    (q : {q // q ∈ vertices (t+2*r+3*s) (piType t r s)}) : ZMod p := outputHash w q.val

/-- Actual native output-hash fibers are paid by all original partitions. -/
theorem actual_output_partition_cap (t r s τ : ℕ)
    (w : TernaryCoverHashes.Coordinate (Fin (t+2*r+3*s)) → ZMod p)
    (hraw : ∀ a b : ZMod p,
      rawPairCount (leftHash (α := alphaType t r s) (π := piType t r s) w) (rightHash w) a b ≤ τ)
    (o : ZMod p) :
    partitionGroup r s*outputFiberCount (actualOutputHash w) o ≤ p*τ := by
  classical
  have h := literal_output_lower_fiber_bound
    (actualOutput (t := t) (r := r) (s := s)) (actualOutputHash w)
    (leftHash w) (rightHash w) (partitionGroup r s) τ ?_ (hashes_add w) hraw o
  · simpa using h
  · intro q
    have heq : (univ.filter (fun e => actualOutput e = q)) =
        (univ.filter (fun e : LocalEdge (t+2*r+3*s) (alphaType t r s) (piType t r s) => output e = q.val)) := by
      ext e
      simp [actualOutput,Subtype.ext_iff]
    rw [heq,← Fintype.card_subtype]
    exact output_partitionGroup_lower t r s q.val ((mem_filter.mp q.property).2)

/-- This recovers the full g-exponent output-volume estimate with only a
polynomial loss; no exact uniform-G assumption is required. -/
theorem actual_output_cap (t r s τ : ℕ)
    (w : TernaryCoverHashes.Coordinate (Fin (t+2*r+3*s)) → ZMod p)
    (hraw : ∀ a b : ZMod p,
      rawPairCount (leftHash (α := alphaType t r s) (π := piType t r s) w) (rightHash w) a b ≤ τ)
    (o : ZMod p) :
    (2^(2*r)*3^(3*s))*outputFiberCount (actualOutputHash w) o ≤ partitionLoss r s*p*τ := by
  have hp : 2^(2*r)*3^(3*s) ≤ partitionLoss r s*partitionGroup r s := by
    simpa [partitionLoss,partitionGroup,Nat.mul_assoc] using
      TernaryCoverPartitionLower.partitionCap_le_poly_mul_group r s
  have h := actual_output_partition_cap t r s τ w hraw o
  calc
    _ ≤ (partitionLoss r s*partitionGroup r s)*outputFiberCount (actualOutputHash w) o :=
      Nat.mul_le_mul_right _ hp
    _ = partitionLoss r s*(partitionGroup r s*outputFiberCount (actualOutputHash w) o) := by ring
    _ ≤ partitionLoss r s*(p*τ) := Nat.mul_le_mul_left _ h
    _ = _ := by ring
end Actual
end ThreeSum.TernaryLiteralOutputCap
