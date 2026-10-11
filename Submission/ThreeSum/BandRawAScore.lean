import Submission.ThreeSum.BandRawAProduct

/-!
# The aggregate prime score is the exact physical incidence-product score

The executable A catalog supplies the first-coordinate values. Its owner
metadata supplies the B/C slices. Thus the mathematical score summed by
the actual prime selector counts this same domain with all multiplicities.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 1900000
set_option maxRecDepth 8000

def valueAt (n g : ℕ) (rs : List Record) (A : ℕ → ℤ) (i : ℕ) : ℤ :=
  (values A (items n g rs)).getD i 0

theorem valueAt_owner {n g s j : ℕ} {rs : List Record} (A : ℕ → ℤ)
    (hs : s < rs.length) (hj : j < (row n g s (rs.getD s default)).length) :
    valueAt n g rs A (count n g rs s+j)=A (BandPartition.start g (rs.getD s default).a+j) :=
  values_getD_owner A hs hj

theorem owner_weightedFalseCount (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) {s : ℕ} (hs : s < rs.length) :
    Arithmetic.weightedFalseCount (ownerProduct nA nB nC g rs s)
      (ModuloCounts.difference (valueAt nA g rs A) B C)
      (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux)) q=
      BandWeightedScore.block primes aux q nA nB nC g A B C (rs.getD s default) := by
  unfold Arithmetic.weightedFalseCount
  rw [sum_ownerProduct]
  unfold BandWeightedScore.block
  by_cases hf : (rs.getD s default).flag=1
  · simp only [if_pos hf,WeightedScore.score,Arithmetic.weightedFalseCount,
      ModuloCounts.triples,sum_product]
    have hrow : (row nA g s (rs.getD s default)).length=
        BandWeightedScore.length nA g (rs.getD s default).a := by
      rw [row_length,if_pos hf,bandLength_eq_score_length]
    rw [hrow]
    simp_rw [bandLength_eq_score_length]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    apply sum_congr rfl
    intro k hk
    have hi' : i < (row nA g s (rs.getD s default)).length := by
      rw [hrow]
      exact mem_range.mp hi
    simp only [ModuloCounts.difference,valueAt_owner A hs hi',BandPartition.start]
    rfl
  · simp only [if_neg hf,row_length,range_zero,sum_empty]

theorem all_weightedFalseCount (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) :
    Arithmetic.weightedFalseCount (allProducts nA nB nC g rs)
      (ModuloCounts.difference (valueAt nA g rs A) B C)
      (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux)) q=
      BandWeightedScore.score primes aux q nA nB nC g A B C rs := by
  unfold Arithmetic.weightedFalseCount
  rw [sum_allProducts]
  unfold BandWeightedScore.score BandWeightedScore.partialScore
  apply sum_congr rfl
  intro s hs
  exact owner_weightedFalseCount primes aux q nA nB nC g A B C rs (mem_range.mp hs)

theorem aIndices_card (n g : ℕ) (rs : List Record) (s : ℕ) :
    (aIndices n g rs s).card=(row n g s (rs.getD s default)).length := by
  unfold aIndices
  rw [card_image_of_injective _ (by intro i j he; exact Nat.add_left_cancel he),card_range]

theorem bandPositions_card (n g a : ℕ) :
    (bandPositions n g a).card=bandLength n g a := by
  unfold bandPositions
  rw [card_image_of_injective _ (by intro i j he; exact Nat.add_left_cancel he),card_range]

theorem ownerProduct_card (nA nB nC g : ℕ) (rs : List Record) (s : ℕ) :
    (ownerProduct nA nB nC g rs s).card=
      (row nA g s (rs.getD s default)).length*
        bandLength nB g (rs.getD s default).b*bandLength nC g (rs.getD s default).c := by
  simp only [ownerProduct,card_product,aIndices_card,bandPositions_card,Nat.mul_assoc]

theorem ownerProduct_card_le (nA nB nC g : ℕ) (rs : List Record) (s : ℕ) :
    (ownerProduct nA nB nC g rs s).card ≤ g^3 := by
  rw [ownerProduct_card]
  calc
    _ ≤ g*g*g := Nat.mul_le_mul (Nat.mul_le_mul (row_length_le ..)
      (BandPartition.length_le ..)) (BandPartition.length_le ..)
    _ = _ := by ring

theorem allProducts_card_le (nA nB nC g : ℕ) (rs : List Record) :
    (allProducts nA nB nC g rs).card ≤ rs.length*g^3 := by
  calc
    _ = ∑ t ∈ allProducts nA nB nC g rs, (1 : ℕ) := by simp
    _ = ∑ s ∈ range rs.length, (ownerProduct nA nB nC g rs s).card := by
      rw [sum_allProducts]
      simp
    _ ≤ ∑ _s ∈ range rs.length, g^3 := sum_le_sum fun s _ => ownerProduct_card_le nA nB nC g rs s
    _ = _ := by simp

/-- The weighted score bound applies directly to the physical owner domain. -/
theorem physical_weighted_bound (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record)
    (hprime : ∀ i < aux, Nat.Prime (primes i))
    (hinj : ∀ i < aux, ∀ j < aux, primes i=primes j → i=j) :
    Arithmetic.weightedFalseCount (allProducts nA nB nC g rs)
      (ModuloCounts.difference (valueAt nA g rs A) B C)
      (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux)) q ≤ rs.length*(aux*g^3) := by
  rw [all_weightedFalseCount]
  exact BandWeightedScore.score_bound primes aux q nA nB nC g A B C rs hprime hinj

end ThreeSum.BandRawA
