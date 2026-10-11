import Submission.ThreeSum.SourceTableLayout
import Submission.ThreeSum.BlockIndexedQuery

/-! # Compact source arrays in the unchanged block-query coordinate system -/

namespace ThreeSum.BlockSourceTableLayout

open SubsetAddress BlockIndex BlockEncoding BlockRows GlobalEncoding

def sets (h J cut i : ℕ) : Finset (Coord J (512*h)) :=
  unindexSet (SourceTableLayout.setAt (J*(512*h)) cut i)

theorem mask_sets {h J cut i : ℕ} (hi : i < downsetCap (J*(512*h)) cut) :
    subsetMask (indexSet (sets h J cut i)) = SourceTableLayout.maskAt (J*(512*h)) cut i := by
  rw [sets,index_unindex,SourceTableLayout.subsetMask_setAt hi]

theorem sets_subsetRank {h J cut : ℕ} (S : Finset (Coord J (512*h)))
    (hS : S.card ≤ cut) :
    sets h J cut (subsetRank (indexSet S)) = S := by
  rw [sets,SourceTableLayout.setAt_subsetRank (indexSet S) (by simpa using hS),unindex_index]

theorem left_tableAt {β : Type*} [Fintype β] [DecidableEq β]
    {h J cut base : ℕ} {μ : ℕ → ℤ}
    (P : ℤ) (B : Finset β) (b : β → ℤ) (q : GlobalOutput h J)
    (hread : ∀ i < downsetCap (J*(512*h)) cut,
      μ (base+i) = (leftWeights (outputOccurrences q) P B b (sets h J cut i) : ℤ)) :
    LightZetaCell.TableAt μ base cut (BlockIndexedQuery.leftSource P B b q) := by
  apply SourceTableLayout.tableAt_of_setAt
  exact hread

theorem right_tableAt {β : Type*} [Fintype β] [DecidableEq β]
    {h J cut base : ℕ} {μ : ℕ → ℤ}
    (P shift : ℤ) (C : Finset β) (c : β → ℤ) (q : GlobalOutput h J)
    (hread : ∀ i < downsetCap (J*(512*h)) cut,
      μ (base+i) = (rightWeights (outputOccurrences q) P shift C c (sets h J cut i) : ℤ)) :
    LightZetaCell.TableAt μ base cut (BlockIndexedQuery.rightSource P shift C c q) := by
  apply SourceTableLayout.tableAt_of_setAt
  exact hread

end ThreeSum.BlockSourceTableLayout
