import Submission.ThreeSum.LightReportingCatalogIndex
import Submission.ThreeSum.LightReportingSuffixQueryIndexed

/-!
# Exact original valid-prefix selection from the complete physical catalog

The index is a proof witness for the actual unique stored mask pair. It is not
an argument supplied to the querying machine: the physical sorted lookup
recovers it from the two original prefix masks.
-/

namespace ThreeSum.ReportingHostCatalogSelection

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixCatalog ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog

theorem original_index {h J k : ℕ} (hk : k ≤ J) (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : ValidPrefix q k pre) :
    ∃ i < count h k,
      preL h J k i = leftPrefix k (prefixRows (J := J) pre) ∧
      preR h J k i = rightPrefix k (outputRows q) (prefixRows (J := J) pre) := by
  obtain ⟨i,hi,hL,hR⟩ := exists_index (J := J) (ofValidPrefix hk q pre hp)
  exact ⟨i,by simpa only [count_eq_length] using hi,
    hL.trans (leftSet_ofValidPrefix hk q pre hp),
    hR.trans (rightSet_ofValidPrefix hk q pre hp)⟩

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

theorem selected_leaf {h J k i : ℕ} (hk : k ≤ J)
    (P shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (o : Occurrences h J) (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (ho : outputOccurrences q = o)
    (hL : preL h J k i = leftPrefix k (prefixRows (J := J) pre))
    (hR : preR h J k i = rightPrefix k (outputRows q) (prefixRows (J := J) pre)) :
    leafWeight (block_fit hk) (leftSourceOf o P B b) (rightSourceOf o P shift C c)
      (suffixStage J (512*h) k) (preL h J k i) (preR h J k i) =
      LightReportingSuffixBoxes.localLeaf hk P shift B C b c q pre := by
  unfold LightReportingSuffixBoxes.localLeaf
  rw [hL,hR,leftSource_eq,rightSource_eq,ho]
  rfl

theorem selected_box {μ : ℕ → ℤ} {h J k i boxCut boxBase : ℕ} (hk : k ≤ J)
    (P shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (o : Occurrences h J) (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (ho : outputOccurrences q = o)
    (hi : i < count h k)
    (hL : preL h J k i = leftPrefix k (prefixRows (J := J) pre))
    (hR : preR h J k i = rightPrefix k (outputRows q) (prefixRows (J := J) pre))
    (hboxes : ∀ j < count h k, LightBoxStages.StoredThrough μ
      (boxBase+j*stride (suffixStage J (512*h) k) boxCut) boxCut
      (leafWeight (block_fit hk) (leftSourceOf o P B b) (rightSourceOf o P shift C c)
        (suffixStage J (512*h) k) (preL h J k j) (preR h J k j))
      (suffixStage J (512*h) k)) :
    LightBoxStages.StoredThrough μ (boxBase+i*stride (suffixStage J (512*h) k) boxCut)
      boxCut (LightReportingSuffixBoxes.localLeaf hk P shift B C b c q pre)
      (suffixStage J (512*h) k) := by
  rw [← selected_leaf hk P shift B C b c o q pre ho hL hR]
  exact hboxes i hi

theorem selected_box_end {N i boxBase boxCut V upper : ℕ} (hi : i < N)
    (hboxes : boxBase+N*stride V boxCut ≤ upper) :
    boxBase+i*stride V boxCut+(V+1)*downsetCap V boxCut ≤ upper := by
  have hm := Nat.mul_le_mul_right (stride V boxCut) (show i+1 ≤ N by omega)
  have hm' : i*stride V boxCut+stride V boxCut ≤ N*stride V boxCut := by
    simpa only [Nat.add_mul,Nat.one_mul] using hm
  change boxBase+i*stride V boxCut+stride V boxCut ≤ upper
  omega

end ThreeSum.ReportingHostCatalogSelection
