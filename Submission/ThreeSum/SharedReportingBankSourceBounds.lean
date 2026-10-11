import Submission.ThreeSum.SharedReportingBankSources
import Submission.ThreeSum.SourceBandFinite

/-! # Retained source pointers and complete source families precede the bank end -/

namespace ThreeSum.SharedReportingBankSources

open Light SubsetAddress BlockIndexedQuery GlobalEncoding

theorem source_bounds {base NB NC g h J cut i s : ℕ}
    (hi : i < SourceBandPairSlices.count NB NC g)
    (hs : s < LightBlockSourceCatalog.count h J) :
    leftCell base h J cut i s < SourceBandBankData.finish base NB NC g h J cut ∧
    rightCell base h J cut i s < SourceBandBankData.finish base NB NC g h J cut ∧
    leftBase base h J cut i s+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤
      SourceBandBankData.finish base NB NC g h J cut ∧
    rightBase base h J cut i s+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤
      SourceBandBankData.finish base NB NC g h J cut := by
  have hend := SourceBandBankLayout.baseAt_mono (SourceBandBankData.first base) h J cut
    (show i+1 ≤ SourceBandPairSlices.count NB NC g by omega)
  have hwork := (SourceBandBankLayout.work_le_end (SourceBandBankData.first base) h J cut i).trans hend
  change LightBlockSourceBatchLayout.work (bankBase base h J cut i)
    (LightBlockSourceCatalog.count h J) (J*(512*h)) cut ≤
      SourceBandBankData.finish base NB NC g h J cut at hwork
  have hhead := LightBlockSourceBatchLayout.banks_le_work (bankBase base h J cut i)
    (LightBlockSourceCatalog.count h J) (J*(512*h)) cut
  unfold LightBlockSourceBatchLayout.banks at hhead
  have hright := (LightBlockSourceBatchLayout.right_end_le_masks
    (base := bankBase base h J cut i) (W := J*(512*h)) (cut := cut) hs).trans
    (LightBlockSourceBatchLayout.masks_le_work _ _ _ _)
  have hleft := LightBlockSourceBatchLayout.right_ge_left (bankBase base h J cut i)
    (LightBlockSourceCatalog.count h J) (J*(512*h)) cut s
  change leftBase base h J cut i s ≤ rightBase base h J cut i s at hleft
  change rightBase base h J cut i s+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤
    LightBlockSourceBatchLayout.work (bankBase base h J cut i)
      (LightBlockSourceCatalog.count h J) (J*(512*h)) cut at hright
  unfold leftCell rightCell
  omega

theorem source_card_le (n g i : ℕ) : (SourceBandPartition.source n g i).card ≤ g := by
  rw [SourceBandPartition.source_card]
  exact BandPartition.length_le n g i

theorem left_abs_le (p : ℤ) (NB g i h J s : ℕ) (fB : ℕ → ℤ)
    (S : Finset (Fin (J*(512*h)))) :
    |leftSource p (SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val)
      (BlockSourceOccurrenceOrder.representative h J s) S| ≤ (g : ℤ) :=
  (leftSource_abs_le _ _ _ _ _).trans (Int.ofNat_le.mpr (source_card_le NB g i))

theorem right_abs_le (p shift : ℤ) (NC g i h J s : ℕ) (fC : ℕ → ℤ)
    (S : Finset (Fin (J*(512*h)))) :
    |rightSource p shift (SourceBandPartition.source NC g i) (fun t : Fin NC => fC t.val)
      (BlockSourceOccurrenceOrder.representative h J s) S| ≤ (g : ℤ) :=
  (rightSource_abs_le _ _ _ _ _ _).trans (Int.ofNat_le.mpr (source_card_le NC g i))

end ThreeSum.SharedReportingBankSources
