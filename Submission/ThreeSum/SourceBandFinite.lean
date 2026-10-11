import Submission.ThreeSum.SourceBandBankData
import Submission.ThreeSum.BandRawAFiniteSlices

/-! # The shared source banks in the physical finite reporting domains -/

namespace ThreeSum.SourceBandFinite

open GlobalEncoding OutputDecodeRecords

theorem source_eq_finiteBandPositions (n g i : ℕ) :
    SourceBandPartition.source n g i=BandRawA.finiteBandPositions n g i := by
  ext t
  rw [SourceBandPartition.mem_source,BandRawA.mem_finiteBandPositions,BandRawA.mem_bandPositions]

theorem len_eq_bandLength (n g i : ℕ) : SourceBandLayout.len n g i=BandRawA.bandLength n g i := rfl

theorem occurrence {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g h J cut occ i k : ℕ} {p shift : ℤ}
    (H : SourceBandBankData.Stored μ fL fR base NL NR g h J cut occ p shift)
    (hi : i < SourceBandPairSlices.count NL NR g) (hk : k < LightBlockSourceCatalog.count h J) :
    LightBlockSourceBatch.BankAt μ (SourceBandBankLayout.baseAt (base+5) h J cut i)
      (LightBlockSourceCatalog.count h J) cut k p shift
      (BandRawA.finiteBandPositions NL g i) (fun t : Fin NL => fL t.val)
      (BandRawA.finiteBandPositions NR g i) (fun t : Fin NR => fR t.val)
      (BlockSourceOccurrenceOrder.representative h J k) := by
  simpa only [SourceBandBankData.first,source_eq_finiteBandPositions] using (H.banks i hi) k hk

theorem decoded {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g h J cut occ i k : ℕ} {p shift : ℤ}
    (H : SourceBandBankData.Stored μ fL fR base NL NR g h J cut occ p shift)
    (hi : i < SourceBandPairSlices.count NL NR g) (hk : k < localCount h^J) :
    LightBlockSourceBatch.BankAt μ (SourceBandBankLayout.baseAt (base+5) h J cut i)
      (LightBlockSourceCatalog.count h J) cut
      (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J k) p shift
      (BandRawA.finiteBandPositions NL g i) (fun t : Fin NL => fL t.val)
      (BandRawA.finiteBandPositions NR g i) (fun t : Fin NR => fR t.val)
      ((GlobalKeyEnumeration.globalRecords h J).getD k (outputDefault h J)) := by
  simpa only [SourceBandBankData.first,source_eq_finiteBandPositions] using H.decoded hi hk

end ThreeSum.SourceBandFinite
