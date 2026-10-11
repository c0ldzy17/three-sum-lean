import Submission.ThreeSum.SharedReportingBankData
import Submission.ThreeSum.SourceBandBankData

/-! # Independent source bands and exact reuse for every decoded output -/

namespace ThreeSum.SharedReportingBankSources

open Light GlobalEncoding BlockEncoding BlockIndexedQuery SharedReportingBankData
open BlockSourceOccurrenceOrder BlockSourceSharing OutputDecodeRecords

def bankBase (base h J cut band : ℕ) : ℕ :=
  SourceBandBankLayout.baseAt (SourceBandBankData.first base) h J cut band

def leftCell (base h J cut band occurrence : ℕ) : ℕ := bankBase base h J cut band+2*occurrence
def rightCell (base h J cut band occurrence : ℕ) : ℕ := bankBase base h J cut band+2*occurrence+1

def leftBase (base h J cut band occurrence : ℕ) : ℕ :=
  LightBlockSourceBatchLayout.leftBase (bankBase base h J cut band)
    (LightBlockSourceCatalog.count h J) (J*(512*h)) cut occurrence

def rightBase (base h J cut band occurrence : ℕ) : ℕ :=
  LightBlockSourceBatchLayout.rightBase (bankBase base h J cut band)
    (LightBlockSourceCatalog.count h J) (J*(512*h)) cut occurrence

theorem source_pair {μ : ℕ → ℤ} {fB fC : ℕ → ℤ}
    {base NB NC g h J cut occ i j s : ℕ} {p shift : ℤ}
    (H : SourceBandBankData.Stored μ fB fC base NB NC g h J cut occ p shift)
    (hi : i < SourceBandPairSlices.count NB NC g) (hj : j < SourceBandPairSlices.count NB NC g)
    (hs : s < LightBlockSourceCatalog.count h J) :
    μ (leftCell base h J cut i s)=(leftBase base h J cut i s : ℤ) ∧
      μ (rightCell base h J cut j s)=(rightBase base h J cut j s : ℤ) ∧
      LightZetaStages.StoredThrough μ (leftBase base h J cut i s) cut
        (leftSource p (SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val)
          (representative h J s)) (J*(512*h)) ∧
      LightZetaStages.StoredThrough μ (rightBase base h J cut j s) cut
        (rightSource p shift (SourceBandPartition.source NC g j) (fun t : Fin NC => fC t.val)
          (representative h J s)) (J*(512*h)) :=
  ⟨(H.banks i hi s hs).headerLeft,(H.banks j hj s hs).headerRight,
    (H.banks i hi s hs).left,(H.banks j hj s hs).right⟩

theorem decoded_sources {μ : ℕ → ℤ} {fB fC : ℕ → ℤ}
    {base NB NC g h J occ i j k : ℕ} {p shift : ℤ}
    (H : SourceBandBankData.Stored μ fB fC base NB NC g h J (2*h*J) occ p shift)
    (hi : i < SourceBandPairSlices.count NB NC g) (hj : j < SourceBandPairSlices.count NB NC g)
    (hk : k < localCount h^J) :
    ReportingHostLevelData.Sources μ p shift
      (SourceBandPartition.source NB g i) (SourceBandPartition.source NC g j)
      (fun t : Fin NB => fB t.val) (fun t : Fin NC => fC t.val)
      ((GlobalKeyEnumeration.globalRecords h J).getD k (outputDefault h J))
      (leftBase base h J (2*h*J) i (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J k))
      (rightBase base h J (2*h*J) j (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J k)) :=
  ⟨(H.decoded hi hk).left,(H.decoded hj hk).right⟩

theorem tables_reuse {β γ : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] {h J k : ℕ} {μ : ℕ → ℤ}
    {D : ReportingHostLevelData.Catalog} {hk : k ≤ J}
    (p shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    {q q' : GlobalOutput h J} (ho : outputOccurrences q=outputOccurrences q')
    (H : Tables μ D hk (leftSource p B b q) (rightSource p shift C c q)) :
    Tables μ D hk (leftSource p B b q') (rightSource p shift C c q') := by
  rw [← BlockSourceSharing.leftSource_eq_of_occurrences p B b ho,
    ← BlockSourceSharing.rightSource_eq_of_occurrences p shift C c ho]
  exact H

theorem entry_reuse {β γ : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] {h J k record : ℕ} {μ : ℕ → ℤ}
    {D : ReportingHostLevelData.Catalog} {hk : k ≤ J}
    (p shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    {q q' : GlobalOutput h J} (ho : outputOccurrences q=outputOccurrences q')
    (H : Entry μ record D hk (leftSource p B b q) (rightSource p shift C c q)) :
    Entry μ record D hk (leftSource p B b q') (rightSource p shift C c q') :=
  ⟨H.header,tables_reuse p shift B C b c ho H.tables⟩

theorem reporting_decoded {β γ : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] {h J k output record : ℕ} {μ : ℕ → ℤ}
    {D : ReportingHostLevelData.Catalog} {hk : k ≤ J}
    (p shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (houtput : output < localCount h^J)
    (H : Entry μ record D hk
      (leftSource p B b (representative h J
        (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J output)))
      (rightSource p shift C c (representative h J
        (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J output)))) :
    ReportingHostLevelData.Stored μ D hk p shift B C b c
      ((GlobalKeyEnumeration.globalRecords h J).getD output (outputDefault h J)) :=
  (tables_reuse p shift B C b c (decoded_occurrences houtput) H.tables).reporting p shift B C b c _

end ThreeSum.SharedReportingBankSources
