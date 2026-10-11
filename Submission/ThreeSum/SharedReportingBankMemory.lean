import Submission.ThreeSum.SharedReportingBankLayout

/-! # Retain earlier shared catalogs while appending a later metadata record -/

namespace ThreeSum.SharedReportingBankData

open Light SubsetAddress ReportingHostSuffix ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData

theorem Tables.of_window {h J k low bound : ℕ} {μ ν : ℕ → ℤ}
    {D : Catalog} {hk : k ≤ J} {f g : Finset (Fin (J*(512*h))) → ℤ}
    (H : Tables μ D hk f g) (heq : ∀ a, low ≤ a → a < bound → ν a=μ a)
    (hindexLow : low ≤ D.indexBase) (hptrLow : low ≤ D.ptrBase)
    (hboxLow : low ≤ D.boxBase) (hindex : D.indexBase+count h k ≤ bound)
    (hptr : D.ptrBase+count h k ≤ bound)
    (hbox : D.boxBase+count h k*stride ((J-k)*(512*h)) D.boxCut ≤ bound) :
    Tables ν D hk f g := by
  obtain ⟨S,hs,hperm,hsort⟩ := H.index
  have hlen : S.length=count h k :=
    hperm.length_eq.trans (ReportingHostPackedCatalog.codes_length _ _)
  refine ⟨⟨S,?_,hperm,hsort⟩,?_,?_⟩
  · intro i hi
    exact (heq _ (by omega) (by rw [hlen] at hi; omega)).trans (hs i hi)
  · intro i hi
    have hi' : i < count h k := by simpa only [List.length_map,List.length_ofFn] using hi
    exact (heq _ (by omega) (by omega)).trans (H.pointers i hi)
  · intro i hi
    exact ReportingHostQueryBounds.boxStored_of_on (H.boxes i hi) (by
      intro a ha hb
      exact heq a (by omega)
        (hb.trans_le (ReportingHostCatalogSelection.selected_box_end hi hbox)))

theorem Entry.of_later {h J k record nextRecord low bound : ℕ} {μ ν : ℕ → ℤ}
    {D : Catalog} {hk : k ≤ J} {f g : Finset (Fin (J*(512*h))) → ℤ}
    (H : Entry μ record D hk f g) (heq : KeptBut μ ν bound nextRecord 5)
    (hrecord : record+5 ≤ nextRecord) (hnext : nextRecord+5 ≤ low)
    (hlow : low ≤ bound) (hindexLow : low ≤ D.indexBase)
    (hptrLow : low ≤ D.ptrBase) (hboxLow : low ≤ D.boxBase)
    (hindex : D.indexBase+count h k ≤ bound) (hptr : D.ptrBase+count h k ≤ bound)
    (hbox : D.boxBase+count h k*stride ((J-k)*(512*h)) D.boxCut ≤ bound) :
    Entry ν record D hk f g := by
  refine ⟨?_,H.tables.of_window (fun a ha hb => heq a ⟨hb,Or.inr (by omega)⟩)
    hindexLow hptrLow hboxLow hindex hptr hbox⟩
  intro i hi
  have hi' : i < 5 := by
    simpa only [Catalog.record,List.length_map,List.length_cons,List.length_nil] using hi
  exact (heq _ ⟨by omega,Or.inl (by omega)⟩).trans (H.header i hi)

end ThreeSum.SharedReportingBankData
