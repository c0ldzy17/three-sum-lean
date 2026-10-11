import Submission.ThreeSum.ReportingHostLevelData
import Submission.ThreeSum.LightReportingCatalogIndex

/-! # Exact retained cells of one shared reporting catalog -/

namespace ThreeSum.SharedReportingBankData

open Light SubsetAddress ReportingHostSuffix ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData

set_option maxHeartbeats 1500000
set_option maxRecDepth 9000

structure Tables {h J k : ℕ} (μ : ℕ → ℤ) (D : Catalog) (hk : k ≤ J)
    (f g : Finset (Fin (J*(512*h))) → ℤ) : Prop where
  index : ∃ S : List ℤ, Seg μ D.indexBase S ∧
    S.Perm (ReportingHostPackedCatalog.codes (ReportingHostPackedCatalog.prefixKey h J k) (count h k)) ∧
    S.Pairwise (· ≤ ·)
  pointers : SegN μ D.ptrBase (List.ofFn fun i : Fin (count h k) =>
    D.boxBase+i.val*stride ((J-k)*(512*h)) D.boxCut)
  boxes : ∀ i < count h k, LightBoxStages.StoredThrough μ
    (D.boxBase+i*stride ((J-k)*(512*h)) D.boxCut) D.boxCut
    (leafWeight (block_fit hk) f g ((J-k)*(512*h)) (preL h J k i) (preR h J k i))
    ((J-k)*(512*h))

structure Entry {h J k : ℕ} (μ : ℕ → ℤ) (record : ℕ) (D : Catalog) (hk : k ≤ J)
    (f g : Finset (Fin (J*(512*h))) → ℤ) : Prop where
  header : SegN μ record (D.record h k)
  tables : Tables μ D hk f g

theorem Tables.of_after {h J k low : ℕ} {μ ν : ℕ → ℤ} {D : Catalog} {hk : k ≤ J}
    {f g : Finset (Fin (J*(512*h))) → ℤ} (H : Tables μ D hk f g)
    (heq : ∀ a, low ≤ a → ν a=μ a)
    (hindex : low ≤ D.indexBase) (hptr : low ≤ D.ptrBase) (hbox : low ≤ D.boxBase) :
    Tables ν D hk f g := by
  obtain ⟨S,hs,hperm,hsort⟩ := H.index
  refine ⟨⟨S,?_,hperm,hsort⟩,?_,?_⟩
  · intro i hi
    exact (heq _ (by omega)).trans (hs i hi)
  · intro i hi
    exact (heq _ (by omega)).trans (H.pointers i hi)
  · intro i hi
    exact ReportingHostQueryBounds.boxStored_of_on (H.boxes i hi)
      (by intro a ha _; exact heq a (by omega))

theorem Tables.of_kept {h J k bound : ℕ} {μ ν : ℕ → ℤ} {D : Catalog} {hk : k ≤ J}
    {f g : Finset (Fin (J*(512*h))) → ℤ} (H : Tables μ D hk f g)
    (heq : Kept μ ν bound) (hindex : D.indexBase+count h k ≤ bound)
    (hptr : D.ptrBase+count h k ≤ bound)
    (hbox : D.boxBase+count h k*stride ((J-k)*(512*h)) D.boxCut ≤ bound) :
    Tables ν D hk f g := by
  obtain ⟨S,hs,hperm,hsort⟩ := H.index
  have hlen : S.length=count h k := hperm.length_eq.trans (ReportingHostPackedCatalog.codes_length _ _)
  refine ⟨⟨S,?_,hperm,hsort⟩,?_,?_⟩
  · intro i hi
    exact (heq _ (by rw [hlen] at hi; omega)).trans (hs i hi)
  · intro i hi
    have hi' : i < count h k := by simpa only [List.length_map,List.length_ofFn] using hi
    exact (heq _ (by omega)).trans (H.pointers i hi)
  · intro i hi
    exact ReportingHostQueryBounds.boxStored_of_on (H.boxes i hi) (by
      intro a _ ha
      exact heq a (ha.trans_le (ReportingHostCatalogSelection.selected_box_end hi hbox)))

theorem Entry.of_kept {h J k record bound : ℕ} {μ ν : ℕ → ℤ} {D : Catalog} {hk : k ≤ J}
    {f g : Finset (Fin (J*(512*h))) → ℤ} (H : Entry μ record D hk f g)
    (heq : Kept μ ν bound) (hrecord : record+5 ≤ bound)
    (hindex : D.indexBase+count h k ≤ bound) (hptr : D.ptrBase+count h k ≤ bound)
    (hbox : D.boxBase+count h k*stride ((J-k)*(512*h)) D.boxCut ≤ bound) :
    Entry ν record D hk f g := by
  refine ⟨?_,H.tables.of_kept heq hindex hptr hbox⟩
  intro i hi
  have hi' : i < 5 := by simpa only [Catalog.record,List.length_map,List.length_cons,List.length_nil] using hi
  exact (heq _ (by omega)).trans (H.header i hi)

theorem Tables.reporting {β γ : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] {h J k : ℕ} {μ : ℕ → ℤ} {D : Catalog} {hk : k ≤ J}
    (p shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (q : GlobalEncoding.GlobalOutput h J)
    (H : Tables μ D hk (BlockIndexedQuery.leftSource p B b q)
      (BlockIndexedQuery.rightSource p shift C c q)) :
    ReportingHostLevelData.Stored μ D hk p shift B C b c q :=
  ⟨H.index,H.pointers,H.boxes⟩

end ThreeSum.SharedReportingBankData
