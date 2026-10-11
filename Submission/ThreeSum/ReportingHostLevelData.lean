import Submission.ThreeSum.LightReportingCatalogQuery
import Submission.ThreeSum.LightReportingFrontierStep

/-!
# Exact retained catalog and scratch interfaces for the level loop

These records collect the memory assertions already produced by the actual
prefix-catalog constructor. They contain no assumed query procedure. The
query adapter below invokes the existing closed, verified catalog program.
-/

namespace ThreeSum.ReportingHostLevelData

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

structure Catalog where
  t : ℕ
  boxCut : ℕ
  boxBase : ℕ
  indexBase : ℕ
  ptrBase : ℕ

/-- The fields actually consumed by the level machine, including the computed
prefix count. The box base remains a semantic ownership bound. -/
def Catalog.record (D : Catalog) (h k : ℕ) : List ℕ :=
  [D.t,D.boxCut,D.indexBase,D.ptrBase,count h k]

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

structure Sources {h J : ℕ} (μ : ℕ→ℤ) (pMod shift : ℤ) (B : Finset β) (C : Finset γ)
    (b : β→ℤ) (c : γ→ℤ) (q : GlobalOutput h J) (baseL baseR : ℕ) : Prop where
  left : LightZetaStages.StoredThrough μ baseL (sourceCut h J) (leftSource pMod B b q) (width h J)
  right : LightZetaStages.StoredThrough μ baseR (sourceCut h J) (rightSource pMod shift C c q) (width h J)

structure Stored {h J k : ℕ} (μ : ℕ→ℤ) (D : Catalog) (hk : k≤J)
    (pMod shift : ℤ) (B : Finset β) (C : Finset γ) (b : β→ℤ) (c : γ→ℤ)
    (q : GlobalOutput h J) : Prop where
  index : ∃ S : List ℤ, Seg μ D.indexBase S ∧
    S.Perm (ReportingHostPackedCatalog.codes (ReportingHostPackedCatalog.prefixKey h J k) (count h k)) ∧
    S.Pairwise (· ≤ ·)
  pointers : SegN μ D.ptrBase (List.ofFn fun i : Fin (count h k) =>
    D.boxBase+i.val*stride (suffixStage J (512*h) k) D.boxCut)
  boxes : ∀ i<count h k, LightBoxStages.StoredThrough μ
    (D.boxBase+i*stride (suffixStage J (512*h) k) D.boxCut) D.boxCut
    (leafWeight (block_fit hk) (leftSource pMod B b q) (rightSource pMod shift C c q)
      (suffixStage J (512*h) k) (preL h J k i) (preR h J k i)) (suffixStage J (512*h) k)

structure Bounds (h J k : ℕ) (D : Catalog) (baseL baseR stop : ℕ) : Prop where
  left : baseL+(width h J+1)*downsetCap (width h J) (sourceCut h J)≤stop
  right : baseR+(width h J+1)*downsetCap (width h J) (sourceCut h J)≤stop
  index : D.indexBase+count h k≤stop
  pointers : D.ptrBase+count h k≤stop
  boxes : D.boxBase+count h k*stride (suffixStage J (512*h) k) D.boxCut≤stop

structure Scratch (lim : Limits) (h J k : ℕ) (D : Catalog) (bCard cCard maskBase work : ℕ) : Prop where
  masks : maskBase+LightSparseQuery.queryItems (residualSize h J k) D.t≤work
  space : work+1+tableSize (width h J)+(width h J+1)≤lim.space
  powers : work+(2*width h J+2)≤lim.space
  emod : work+(Nat.log 2 (LightReportingCatalogLookup.valueBound (width h J) (count h k)+1)+2)≤lim.space
  word : (((width h J+1)*2^(width h J+1) : ℕ) : ℤ)≤lim.word
  lookup : (LightReportingCatalogLookup.word (width h J) (count h k) : ℤ)≤lim.word
  values : (LightSparseQuery.magnitudeBound (suffixStage J (512*h) k) (suffixStage J (512*h) k)
    (residualSize h J k) D.t bCard cCard : ℤ)≤lim.word
  t : D.t≤residualSize h J k+1
  cut : D.boxCut≤residualSize h J k
  flags : residualSize h J k-D.t≤D.boxCut

theorem Bounds.mono {h J k baseL baseR stop stop' : ℕ} {D : Catalog}
    (H : Bounds h J k D baseL baseR stop) (hle : stop≤stop') :
    Bounds h J k D baseL baseR stop' :=
  ⟨H.left.trans hle,H.right.trans hle,H.index.trans hle,H.pointers.trans hle,H.boxes.trans hle⟩

theorem Sources.of_kept {h J k baseL baseR stop : ℕ} {μ ν : ℕ→ℤ} {D : Catalog}
    {pMod shift : ℤ} {B : Finset β} {C : Finset γ} {b : β→ℤ} {c : γ→ℤ} {q : GlobalOutput h J}
    (H : Sources μ pMod shift B C b c q baseL baseR) (HB : Bounds h J k D baseL baseR stop)
    (hkeep : Kept μ ν stop) : Sources ν pMod shift B C b c q baseL baseR := by
  constructor
  · exact LightSignedLeafBatch.storedThrough_of_on H.left
      (by intro i _ hi; exact hkeep i (hi.trans_le HB.left))
  · exact LightSignedLeafBatch.storedThrough_of_on H.right
      (by intro i _ hi; exact hkeep i (hi.trans_le HB.right))

theorem Stored.of_kept {h J k baseL baseR stop : ℕ} {μ ν : ℕ→ℤ} {D : Catalog} {hk : k≤J}
    {pMod shift : ℤ} {B : Finset β} {C : Finset γ} {b : β→ℤ} {c : γ→ℤ} {q : GlobalOutput h J}
    (H : Stored μ D hk pMod shift B C b c q) (HB : Bounds h J k D baseL baseR stop)
    (hkeep : Kept μ ν stop) : Stored ν D hk pMod shift B C b c q := by
  obtain ⟨S,hs,hperm,hsort⟩ := H.index
  have hlen : S.length=count h k := hperm.length_eq.trans (ReportingHostPackedCatalog.codes_length _ _)
  constructor
  · refine ⟨S,?_,hperm,hsort⟩
    intro i hi
    exact (hkeep _ (by rw [hlen] at hi; have hh:=HB.index; omega)).trans (hs i hi)
  · intro i hi
    have hi' : i<count h k := by simpa only [List.length_map,List.length_ofFn] using hi
    exact (hkeep _ (by have hh:=HB.pointers; omega)).trans (H.pointers i hi)
  · intro i hi
    exact ReportingHostQueryBounds.boxStored_of_on (H.boxes i hi) (by
      intro u _ hu
      exact hkeep u (hu.trans_le (ReportingHostCatalogSelection.selected_box_end hi HB.boxes)))

theorem query_meets {lim : Limits} {μ : ℕ→ℤ} {h J k baseL baseR maskBase work depth : ℕ}
    {D : Catalog} (hk : k≤J) (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ) (w : Wanted h J α)
    (pre : List (Finset (Fin (512*h)))) (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1∈A ∧ globalModulus h J ∣ (a w.1%pMod+lift w.2.1*pMod+shift)-globalKey w.2.2)
    (hw : (lim.space : ℤ)≤lim.word)
    (HS : Sources μ pMod shift B C b c w.2.2 baseL baseR)
    (HC : Stored μ D hk pMod shift B C b c w.2.2)
    (HB : Bounds h J k D baseL baseR maskBase)
    (HW : Scratch lim h J k D B.card C.card maskBase work)
    (hd : depth+2*width h J+12≤lim.depth) :
    Meets lim LightReportingCatalogQuery.program 35 depth
      [width h J,sourceCut h J,suffixStage J (512*h) k,k*h,
        subsetMask (leftPrefix k (prefixRows (J := J) pre)),k*h,
        subsetMask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) pre)),
        suffixStage J (512*h) k,k*(512*h),residualSize h J k,subsetMask (querySet k (outputRows w.2.2)),
        D.t,baseL,baseR,D.boxCut,D.indexBase,D.ptrBase,count h k,maskBase,work]
      μ (LightReportingCatalogQuery.time h J k D.t)
      (fun r ν => r=(prefixQuery (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k pre : ℤ) ∧
        KeptBut μ ν work maskBase (LightSparseQuery.queryItems (residualSize h J k) D.t)) :=
  LightReportingCatalogQuery.program_meets pMod shift A B C a b c w pre hk hp hkey hw
    HB.left HB.right HB.index HB.pointers HB.boxes HW.masks HW.space HW.powers HW.emod
    HW.word HW.lookup HW.values HW.t HW.cut HW.flags HS.left HS.right HC.index HC.pointers HC.boxes hd

end ThreeSum.ReportingHostLevelData
