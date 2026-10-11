import Submission.ThreeSum.SharedReportingBankResourceBoundsPolynomial
import Submission.ThreeSum.SharedReportingBankAccess

/-!
# Concrete scratch limits for queries into the retained shared catalog bank

One mask span of `2^W` works for every prescribed level. The remaining
workspace is polynomial in W, including the exact packed-key remainder
workspace. Both source cardinalities are bounded independently by the
physical band size, and the switch and cut are the executed bank values.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light SubsetAddress SharedReportingBankLayout

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

def queryMaskSpan (h J : ℕ) : ℕ := 2^(width h J)
def queryWorkSpan (h J : ℕ) : ℕ := (width h J+1)^2+8*(width h J+1)+8
def queryWord (h J g : ℕ) : ℕ :=
  (width h J+1)*2^(width h J+1)+
    LightReportingCatalogLookup.word (width h J) (2^(2*width h J))+
    (2^(width h J)+1)*(2^(width h J)*((2^(width h J)*g)*(2^(width h J)*g)))

theorem query_items_le {c t : ℕ} (ht : t ≤ c) :
    LightSparseQuery.queryItems c t ≤ 2^c := by
  simpa only [LightSparseQuery.queryItems,downsetCap,Nat.min_eq_left ht,layerOffset_succ]
    using downset_le_pow c t

theorem query_lookup_word_mono {W a b : ℕ} (hab : a ≤ b) :
    LightReportingCatalogLookup.word W a ≤ LightReportingCatalogLookup.word W b := by
  have hmul := Nat.mul_le_mul_left (2^(2*W)) (Nat.add_le_add_right hab 1)
  unfold LightReportingCatalogLookup.word LightReportingCatalogLookup.valueBound
  omega

theorem query_lookup_log_le {W N : ℕ} (hN : N ≤ 2^(2*W)) :
    Nat.log 2 (LightReportingCatalogLookup.valueBound W N+1) ≤ 4*W+2 := by
  have hn := LightLocalCoverMagnitude.succ_pow_bound hN
  have hv : LightReportingCatalogLookup.valueBound W N ≤ 2^(4*W+1) := by
    calc
      _ ≤ 2^(2*W)*2^(2*W+1) := Nat.mul_le_mul_left _ hn
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hl := Nat.log_mono_right (b := 2) (LightLocalCoverMagnitude.succ_pow_bound hv)
  rw [Nat.log_pow (by decide)] at hl
  omega

theorem query_band_card_le (n g i : ℕ) : (BandRawA.finiteBandPositions n g i).card ≤ g := by
  rw [← SourceBandFinite.source_eq_finiteBandPositions]
  exact SharedReportingBankSources.source_card_le n g i

theorem query_catalog_parameters {report h J NB NC g s i j k : ℕ}
    (hk : k ≤ LightSwitchDepth.depth J) :
    let D := SharedReportingBankAccess.levelCatalog report h J NB NC g s i j k
    D.t ≤ LightBlockQuery.residualSize h J k ∧
      D.boxCut ≤ LightBlockQuery.residualSize h J k ∧
      LightBlockQuery.residualSize h J k-D.t=D.boxCut := by
  change SharedReportingBankLevels.switch h J k ≤ (J-k)*(2*h) ∧
    SharedReportingBankLevels.boxCut h J k ≤ (J-k)*(2*h) ∧
    (J-k)*(2*h)-SharedReportingBankLevels.switch h J k=SharedReportingBankLevels.boxCut h J k
  rw [show (J-k)*(2*h)=SharedReportingBankLevels.residual h J k by
    unfold SharedReportingBankLevels.residual; ring]
  exact ⟨SharedReportingBankLevels.switch_le hk,SharedReportingBankLevels.boxCut_le h J k,rfl⟩

theorem query_masks_le {report h J NB NC g s i j k : ℕ}
    (hk : k ≤ LightSwitchDepth.depth J) :
    LightSparseQuery.queryItems (LightBlockQuery.residualSize h J k)
      (SharedReportingBankAccess.levelCatalog report h J NB NC g s i j k).t ≤ queryMaskSpan h J := by
  have ht := (query_catalog_parameters (report := report) (NB := NB) (NC := NC)
    (g := g) (s := s) (i := i) (j := j) (h := h) hk).1
  have hv : BlockIndexedQuery.suffixStage J (512*h) k ≤ width h J :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  exact (query_items_le ht).trans (Nat.pow_le_pow_right (by decide)
    (LightReportingSuffixBoxes.residual_le_suffix.trans hv))

theorem query_scratch {lim : Limits} {report h J NB NC g s i j k maskBase work : ℕ}
    (hk : k ≤ LightSwitchDepth.depth J)
    (hmasks : maskBase+queryMaskSpan h J ≤ work)
    (hspace : work+queryWorkSpan h J ≤ lim.space)
    (hword : (queryWord h J g : ℤ) ≤ lim.word) :
    ReportingHostLevelData.Scratch lim h J k
      (SharedReportingBankAccess.levelCatalog report h J NB NC g s i j k)
      (BandRawA.finiteBandPositions NB g i).card
      (BandRawA.finiteBandPositions NC g j).card maskBase work := by
  let D := SharedReportingBankAccess.levelCatalog report h J NB NC g s i j k
  have hpar := query_catalog_parameters (report := report) (NB := NB) (NC := NC)
    (g := g) (s := s) (i := i) (j := j) (h := h) hk
  have hmask := query_masks_le (report := report) (NB := NB) (NC := NC)
    (g := g) (s := s) (i := i) (j := j) (h := h) hk
  have hN := ReportingHostPackedCatalog.prefix_count_le_pow (h := h)
    (SharedReportingBankLevels.level_le hk)
  have hlog := query_lookup_log_le hN
  have hlookup := query_lookup_word_mono (W := width h J) hN
  have hv : BlockIndexedQuery.suffixStage J (512*h) k ≤ width h J :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hv
  have hB := query_band_card_le NB g i
  have hC := query_band_card_le NC g j
  have hvalue : LightSparseQuery.magnitudeBound
      (BlockIndexedQuery.suffixStage J (512*h) k) (BlockIndexedQuery.suffixStage J (512*h) k)
      (LightBlockQuery.residualSize h J k) D.t
      (BandRawA.finiteBandPositions NB g i).card (BandRawA.finiteBandPositions NC g j).card ≤
      (2^(width h J)+1)*(2^(width h J)*((2^(width h J)*g)*(2^(width h J)*g))) :=
    Nat.mul_le_mul (Nat.add_le_add_right hmask 1)
      (Nat.mul_le_mul hp (Nat.mul_le_mul (Nat.mul_le_mul hp hB) (Nat.mul_le_mul hp hC)))
  have budget (x : ℕ) (hx : x ≤ queryWord h J g) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  refine ⟨(Nat.add_le_add_left hmask maskBase).trans hmasks,?_,?_,?_,
    budget _ ?_,budget _ ?_,budget _ ?_,by omega,hpar.2.1,hpar.2.2.le⟩
  · unfold queryWorkSpan at hspace
    unfold LightPascal.tableSize
    dsimp only [SharedReportingBankLayout.width,SharedReportingBankLayout.localWidth,LightBlockQuery.width] at *
    omega
  · unfold queryWorkSpan at hspace
    dsimp only [SharedReportingBankLayout.width,SharedReportingBankLayout.localWidth,LightBlockQuery.width] at *
    omega
  · unfold queryWorkSpan at hspace
    dsimp only [SharedReportingBankLayout.width,SharedReportingBankLayout.localWidth,LightBlockQuery.width] at *
    omega
  · unfold queryWord
    dsimp only [SharedReportingBankLayout.width,SharedReportingBankLayout.localWidth,LightBlockQuery.width] at *
    omega
  · unfold queryWord
    dsimp only [SharedReportingBankLayout.width,SharedReportingBankLayout.localWidth,LightBlockQuery.width] at *
    omega
  · unfold queryWord
    exact hvalue.trans (Nat.le_add_left _ _)

end ThreeSum.SharedReportingBankResourceBounds
