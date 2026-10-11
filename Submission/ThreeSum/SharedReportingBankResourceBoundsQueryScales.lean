import Submission.ThreeSum.SharedReportingBankResourceBoundsQuery

/-! # Polynomial resources for every wanted query into the shared bank -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light StageBounds SharedReportingBankLayout

set_option maxHeartbeats 1600000
set_option maxRecDepth 12000

def queryEnvelope (n : ℕ) : ℕ := 100*(magnitude n+1)^6

def queryNeed (n _U : ℕ) : Light.Need :=
  ⟨queryWord (half n) (blocks n) (BandScales.bandSize n),
    queryMaskSpan (half n) (blocks n)+queryWorkSpan (half n) (blocks n),
    2*width (half n) (blocks n)+12⟩

theorem query_word_le (n : ℕ) :
    queryWord (half n) (blocks n) (BandScales.bandSize n) ≤ queryEnvelope n := by
  have H := components n
  have hW := H.widthBound
  have hWP := H.widthPower
  have hIP := H.indexPower
  have hP : 2^(width (half n) (blocks n)) ≤ magnitude n :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans hWP
  have hG := band_le_magnitude n
  have hwidth : (width (half n) (blocks n)+1)*2^(width (half n) (blocks n)+1) ≤
      (magnitude n)^2 := by
    simpa only [pow_two] using Nat.mul_le_mul hW hWP
  have hvalue : LightReportingCatalogLookup.valueBound (width (half n) (blocks n))
      (2^(2*width (half n) (blocks n))) ≤ (magnitude n+1)^2 := by
    have hh := Nat.mul_le_mul (hIP.trans (Nat.le_succ _)) (Nat.add_le_add_right hIP 1)
    simpa only [LightReportingCatalogLookup.valueBound,pow_two] using hh
  have hfour : 2^(2*width (half n) (blocks n)+2) ≤ 4*magnitude n := by
    calc
      _ = 4*2^(2*width (half n) (blocks n)) := by rw [pow_add]; norm_num; ring
      _ ≤ _ := Nat.mul_le_mul_left 4 hIP
  have hlookup : LightReportingCatalogLookup.word (width (half n) (blocks n))
      (2^(2*width (half n) (blocks n))) ≤ 4*(magnitude n+1)^2+10*magnitude n+20 := by
    unfold LightReportingCatalogLookup.word
    omega
  have hvalues : (2^(width (half n) (blocks n))+1)*
      (2^(width (half n) (blocks n))*
        ((2^(width (half n) (blocks n))*BandScales.bandSize n)*
         (2^(width (half n) (blocks n))*BandScales.bandSize n))) ≤ (magnitude n+1)^6 := by
    have hp := hP.trans (Nat.le_succ _)
    have hg := hG.trans (Nat.le_succ _)
    have hh := Nat.mul_le_mul (Nat.add_le_add_right hP 1)
      (Nat.mul_le_mul hp (Nat.mul_le_mul (Nat.mul_le_mul hp hg) (Nat.mul_le_mul hp hg)))
    calc
      _ ≤ (magnitude n+1)*((magnitude n+1)*
          (((magnitude n+1)*(magnitude n+1))*((magnitude n+1)*(magnitude n+1)))) := hh
      _ = _ := by ring
  have h1 : 1 ≤ (magnitude n+1)^6 := Nat.one_le_pow _ _ (by omega)
  have hm : magnitude n ≤ (magnitude n+1)^6 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  have h2 : (magnitude n+1)^2 ≤ (magnitude n+1)^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have hm2 : (magnitude n)^2 ≤ (magnitude n+1)^6 :=
    (Nat.pow_le_pow_left (Nat.le_succ _) 2).trans h2
  unfold queryWord queryEnvelope
  omega

theorem query_cells_le (n : ℕ) :
    queryMaskSpan (half n) (blocks n)+queryWorkSpan (half n) (blocks n) ≤ queryEnvelope n := by
  have H := components n
  have hW := H.widthBound
  have hp : 2^(width (half n) (blocks n)) ≤ magnitude n :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans H.widthPower
  have hquad := Nat.pow_le_pow_left hW 2
  have h1 : 1 ≤ (magnitude n+1)^6 := Nat.one_le_pow _ _ (by omega)
  have hm : magnitude n ≤ (magnitude n+1)^6 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  have hm2 : (magnitude n)^2 ≤ (magnitude n+1)^6 :=
    (Nat.pow_le_pow_left (Nat.le_succ _) 2).trans (Nat.pow_le_pow_right (by omega) (by decide))
  unfold queryMaskSpan queryWorkSpan queryEnvelope
  omega

theorem query_depth_le (n : ℕ) : 2*width (half n) (blocks n)+12 ≤ queryEnvelope n := by
  have hW := (components n).widthBound
  have h1 : 1 ≤ (magnitude n+1)^6 := Nat.one_le_pow _ _ (by omega)
  have hm : magnitude n ≤ (magnitude n+1)^6 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  unfold queryEnvelope
  omega

noncomputable section

theorem query_envelope_powerBound : PowerBound queryEnvelope 12288 := by
  have hm := magnitude_powerBound.add_same
    ((PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ) ≤ 2048))
  have hh := (PowerBound.const 100).mul (hm.pow 6)
  convert hh using 1 <;> (first | rfl | norm_num [queryEnvelope])

theorem query_poly_need : Light.PolyNeed queryNeed := by
  apply PolynomialResources.polyNeed_of_envelope query_envelope_powerBound 0
  · intro n U; simpa only [queryNeed,pow_zero,mul_one] using query_word_le n
  · intro n U; simpa only [queryNeed,pow_zero,mul_one] using query_cells_le n
  · intro n U; simpa only [queryNeed,pow_zero,mul_one] using query_depth_le n

theorem query_scratch_scales {lim : Limits} {n report NB NC s i j k maskBase work : ℕ}
    (hk : k ≤ LightSwitchDepth.depth (blocks n))
    (hmasks : maskBase+queryMaskSpan (half n) (blocks n) ≤ work)
    (hspace : work+queryWorkSpan (half n) (blocks n) ≤ lim.space)
    (hword : (queryEnvelope n : ℤ) ≤ lim.word) :
    ReportingHostLevelData.Scratch lim (half n) (blocks n) k
      (SharedReportingBankAccess.levelCatalog report (half n) (blocks n)
        NB NC (BandScales.bandSize n) s i j k)
      (BandRawA.finiteBandPositions NB (BandScales.bandSize n) i).card
      (BandRawA.finiteBandPositions NC (BandScales.bandSize n) j).card maskBase work :=
  query_scratch hk hmasks hspace ((Int.ofNat_le.mpr (query_word_le n)).trans hword)

theorem query_scratch_of_ok {lim : Limits} {n U report NB NC s i j k maskBase d : ℕ}
    (hk : k ≤ LightSwitchDepth.depth (blocks n))
    (hok : (queryNeed n U).Ok lim maskBase d) :
    ReportingHostLevelData.Scratch lim (half n) (blocks n) k
      (SharedReportingBankAccess.levelCatalog report (half n) (blocks n)
        NB NC (BandScales.bandSize n) s i j k)
      (BandRawA.finiteBandPositions NB (BandScales.bandSize n) i).card
      (BandRawA.finiteBandPositions NC (BandScales.bandSize n) j).card maskBase
      (maskBase+queryMaskSpan (half n) (blocks n)) :=
  query_scratch hk le_rfl (by simpa only [queryNeed,Nat.add_assoc] using hok.cells) hok.word

theorem query_depth_of_ok {lim : Limits} {n U maskBase d : ℕ}
    (hok : (queryNeed n U).Ok lim maskBase d) :
    d+2*width (half n) (blocks n)+12 ≤ lim.depth := by
  have hh := hok.depth
  change d+(2*width (half n) (blocks n)+12) ≤ lim.depth at hh
  omega

end
end ThreeSum.SharedReportingBankResourceBounds
