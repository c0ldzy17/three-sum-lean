import Submission.ThreeSum.SourceFiniteData

/-! # Keep the complete finite source catalog below its exact returned end -/

namespace ThreeSum.SourceFiniteData

open Light

theorem source_ends (base NL NR g h J cut : ℕ) :
    base+3 ≤ LightSourceControlsHost.finish base NL NR g h J cut ∧
    SourceBandPairData.next (LightSourceControlsHost.sourceBase base) NL NR g
      (BlockSourceEncoding.modulus h J) ≤ LightSourceControlsHost.finish base NL NR g h J cut ∧
    LightSourceBandHost.bankHeader (LightSourceControlsHost.sourceBase base) NL NR g h J+5 ≤
      LightSourceControlsHost.finish base NL NR g h J cut := by
  have ho := SourceBandPairData.ordered (LightSourceControlsHost.sourceBase base)
    NL NR g (BlockSourceEncoding.modulus h J)
  unfold LightSourceControlsHost.finish LightSourceBandHost.finish SourceBandBankData.finish
    SourceBandBankLayout.baseAt SourceBandBankData.first LightSourceBandHost.bankHeader
    LightSourceBandHost.occurrenceBase LightSourceControlsHost.sourceBase
  unfold SourceBandPairData.leftBase LightSourceControlsHost.sourceBase at ho
  omega

theorem Stored.of_kept {μ ν : ℕ → ℤ} {base g p h J cut bound : ℕ} {B C : List ℤ} {shift r : ℤ}
    (H : Stored μ base g p h J cut B C shift r)
    (K : Kept μ ν bound)
    (hb : LightSourceControlsHost.finish base B.length C.length g h J cut ≤ bound) :
    Stored ν base g p h J cut B C shift r := by
  obtain ⟨hcontrol,hpair,_⟩ := source_ends base B.length C.length g h J cut
  refine ⟨H.returned,?_,?_,?_⟩
  · exact H.controls.of_kept K (by simpa [SourceControlLayout.values] using hcontrol.trans hb)
  · exact H.buckets.of_kept (BlockSourceEncoding.modulus_pos h J) K (hpair.trans hb)
  · exact H.banks.of_kept K le_rfl hb

end ThreeSum.SourceFiniteData
