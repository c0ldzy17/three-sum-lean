import Submission.ThreeSum.SharedReportingBankResourceBoundsPolynomial

/-! # Executed shared catalogs with proved polynomial limits and exact time -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light

theorem program_meets {lim : Limits} {μ : ℕ → ℤ} {fB fC : ℕ → ℤ}
    {n U controls pairHeader bankHeader free NB NC occ p m d : ℕ} {shift : ℤ}
    (hB : NB ≤ n) (hC : NC ≤ n)
    (Hcontrol : Seg μ controls (SourceControlLayout.values (half n) (blocks n) (2*half n*blocks n)))
    (Hpair : SourceBandPairData.Stored μ fB fC pairHeader NB NC (BandScales.bandSize n) p m shift)
    (Hbank : SourceBandBankData.Stored μ fB fC bankHeader NB NC (BandScales.bandSize n)
      (half n) (blocks n) (2*half n*blocks n) occ (p : ℤ) shift)
    (hcontrol : controls+3 ≤ free) (hpair : pairHeader+8 ≤ free)
    (hocc : occ+LightBlockSourceCatalog.count (half n) (blocks n)*blocks n ≤ bankHeader)
    (hsource : SourceBandBankData.finish bankHeader NB NC (BandScales.bandSize n)
      (half n) (blocks n) (2*half n*blocks n) ≤ free)
    (hok : (need n U).Ok lim free d) :
    Meets lim LightSharedReportingHost.program 74 d
      [half n,blocks n,controls,pairHeader,bankHeader,free] μ (SharedReportingBankCosts.budget n)
      (fun result ν => result=(SharedReportingBankHeader.finish free (half n) (blocks n)
          NB NC (BandScales.bandSize n) : ℤ) ∧
        SharedReportingBankHeader.Stored ν free (half n) (blocks n)
          NB NC (BandScales.bandSize n) fB fC (p : ℤ) shift ∧ Kept μ ν free) :=
  (LightSharedReportingHost.program_meets Hcontrol Hpair Hbank hok.space
    hcontrol hpair hocc hsource (resources_of_ok hB hC hok)).mono_time
      (SharedReportingBankCosts.host_time_le hB hC)

end ThreeSum.SharedReportingBankResourceBounds
