import Submission.ThreeSum.SharedReportingBankResourceBoundsWantedHost

/-! # Word bounds for every physical scan prefix, including later prefixes -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light

theorem wanted_guard_word_of_mass_bound {lim : Limits} {dst n U old mass threshold d : ℕ}
    (hold : old≤3*(magnitude n)^7) (hmass : mass≤3*(magnitude n)^7)
    (hthreshold : threshold≤9*(magnitude n)^8)
    (hok : (wantedNeed n U).Ok lim dst d) :
    ((old+mass+threshold+2 : ℕ) : ℤ)≤lim.word := by
  have h7 := wanted_power_le n 7 10 (by decide)
  have h8 := wanted_power_le n 8 10 (by decide)
  have h1 : 1≤(magnitude n+1)^10 := Nat.one_le_pow _ _ (by omega)
  have hh : old+mass+threshold+2≤wantedEnvelope n := by
    unfold wantedEnvelope
    omega
  exact (Int.ofNat_le.mpr hh).trans (wanted_envelope_word_of_ok hok)

end ThreeSum.SharedReportingBankResourceBounds
