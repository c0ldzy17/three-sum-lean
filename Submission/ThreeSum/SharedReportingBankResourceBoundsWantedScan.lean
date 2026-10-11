import Submission.ThreeSum.SharedReportingBankResourceBoundsWantedRecord

/-! # Polynomial call depth for scanning every physical wanted record

The scan retains the exact word and cell reservations of one wanted
dispatcher. Only its depth includes the number of physical records.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light Scales StageBounds

set_option maxHeartbeats 1700000
set_option maxRecDepth 14000

def wantedScanCount (n : ℕ) : ℕ := 9*(magnitude n)^5

def wantedScanNeed (n U : ℕ) : Light.Need :=
  ⟨(wantedNeed n U).word,(wantedNeed n U).cells,(wantedNeed n U).depth+wantedScanCount n+4⟩

theorem wanted_scan_count_le {n N count : ℕ}
    (hN : N≤3*(magnitude n)^3)
    (hcount : count≤(3*N)*LightGuardedWanted.totalKeys (half n) (blocks n)) :
    count≤wantedScanCount n := by
  have ho : LightGuardedWanted.totalKeys (half n) (blocks n)≤(magnitude n)^2 :=
    output_count_le_magnitude n
  calc
    _ ≤ (3*N)*LightGuardedWanted.totalKeys (half n) (blocks n) := hcount
    _ ≤ (9*(magnitude n)^3)*(magnitude n)^2 := Nat.mul_le_mul (by omega) ho
    _ = wantedScanCount n := by unfold wantedScanCount; ring

theorem wanted_scan_count_envelope (n : ℕ) : wantedScanCount n+4≤wantedEnvelope n := by
  have h5 := wanted_power_le n 5 10 (by decide)
  have h1 : 1≤(magnitude n+1)^10 := Nat.one_le_pow _ _ (by omega)
  unfold wantedScanCount wantedEnvelope
  omega

theorem wanted_scan_step_of_ok {lim : Limits} {n U dst d count : ℕ}
    (hcount : count≤wantedScanCount n) (hok : (wantedScanNeed n U).Ok lim dst d) :
    (wantedNeed n U).Ok lim dst (d+count+4) :=
  hok.mono le_rfl le_rfl (by dsimp only [wantedScanNeed]; omega)

theorem wanted_scan_at_depth_of_ok {lim : Limits} {n U dst d count e : ℕ}
    (hcount : count≤wantedScanCount n) (he : e≤d+count+4)
    (hok : (wantedScanNeed n U).Ok lim dst d) : (wantedNeed n U).Ok lim dst e :=
  (wanted_scan_step_of_ok hcount hok).mono le_rfl le_rfl (by omega)

theorem wanted_scan_count_word {lim : Limits} {n U dst d count : ℕ}
    (hcount : count≤wantedScanCount n) (hok : (wantedScanNeed n U).Ok lim dst d) :
    ((count+4 : ℕ) : ℤ)≤lim.word := by
  have hh := (Nat.add_le_add_right hcount 4).trans (wanted_scan_count_envelope n)
  have hw : (wantedEnvelope n*(U+1) : ℤ)≤lim.word := hok.word
  exact (Int.ofNat_le.mpr (hh.trans (Nat.le_mul_of_pos_right _ (by omega : 0<U+1)))).trans hw

noncomputable section

theorem wanted_scan_poly_need : Light.PolyNeed wantedScanNeed := by
  have he : PowerBound (fun n => 2*wantedEnvelope n) 20480 := by
    simpa only [zero_add] using (PowerBound.const 2).mul wanted_envelope_powerBound
  apply PolynomialResources.polyNeed_of_envelope he 1
  · intro n U
    simp only [wantedScanNeed,wantedNeed,pow_one]
    nlinarith only [Nat.zero_le (wantedEnvelope n*(U+1))]
  · intro n U
    simp only [wantedScanNeed,wantedNeed,pow_one]
    have hh : wantedEnvelope n≤wantedEnvelope n*(U+1) := Nat.le_mul_of_pos_right _ (by omega)
    nlinarith only [hh]
  · intro n U
    simp only [wantedScanNeed,wantedNeed,pow_one]
    have hc := wanted_scan_count_envelope n
    have hh : 2*wantedEnvelope n≤2*wantedEnvelope n*(U+1) := Nat.le_mul_of_pos_right _ (by omega)
    omega

end
end ThreeSum.SharedReportingBankResourceBounds
