import Submission.ThreeSum.EncodedColorTimeCover

/-!
# Time of the actual balanced wanted-record construction

The emitted-record term retains the proved division by the dense modulus.
The remaining terms scan the original A incidences and global key rows,
construct histograms, and execute the verified correlation/minimum routine.
-/

namespace ThreeSum.EncodedColorTime

open Filter Real Scales BandScales Parameters StageBounds ArithmeticStageBounds
open EncodedColorResources CostLedger ModuloCosts

set_option maxHeartbeats 1800000
set_option maxRecDepth 14000

theorem original_offset_time_le (p NL NR U : ℕ) :
    LightOriginalOffset.time p NL NR U ≤
      3000*roundedPower p+131*(NL+NR)*(Nat.log 2 (U+1)+1)+642 := by
  have ht := LightOriginalOffset.time_bound p NL NR U
  have hc := capacity_le_roundedPower p
  have hl := log_le_roundedPower p
  have hk : LightKaratsuba.time (Nat.clog 2 p) ≤ 2530*roundedPower p := LightKaratsuba.time_le _
  omega

noncomputable section

theorem const_certificate (c : ℕ) : PowerBound (fun _ => c) certificateExponent :=
  (PowerBound.const c).mono_exponent (by norm_num [certificateExponent])

theorem raw_keys_time_powerBound (k : ℕ) :
    PowerBound (fun n => LightRawAKeys.time (EncodedColorStageCosts.incidenceCap n) (n^k)) (3/2) := by
  have hc := incidence_three_halves.add_same
    ((PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ) ≤ 3/2))
  have hl := sum_zero (input_log_powerBound k) (PowerBound.const 1)
  have hh : PowerBound (fun n => 220*(EncodedColorStageCosts.incidenceCap n+1)*
      (Nat.log 2 (n^k+1)+1)) (3/2) := by
    simpa only [zero_add,add_zero] using ((PowerBound.const 220).mul hc).mul hl
  exact powerBound_mono hh (Eventually.of_forall fun n => LightRawAKeys.time_bound _ _)

theorem rounded_radix_powerBound :
    PowerBound (fun n => roundedPower (radix n)) ((8/5)*((E+1/2)/5)) := by
  apply powerBound_of_fifth (PowerBound.of_rate radix_log_ratio_tendsto)
  intro n
  simpa only [show (2 : ℕ)^8=256 by norm_num] using roundedPower_fifth (radix_pos n)

theorem rounded_radix_certificate :
    PowerBound (fun n => roundedPower (radix n)) certificateExponent :=
  rounded_radix_powerBound.mono_exponent (by
    have h := E_bounds.2
    unfold certificateExponent
    linarith)

theorem left_keys_certificate :
    PowerBound (fun n => 3*EncodedColorStageCosts.incidenceCap n) certificateExponent := by
  simpa only [zero_add] using (PowerBound.const 3).mul incidence_certificate

theorem original_offset_time_certificate :
    PowerBound (fun n => LightOriginalOffset.time (radix n) (3*EncodedColorStageCosts.incidenceCap n)
      (LightGuardedWanted.totalKeys (half n) (blocks n))
      (LightGuardedWanted.keyBound (maxMod n) (half n) (blocks n))) certificateExponent := by
  have hcount := left_keys_certificate.add_same keys_certificate
  have hlog := sum_zero key_log_powerBound (PowerBound.const 1)
  have h1 : PowerBound (fun n => 3000*roundedPower (radix n)) certificateExponent := by
    simpa only [zero_add] using (PowerBound.const 3000).mul rounded_radix_certificate
  have h2 : PowerBound (fun n => 131*(3*EncodedColorStageCosts.incidenceCap n+
      LightGuardedWanted.totalKeys (half n) (blocks n))*
      (Nat.log 2 (LightGuardedWanted.keyBound (maxMod n) (half n) (blocks n)+1)+1))
      certificateExponent := by
    simpa only [zero_add,add_zero] using ((PowerBound.const 131).mul hcount).mul hlog
  exact powerBound_mono ((h1.add_same h2).add_same (const_certificate 642))
    (Eventually.of_forall fun n => original_offset_time_le _ _ _ _)

theorem wanted_scan_time_certificate :
    PowerBound (fun n =>
      2000*(3*EncodedColorStageCosts.incidenceCap n+LightGuardedWanted.totalKeys (half n) (blocks n)+
        radix n+3*EncodedColorStageCosts.incidenceCap n*
          LightGuardedWanted.totalKeys (half n) (blocks n)/radix n+1)*
        (Nat.log 2 (LightGuardedWanted.keyBound (maxMod n) (half n) (blocks n)+1)+
          Nat.log 2 (radix n+radix n+1)+1)) certificateExponent := by
  have hc := (((left_keys_certificate.add_same keys_certificate).add_same radix_certificate).add_same
    wanted_rows_certificate).add_same (const_certificate 1)
  have hl := sum_zero (sum_zero key_log_powerBound radix_log_powerBound) (PowerBound.const 1)
  simpa only [zero_add,add_zero] using ((PowerBound.const 2000).mul hc).mul hl

theorem wanted_time_certificate (k : ℕ) :
    PowerBound (fun n => EncodedColorWantedCosts.time (maxMod n) (radix n) (half n) (blocks n)
      (n^k) (EncodedColorStageCosts.incidenceCap n)) certificateExponent := by
  have hraw := (raw_keys_time_powerBound k).mono_exponent
    (show (3/2 : ℝ) ≤ certificateExponent by norm_num [certificateExponent])
  exact (((cover_time_certificate.add_same hraw).add_same original_offset_time_certificate).add_same
    wanted_scan_time_certificate).add_same (const_certificate 400)

end
end ThreeSum.EncodedColorTime
