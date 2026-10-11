import Submission.ThreeSum.EncodedColorStageCosts
import Submission.ThreeSum.LightBandRawAResourcesScales
import Submission.ThreeSum.LightLocalCoverInitResources

/-! # A proved polynomial scale for the selected-color program's dimensions -/

namespace ThreeSum.EncodedColorResources

open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open Filter

set_option maxHeartbeats 2200000
set_option maxRecDepth 13000

def half (n : ℕ) : ℕ := microHalf (inputBits n)
def blocks (n : ℕ) : ℕ := blockCount (inputBits n)
def width (n : ℕ) : ℕ := blocks n*(512*half n)
def localEnvelope (n : ℕ) : ℕ := LightLocalCoverInitResources.envelope (half n)
def scale (n : ℕ) : ℕ := SharedReportingBankResourceBounds.magnitude n+localEnvelope n+
  maxMod n+primeWindow n+n+100

theorem scale_bounds (n : ℕ) : 100 ≤ scale n ∧ n+1 ≤ scale n ∧
    SharedReportingBankResourceBounds.magnitude n ≤ scale n ∧ localEnvelope n ≤ scale n ∧
    maxMod n ≤ scale n ∧ primeWindow n ≤ scale n := by
  unfold scale
  omega

theorem local_bounds (n : ℕ) : LightLocalCoverMagnitude.Bounds (half n) (scale n) := by
  have hm : LightLocalCoverMagnitude.magnitude (half n) ≤ localEnvelope n := by
    unfold LightLocalCoverMagnitude.magnitude localEnvelope LightLocalCoverInitResources.envelope
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by decide : 600000 ≤ 5000000))
  have hs := hm.trans (scale_bounds n).2.2.2.1
  have H := LightLocalCoverMagnitude.bounds (half n)
  exact ⟨H.positive.trans hs,H.width.trans hs,H.vertices.trans hs,H.prime.trans hs,
    H.cap.trans hs,H.candidates.trans hs,H.rounds.trans hs,H.decodePower.trans hs,H.maskPower.trans hs⟩

theorem dimensions (n : ℕ) : width n+1 ≤ scale n ∧ blocks n+1 ≤ scale n ∧
    mu n+1 ≤ scale n ∧ bandSize n ≤ scale n ∧ radix n ≤ scale n := by
  have H := SharedReportingBankResourceBounds.components n
  have hm := (scale_bounds n).2.2.1
  have hw : width n+1 ≤ scale n := H.widthBound.trans hm
  have hj : blocks n+1 ≤ scale n := H.blocksBound.trans hm
  have ht := H.switchBase.trans hm
  rw [show 2*SharedReportingBankResourceBounds.half n*SharedReportingBankResourceBounds.blocks n=mu n from
    BlockSourceSharing.cutoff_eq n] at ht
  have hg := (SharedReportingBankResourceBounds.band_le_magnitude n).trans hm
  have hy := primeWindow_ge_two n
  have hr : radix n ≤ maxMod n := by
    unfold maxMod
    exact Nat.le_mul_of_pos_right _ (by positivity)
  exact ⟨hw,hj,by omega,hg,hr.trans (scale_bounds n).2.2.2.2.1⟩

theorem powers (n : ℕ) : 2^(width n+1) ≤ scale n ∧
    LightBlockSourceCatalog.count (half n) (blocks n) ≤ scale n ∧
    localPrime (half n)^(blocks n)*localPrime (half n) ≤ scale n ∧
    2^(blocks n) ≤ scale n := by
  have H := SharedReportingBankResourceBounds.components n
  have hm := (scale_bounds n).2.2.1
  refine ⟨H.widthPower.trans hm,H.occurrence.trans hm,H.primePower.trans hm,?_⟩
  have htwo : (2 : ℕ) ≤ 2^(512*half n)+1 := by have hh := Nat.two_pow_pos (512*half n); omega
  exact (Nat.pow_le_pow_left htwo (blocks n)).trans (H.radixPower.trans hm)

theorem modulus_le (n : ℕ) : BlockSourceEncoding.modulus (half n) (blocks n) ≤ scale n := by
  exact (Nat.le_mul_of_pos_right _ (localPrime_pos (half n))).trans (powers n).2.2.1

theorem endpoint_le (n : ℕ) : LightBlockSourceBuild.endpointBound (half n) (blocks n) ≤ (scale n)^2 := by
  have hw : width n ≤ scale n := by have hh := (dimensions n).1; omega
  have hh := Nat.mul_le_mul hw (powers n).2.2.1
  simpa only [LightBlockSourceBuild.endpointBound,width,BlockSourceEncoding.modulus,pow_two] using hh

theorem radix_power_le (n : ℕ) : (localPrime (half n)+1)^(blocks n) ≤ (scale n)^2 := by
  have hp := localPrime_pos (half n)
  have hmod := modulus_le n
  calc
    _ ≤ (2*localPrime (half n))^(blocks n) := Nat.pow_le_pow_left (by omega) _
    _ = 2^(blocks n)*localPrime (half n)^(blocks n) := mul_pow _ _ _
    _ ≤ scale n*scale n := Nat.mul_le_mul (powers n).2.2.2 hmod
    _ = _ := by ring

theorem schedule_power_le (n : ℕ) : (scheduleSize (half n)+1)^(blocks n+1) ≤ 2*(scale n)^3 := by
  have hS : 1 ≤ scheduleSize (half n) := by change 0 < scheduleSize (half n); unfold scheduleSize LocalHashMoments.scheduleLength; positivity
  have hrow : scheduleSize (half n) ≤ scale n := by have h := (local_bounds n).rounds; omega
  have hocc : scheduleSize (half n)^(blocks n) ≤ scale n := (powers n).2.1
  calc
    _ ≤ (2*scheduleSize (half n))^(blocks n+1) := Nat.pow_le_pow_left (by omega) _
    _ = 2*(2^(blocks n)*scheduleSize (half n)^(blocks n)*scheduleSize (half n)) := by
      rw [mul_pow,pow_succ,pow_succ]
      ring
    _ ≤ 2*(scale n*scale n*scale n) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul (Nat.mul_le_mul (powers n).2.2.2 hocc) hrow)
    _ = _ := by ring

theorem layer_le (n : ℕ) : outputCount (512*half n) (half n) ≤ scale n := by
  have hh : outputCount (512*half n) (half n) ≤ 2^(512*half n) := Nat.choose_le_two_pow _ _
  have hp : 2^(512*half n) ≤ scale n := by have h := (local_bounds n).maskPower; have hh := Nat.two_pow_pos (512*half n); rw [pow_succ] at h; omega
  exact hh.trans hp

theorem totalKeys_le (n : ℕ) : LightGuardedWanted.totalKeys (half n) (blocks n) ≤ (scale n)^2 := by
  have hq : outputCount (512*half n) (half n)^(blocks n) ≤ scale n := by
    calc
      _ ≤ (2^(512*half n))^(blocks n) := Nat.pow_le_pow_left (Nat.choose_le_two_pow _ _) _
      _ = 2^(width n) := by unfold width; rw [← pow_mul]; congr 1; ring
      _ ≤ 2^(width n+1) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ scale n := (powers n).1
  unfold LightGuardedWanted.totalKeys LightGlobalKeys.localCount
  rw [mul_pow]
  exact (Nat.mul_le_mul (powers n).2.1 hq).trans_eq (pow_two _).symm

theorem keyBound_le (n : ℕ) : LightGuardedWanted.keyBound (maxMod n) (half n) (blocks n) ≤ 3*(scale n)^4 := by
  have hP := (scale_bounds n).2.2.2.2.1
  have hL : 512*half n ≤ scale n := by have h := (local_bounds n).width; omega
  have hp : localPrime (half n) ≤ scale n := by have h := (local_bounds n).prime; omega
  have hm := Nat.mul_le_mul (Nat.mul_le_mul hL hp) (radix_power_le n)
  have hs4 : scale n ≤ (scale n)^4 := Nat.le_self_pow (by decide) _
  unfold LightGuardedWanted.keyBound
  nlinarith only [hm,hP,hs4]

noncomputable section

theorem localEnvelope_powerBound : PowerBound localEnvelope 0 := by
  refine ArithmeticStageBounds.powerBound_mono (g := localSearch 5000000) ?_ ?_
  · intro d hd
    simpa only [zero_add] using localSearch_subpolynomial 5000000 hd
  · filter_upwards [(microHalf_tendsto_atTop.comp inputBits_tendsto_atTop).eventually
      (eventually_ge_atTop 1)] with n hn
    exact LightLocalCoverInitResources.envelope_le_search hn

theorem scale_powerBound : PowerBound scale 2048 := by
  have hl := localEnvelope_powerBound.mono_exponent (by norm_num : (0 : ℝ) ≤ 2048)
  have hp := maxMod_powerBound.mono_exponent (show (Parameters.E+1/2)/5 ≤ (2048 : ℝ) by
    have hh := Parameters.E_bounds.2; linarith)
  have hy := window_powerBound.mono_exponent (by norm_num : (0 : ℝ) ≤ 2048)
  have hn := identity_powerBound.mono_exponent (by norm_num : (1 : ℝ) ≤ 2048)
  have hc := (PowerBound.const 100).mono_exponent (by norm_num : (0 : ℝ) ≤ 2048)
  exact ((((SharedReportingBankResourceBounds.magnitude_powerBound.add_same hl).add_same hp).add_same hy).add_same hn).add_same hc

end
end ThreeSum.EncodedColorResources
