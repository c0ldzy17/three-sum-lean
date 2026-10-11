import Submission.ThreeSum.SharedReportingBankResourceBoundsWanted
import Submission.ThreeSum.LightDenseSetup

/-! # Explicit finite scale bounds for reporter words and the dense counter -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Scales Light GlobalEncoding LocalCoverBounds SharedReportingBankLayout
open ReportingHostWantedLayout

set_option maxHeartbeats 2800000
set_option maxRecDepth 14000

theorem wanted_cap_le_magnitude (n : ℕ) : localBucketCap (half n)≤magnitude n := by
  have hh := (primitive_bounds n).1
  exact (LightLocalCoverMagnitude.cap_bound (half n)).trans
    (Nat.pow_le_pow_right (by decide) (by omega))

theorem wanted_representation_cap_le (n : ℕ) :
    representationCap (half n) (blocks n)≤(magnitude n)^2 := by
  obtain ⟨hh,hJ,ht,hW⟩ := primitive_bounds n
  have hp : localBucketCap (half n)^(2*blocks n)≤magnitude n := by
    calc
      _ ≤ (2^(514*half n+6))^(2*blocks n) :=
        Nat.pow_le_pow_left (LightLocalCoverMagnitude.cap_bound (half n)) _
      _ = 2^((514*half n+6)*(2*blocks n)) := by rw [← pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith only [ht,hJ])
  have hs := (components n).occurrence
  change (scheduleSize (half n))^(blocks n)≤magnitude n at hs
  rw [representationCap,mul_pow,← pow_mul]
  simpa only [pow_two] using Nat.mul_le_mul hs hp

theorem wanted_group_le_magnitude (n : ℕ) : groupSize (half n)≤magnitude n := by
  have hc : groupSize (half n)≤2^(2*half n) := Nat.choose_le_two_pow _ _
  exact hc.trans ((Nat.pow_le_pow_right (by decide) (by omega)).trans (components n).localPower)

theorem wanted_modulus_le_magnitude (n : ℕ) :
    BlockSourceEncoding.modulus (half n) (blocks n)≤magnitude n := by
  have hp := (components n).primePower
  exact (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero
    (LocalCoverBounds.localPrime_prime (half n)).ne_zero)).trans hp

theorem wanted_endpoint_le_magnitude (n : ℕ) :
    LightBlockSourceBuild.endpointBound (half n) (blocks n)≤(magnitude n)^2 := by
  have H := components n
  have hW : width (half n) (blocks n)≤magnitude n := by have hh := H.widthBound; omega
  simpa only [LightBlockSourceBuild.endpointBound,width,localWidth,pow_two] using
    Nat.mul_le_mul hW H.primePower

theorem wanted_terminal_word_le (n : ℕ) :
    LightReportingTerminal.word (half n) (blocks n)≤100*(magnitude n+1)^2 := by
  have H := components n
  have hL := H.localWidthBound
  have hW := H.widthBound
  have hp := H.prime
  have hp1 : localPrime (half n)^(blocks n+1)≤magnitude n := by
    simpa only [pow_succ] using H.primePower
  have hpp := H.primePower
  have hwp := H.widthPower
  have hc := wanted_cap_le_magnitude n
  have he := wanted_endpoint_le_magnitude n
  have hm := wanted_modulus_le_magnitude n
  have hv : (512*half n).choose (half n)≤magnitude n :=
    (Nat.choose_le_two_pow _ _).trans
      ((Nat.pow_le_pow_right (by decide) (by omega)).trans H.localPower)
  have hhash := Nat.mul_le_mul hp1 (Nat.add_le_add_right hp 1)
  have hendpoint := Nat.mul_le_mul hW hpp
  have hrow := Nat.mul_le_mul hL (Nat.add_le_add_right hp 1)
  have hLP := Nat.mul_le_mul (show 512*half n≤magnitude n by omega) hp
  unfold LightReportingTerminal.word LightReportingTerminalPrepared.word
    LightSourcePreparation.word LightBlockSourceHashes.word LightBlockCoefficients.word
    LightOneHot.word LightSourceMaskFlags.word LightSourceRowFlag.word LightSourceRowScan.word
  dsimp only [width,localWidth] at hW hwp hendpoint
  nlinarith only [hL,hW,hp,hwp,hc,he,hm,hv,hhash,hendpoint,hrow,hLP]

theorem wanted_terminal_cells_le (n : ℕ) :
    LightReportingTerminal.space 0 (half n) (blocks n)≤20*(magnitude n+1)^2 := by
  have H := components n
  have hJ := H.blocksBound
  have hW := H.widthBound
  have hL := H.localWidthBound
  have hp := H.prime
  have he := wanted_endpoint_le_magnitude n
  have hlogE := (Nat.log_le_self 2
    (LightBlockSourceBuild.endpointBound (half n) (blocks n)+1)).trans (Nat.add_le_add_right he 1)
  have hLP := Nat.mul_le_mul (show 512*half n≤magnitude n by omega) hp
  have hlogP : Nat.log 2 ((512*half n)*localPrime (half n)+1)≤(magnitude n)^2+1 :=
    (Nat.log_le_self 2 _).trans (Nat.add_le_add_right (by simpa only [pow_two] using hLP) 1)
  have hquad : (width (half n) (blocks n)+1)^2≤(magnitude n)^2 := Nat.pow_le_pow_left hW 2
  have hm : magnitude n≤(magnitude n+1)^2 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  have hm2 : (magnitude n)^2≤(magnitude n+1)^2 := Nat.pow_le_pow_left (Nat.le_succ _) 2
  have h1 : 1≤(magnitude n+1)^2 := Nat.one_le_pow _ _ (by omega)
  unfold LightReportingTerminal.space LightReportingTerminalPrepared.space
    LightSourcePreparation.space LightBlockSourceHashes.space LightSourceMaskFlags.space
    LightPascal.tableSize
  dsimp only [width,localWidth] at hW hquad
  simp only [zero_add,max_le_iff]
  constructor
  · constructor
    · constructor
      · constructor <;> omega
      · constructor <;> omega
    · omega
  · constructor
    · omega
    · omega

theorem wanted_mass_bound_le {n N NB NC : ℕ}
    (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    massBound N NB NC (representationCap (half n) (blocks n))≤3*(magnitude n)^7 := by
  have hb := hB.trans (input_le_magnitude n)
  have hc := hC.trans (input_le_magnitude n)
  have hh := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hN hb) hc)
    (wanted_representation_cap_le n)
  calc
    _ ≤ ((3*(magnitude n)^3)*magnitude n)*magnitude n*(magnitude n)^2 := hh
    _ = _ := by ring

theorem wanted_prime_pool_le (n : ℕ) : LightPrimePool.size (primeWindow n)≤3*magnitude n := by
  have hs := Nat.sqrt_le_self (inputBits n)
  have hw : primeWindow n≤magnitude n :=
    Nat.pow_le_pow_right (by decide) (by dsimp only [windowExponent]; omega)
  exact (LightPrimePool.size_le _).trans (Nat.mul_le_mul_left 3 hw)

theorem wanted_threshold_le {n nA nB nC q : ℕ}
    (A B C : ℕ→ℤ) (rs : List BandCandidateRows.Record) (hrs : rs.length≤3*n^2) :
    representationCap (half n) (blocks n)*
      LightDenseSetup.falseScore (LightPrimePool.prime (primeWindow n))
        (LightPrimePool.size (primeWindow n)) q nA nB nC (BandScales.bandSize n) A B C rs≤
      9*(magnitude n)^8 := by
  rw [LightDenseSetup.falseScore_eq]
  have hs := BandWeightedScore.score_bound (LightPrimePool.prime (primeWindow n))
    (LightPrimePool.size (primeWindow n)) q nA nB nC (BandScales.bandSize n) A B C rs
    (fun i hi => (LightPrimePool.prime_spec hi).1) (fun i hi j hj => LightPrimePool.prime_injective hi hj)
  have hr := hrs.trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (input_le_magnitude n) 2))
  have hh := Nat.mul_le_mul (wanted_representation_cap_le n)
    (Nat.mul_le_mul hr (Nat.mul_le_mul (wanted_prime_pool_le n)
      (Nat.pow_le_pow_left (band_le_magnitude n) 3)))
  calc
    _ ≤ representationCap (half n) (blocks n)*(rs.length*
        (LightPrimePool.size (primeWindow n)*(BandScales.bandSize n)^3)) := Nat.mul_le_mul_left _ hs
    _ ≤ (magnitude n)^2*((3*(magnitude n)^2)*((3*magnitude n)*(magnitude n)^3)) := hh
    _ = _ := by ring

end ThreeSum.SharedReportingBankResourceBounds
