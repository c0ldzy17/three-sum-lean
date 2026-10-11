import Submission.ThreeSum.SharedReportingBankResourceBoundsQueryScales
import Submission.ThreeSum.LightWantedDecode
import Submission.ThreeSum.BandRawA

/-!
# Size-only magnitudes for physical wanted indices

The left index includes the lift and the retained A-incidence position.
The right index selects an original output record, including its occurrence
identity. Neither bound depends on the magnitude of the input integers.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Scales GlobalEncoding LocalCoverBounds OutputDecodeRecords
open SharedReportingBankLayout

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

def wantedDecodeV (n : ℕ) : ℕ := 2^(8192*(inputBits n+1))

theorem input_le_magnitude (n : ℕ) : n ≤ magnitude n := by
  have hn : n ≤ 2^(inputBits n+1) := by
    simpa only [inputBits,Nat.log2_eq_log_two,Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by decide : 1<2) n).le
  exact hn.trans (Nat.pow_le_pow_right (by decide) (by omega))

theorem wanted_decode_v_eq (n : ℕ) : wantedDecodeV n=(magnitude n)^4 := by
  unfold wantedDecodeV magnitude
  rw [← pow_mul]
  congr 1
  omega

theorem local_layer_le_magnitude (n : ℕ) : layerCount (half n) ≤ magnitude n := by
  have hc : layerCount (half n) ≤ 2^(512*half n) := Nat.choose_le_two_pow _ _
  exact hc.trans ((Nat.pow_le_pow_right (by decide) (by omega)).trans (components n).localPower)

theorem local_schedule_le_magnitude (n : ℕ) : scheduleSize (half n) ≤ magnitude n := by
  have hh := (primitive_bounds n).1
  exact (LightLocalCoverMagnitude.rounds_bound (half n)).trans
    (Nat.pow_le_pow_right (by decide) (by omega))

theorem output_count_le_magnitude (n : ℕ) :
    localCount (half n)^(blocks n) ≤ (magnitude n)^2 := by
  have hs := (components n).occurrence
  have hp : (layerCount (half n))^(blocks n) ≤ magnitude n := by
    calc
      _ ≤ (2^(512*half n))^(blocks n) := Nat.pow_le_pow_left (Nat.choose_le_two_pow _ _) _
      _ = 2^(width (half n) (blocks n)) := by
        rw [← pow_mul]
        congr 1
        unfold width localWidth
        ring
      _ ≤ magnitude n := (Nat.pow_le_pow_right (by decide) (by omega)).trans (components n).widthPower
  simpa only [localCount,mul_pow,pow_two,LightBlockSourceCatalog.count] using Nat.mul_le_mul hs hp

theorem incidence_count_le_magnitude {n nA N : ℕ} {rs : List BandCandidateRows.Record}
    (hrs : rs.length ≤ 3*n^2) (hN : N ≤ (BandRawA.items nA (BandScales.bandSize n) rs).length) :
    N ≤ 3*(magnitude n)^3 := by
  have hcount := BandRawA.items_length_le nA (BandScales.bandSize n) rs
  have hg := band_le_magnitude n
  have hn := input_le_magnitude n
  have hnum := Nat.mul_le_mul hg (hrs.trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hn 2)))
  calc
    N ≤ BandScales.bandSize n*rs.length := hN.trans hcount
    _ ≤ magnitude n*(3*(magnitude n)^2) := hnum
    _ = _ := by ring

theorem wanted_left_index_le {n N i : ℕ}
    (hN : N ≤ 3*(magnitude n)^3) (hi : i<3*N) : i≤wantedDecodeV n := by
  have h9 : 9≤magnitude n := by have hh := linear_le_magnitude n; omega
  have hh : 9*(magnitude n)^3 ≤ (magnitude n)^4 := by
    calc
      _ ≤ magnitude n*(magnitude n)^3 := Nat.mul_le_mul_right _ h9
      _ = _ := by ring
  rw [wanted_decode_v_eq]
  omega

theorem wanted_right_index_le {n j : ℕ}
    (hj : j<localCount (half n)^(blocks n)) : j≤wantedDecodeV n := by
  rw [wanted_decode_v_eq]
  exact hj.le.trans ((output_count_le_magnitude n).trans
    (Nat.pow_le_pow_right (components n).positive (by decide)))

theorem wanted_decode_log_le (n : ℕ) :
    Nat.log 2 (wantedDecodeV n+1) ≤ 8192*(inputBits n+1)+1 := by
  have hp : 1≤wantedDecodeV n := Nat.one_le_pow _ _ (by decide)
  have hb : wantedDecodeV n+1 ≤ 2^(8192*(inputBits n+1)+1) := by
    unfold wantedDecodeV at *
    rw [pow_succ]
    omega
  exact (Nat.log_mono_right (b := 2) hb).trans (by simp)

theorem wanted_decoder_word_le {n N : ℕ} (hN : N ≤ 3*(magnitude n)^3) :
    LightWantedDecode.word (wantedDecodeV n) N (half n) (blocks n) ≤
      1000*(magnitude n+1)^4 := by
  have H := components n
  have hs := local_schedule_le_magnitude n
  have hl := local_layer_le_magnitude n
  have hsl := Nat.mul_le_mul hs hl
  have hJ := H.blocksBound
  have ho := H.occurrence
  have hp : 2^(512*half n)≤magnitude n :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans H.localPower
  have hM : magnitude n≤(magnitude n+1)^4 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  have hM2 : (magnitude n)^2≤(magnitude n+1)^4 :=
    (Nat.pow_le_pow_left (Nat.le_succ _) 2).trans (Nat.pow_le_pow_right (by omega) (by decide))
  have hM3 : (magnitude n)^3≤(magnitude n+1)^4 :=
    (Nat.pow_le_pow_left (Nat.le_succ _) 3).trans (Nat.pow_le_pow_right (by omega) (by decide))
  have hM4 : (magnitude n)^4≤(magnitude n+1)^4 := Nat.pow_le_pow_left (Nat.le_succ _) 4
  have h1 : 1≤(magnitude n+1)^4 := Nat.one_le_pow _ _ (by omega)
  rw [wanted_decode_v_eq]
  unfold LightWantedDecode.word LightOutputDecode.word
  change (scheduleSize (half n))^(blocks n)≤magnitude n at ho
  simp only [pow_two] at hsl hM2
  omega

end ThreeSum.SharedReportingBankResourceBounds
