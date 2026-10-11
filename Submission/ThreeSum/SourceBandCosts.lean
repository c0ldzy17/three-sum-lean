import Submission.ThreeSum.LightSourceBandSetup
import Submission.ThreeSum.BlockSourceCatalogCosts
import Mathlib.Data.Nat.Choose.Vandermonde

/-! # Finite charge of the actual original-band histogram and bucket catalog -/

namespace ThreeSum.SourceBandCosts

open Scales TrimScales StageBounds CostLedger BandScales LocalCoverBounds

theorem choose_mul_le (L K N M : ℕ) : L.choose K*N.choose M ≤ (L+N).choose (K+M) := by
  rw [Nat.add_choose_eq]
  exact Finset.single_le_sum (f := fun ij : ℕ×ℕ => L.choose ij.1*N.choose ij.2)
    (fun _ _ => Nat.zero_le _) (by simp : (K,M) ∈ Finset.antidiagonal (K+M))

theorem choose_pow_le (L K J : ℕ) : (L.choose K)^J ≤ (J*L).choose (J*K) := by
  induction J with
  | zero => simp
  | succ J ih =>
    calc
      _ = (L.choose K)^J*L.choose K := pow_succ _ _
      _ ≤ (J*L).choose (J*K)*L.choose K := Nat.mul_le_mul_right _ ih
      _ ≤ (J*L+L).choose (J*K+K) := choose_mul_le _ _ _ _
      _ = _ := by simp only [Nat.succ_mul]

theorem typedOutputs_le_fullOutputs (n : ℕ) : typedOutputs n ≤ fullOutputs n := by
  have h := choose_pow_le (256*muZero n) (muZero n) (blockCount (inputBits n))
  have hwidth : blockCount (inputBits n)*(256*muZero n)=256*mu n := by
    unfold mu muZero totalSize
    ring
  have hcut : blockCount (inputBits n)*muZero n=mu n := rfl
  rw [hwidth,hcut] at h
  exact h

theorem four_le_scheduleSize (h : ℕ) : 4 ≤ GlobalEncoding.scheduleSize h := by
  unfold GlobalEncoding.scheduleSize LocalHashMoments.scheduleLength
  calc
    4 ≤ 320 := by decide
    _ ≤ 320*(2*h+1) := Nat.le_mul_of_pos_right _ (by omega)
    _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)

theorem localPrime_le_four_outputs (h : ℕ) : localPrime h ≤ 4*outputCount (512*h) h := by
  have ho : 2^(2*h) ≤ outputCount (512*h) h := by
    by_cases hz : h=0
    · simp [hz,outputCount]
    · exact (concrete_output_gt_pow (by omega)).le
  have hu := localPrime_sq_upper h
  have hm := Nat.mul_le_mul_left (16*outputCount (512*h) h) ho
  nlinarith

theorem modulus_le_global_outputs (h J : ℕ) :
    BlockSourceEncoding.modulus h J ≤ GlobalEncoding.scheduleSize h^J*
      (J*(512*h)).choose (J*(2*h)) := by
  have hl : localPrime h ≤ GlobalEncoding.scheduleSize h*outputCount (512*h) h :=
    (localPrime_le_four_outputs h).trans (Nat.mul_le_mul_right _ (four_le_scheduleSize h))
  have hp := Nat.pow_le_pow_left hl J
  rw [mul_pow] at hp
  unfold BlockSourceEncoding.modulus
  exact hp.trans (Nat.mul_le_mul_left _ (choose_pow_le (512*h) (2*h) J))

theorem modulus_le_tableCount (n : ℕ) :
    BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n)) ≤ tableCount n := by
  have hm := modulus_le_global_outputs (microHalf (inputBits n)) (blockCount (inputBits n))
  have hc : blockCount (inputBits n)*(2*microHalf (inputBits n))=mu n := by
    rw [Nat.mul_comm,BlockSourceSharing.cutoff_eq]
  rw [BlockSourceSharing.width_eq,hc] at hm
  change LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n))*fullOutputs n ≥ _ at hm
  rw [BlockSourceCatalogCosts.count_eq_scheduleCount] at hm
  exact hm

theorem bandSize_le_fullOutputs (n : ℕ) : bandSize n ≤ fullOutputs n := by
  have hb : bandSize n ≤ bandRoot n := by
    apply (ceilDiv_le_iff_le_mul (a := bandDivisor n) (bandDivisor_pos n)).mpr
    exact Nat.le_mul_of_pos_left _ (bandDivisor_pos n)
  have hr : bandRoot n ≤ typedOutputs n := by
    have hs := Nat.sqrt_le_self (typedOutputs n-1)
    have hp := typedOutputs_pos n
    unfold bandRoot rootCeiling
    omega
  exact hb.trans (hr.trans (typedOutputs_le_fullOutputs n))

theorem scheduleCount_pos (n : ℕ) : 0 < scheduleCount n := by
  unfold scheduleCount replicatedHalf
  exact pow_pos (localLength_pos _) _

theorem bands_outputs_le_encoderCount (n : ℕ) : bandCount n*fullOutputs n ≤ encoderCount n := by
  have hs : 1 ≤ scheduleCount n := scheduleCount_pos n
  calc
    _ ≤ bandCount n*scheduleCount n*fullOutputs n := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_right (fullOutputs n) (Nat.mul_le_mul_left (bandCount n) hs)
    _ ≤ 2*(bandCount n*scheduleCount n*fullOutputs n) := Nat.le_mul_of_pos_left _ (by omega)
    _ = _ := by unfold encoderCount; ring

theorem input_le_encoderCount (n : ℕ) : n ≤ encoderCount n := by
  calc
    _ ≤ bandSize n*bandCount n := (bandCount_mul_bounds n).1
    _ ≤ fullOutputs n*bandCount n := Nat.mul_le_mul_right _ (bandSize_le_fullOutputs n)
    _ = bandCount n*fullOutputs n := Nat.mul_comm _ _
    _ ≤ _ := bands_outputs_le_encoderCount n

theorem bands_modulus_le_encoderCount (n : ℕ) :
    bandCount n*BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n)) ≤ encoderCount n := by
  calc
    _ ≤ bandCount n*tableCount n := Nat.mul_le_mul_left _ (modulus_le_tableCount n)
    _ ≤ 2*(bandCount n*tableCount n) := Nat.le_mul_of_pos_left _ (by omega)
    _ = _ := by unfold tableCount encoderCount; ring

theorem bands_le_encoderCount (n : ℕ) : bandCount n ≤ encoderCount n := by
  calc
    _ ≤ bandCount n*BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n)) :=
      Nat.le_mul_of_pos_right _ (BlockSourceEncoding.modulus_pos _ _)
    _ ≤ _ := bands_modulus_le_encoderCount n

theorem size_le_bandCount {N n : ℕ} (hN : N ≤ n) : BandPartition.size N (bandSize n) ≤ bandCount n := by
  apply (BandPartition.size_mono hN).trans
  by_cases hn : n=0
  · simp [hn,BandPartition.size]
  · have hg := bandSize_pos n
    have hb := (bandCount_mul_bounds n).1
    have hb' : n ≤ bandCount n*bandSize n := by simpa only [Nat.mul_comm] using hb
    have hd : (n-1)/bandSize n < bandCount n :=
      (Nat.div_lt_iff_lt_mul hg).mpr (by omega)
    simp only [BandPartition.size,if_neg hn]
    omega

theorem time_le_encoderCount {N n p U D : ℕ} (hN : N ≤ n) :
    LightSourceBandSetup.time N (bandSize n) p
      (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) U D ≤
      (1016*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+1946)*encoderCount n+560 := by
  have ht := LightSourceBandSetup.time_bound N (bandSize n) p
    (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) U D (bandSize_pos n)
  have hn := hN.trans (input_le_encoderCount n)
  have hb := size_le_bandCount hN
  have hm := (Nat.mul_le_mul_right
    (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) hb).trans
      (bands_modulus_le_encoderCount n)
  have hbc := hb.trans (bands_le_encoderCount n)
  have hscan := Nat.mul_le_mul_left 1016 (Nat.mul_le_mul_right
    (Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1) hn)
  nlinarith

theorem persistent_space_le_encoderCount {base N n : ℕ} (hN : N ≤ n) :
    SourceBandLayout.work base N (bandSize n)
      (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) ≤
      base+14*encoderCount n := by
  have hs := SourceBandLayout.work_bound base N (bandSize n)
    (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) (bandSize_pos n)
  have hn := hN.trans (input_le_encoderCount n)
  have hb := size_le_bandCount hN
  have hm := (Nat.mul_le_mul_right
    (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) hb).trans
      (bands_modulus_le_encoderCount n)
  have hbc := hb.trans (bands_le_encoderCount n)
  nlinarith

end ThreeSum.SourceBandCosts
