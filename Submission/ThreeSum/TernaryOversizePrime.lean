import Submission.ThreeSum.TernaryEntropyRates
import Submission.ThreeSum.TernaryCoverCapParameters

/-! Finite integer root and oversized native field for paired reporting. -/
noncomputable section
namespace ThreeSum.TernaryOversizePrime
open Finset TernaryCoverScale TernaryEntropyRates TernaryLocalParameters
open TernaryCoverLocal TernaryCoverFrequency TernaryCoverCapParameters
set_option maxHeartbeats 2000000

def rootCandidates (K M : ℕ) : Finset ℕ :=
  (range (M+1)).filter fun s => M ≤ s^K

theorem rootCandidates_nonempty {K M : ℕ} (hK : 0 < K) (hM : 0 < M) :
    (rootCandidates K M).Nonempty := by
  refine ⟨M,mem_filter.mpr ⟨mem_range.mpr (by omega),?_⟩⟩
  exact Nat.le_self_pow hK.ne' M

def rootCeiling (K M : ℕ) : ℕ :=
  if h : (rootCandidates K M).Nonempty then (rootCandidates K M).min' h else 1

theorem rootCeiling_mem {K M : ℕ} (hK : 0 < K) (hM : 0 < M) :
    rootCeiling K M ∈ rootCandidates K M := by
  rw [rootCeiling,dif_pos (rootCandidates_nonempty hK hM)]
  exact min'_mem _ _

theorem rootCeiling_lower {K M : ℕ} (hK : 0 < K) (hM : 0 < M) :
    M ≤ rootCeiling K M^K := (mem_filter.mp (rootCeiling_mem hK hM)).2

theorem rootCeiling_le {K M : ℕ} (hK : 0 < K) (hM : 0 < M) :
    rootCeiling K M ≤ M := by
  have h := (mem_range.mp (mem_filter.mp (rootCeiling_mem hK hM)).1)
  omega

theorem rootCeiling_pos {K M : ℕ} (hK : 0 < K) (hM : 0 < M) :
    0 < rootCeiling K M := by
  have h := rootCeiling_lower hK hM
  by_contra hn
  have hz : rootCeiling K M=0 := by omega
  rw [hz,zero_pow hK.ne'] at h
  omega

theorem rootCeiling_upper {K M : ℕ} (hK : 0 < K) (hM : 0 < M) :
    rootCeiling K M^K ≤ 2^K*M := by
  by_cases h1 : M=1
  · subst M
    have hs := rootCeiling_le hK (by decide : 0 < (1 : ℕ))
    have hp := rootCeiling_pos hK (by decide : 0 < (1 : ℕ))
    have he : rootCeiling K 1=1 := by omega
    rw [he,one_pow,mul_one]
    exact Nat.one_le_pow _ _ (by decide)
  have hM1 : 1 < M := by omega
  have hs := rootCeiling_pos hK hM
  have hs2 : 2 ≤ rootCeiling K M := by
    have hl := rootCeiling_lower hK hM
    by_contra hn
    have he : rootCeiling K M=1 := by omega
    rw [he,one_pow] at hl
    omega
  have hpred : (rootCeiling K M-1)^K < M := by
    by_contra hn
    have hm : rootCeiling K M-1 ∈ rootCandidates K M := by
      apply mem_filter.mpr
      refine ⟨mem_range.mpr ?_,by omega⟩
      have := rootCeiling_le hK hM
      omega
    have hle : rootCeiling K M ≤ rootCeiling K M-1 := by
      simpa only [rootCeiling,dif_pos (rootCandidates_nonempty hK hM)] using min'_le _ _ hm
    omega
  have htw : rootCeiling K M ≤ 2*(rootCeiling K M-1) := by omega
  calc
    _ ≤ (2*(rootCeiling K M-1))^K := Nat.pow_le_pow_left htw K
    _ = 2^K*(rootCeiling K M-1)^K := mul_pow _ _ _
    _ ≤ 2^K*M := Nat.mul_le_mul_left _ hpred.le

theorem outputSize_pos (m : ℕ) : 0 < outputSize m := by
  rw [actual_output_count]
  exact typeCount_pos (by decide) m

def inflation (K m : ℕ) : ℕ := rootCeiling K (outputSize m)
def inflatedThreshold (K m : ℕ) : ℕ := threshold m*(inflation K m)^2
/- The checked opaque package stops typeclass normalization from evaluating
the entire finite prime search while constructing a ZMod instance. -/
opaque nativePrimeData (K m : ℕ) : {p : ℕ // p.Prime ∧
    p=LocalCoverBounds.selectedPrime (inflatedThreshold K m)} :=
  ⟨LocalCoverBounds.selectedPrime (inflatedThreshold K m),
    (LocalCoverBounds.selectedPrime_spec (inflatedThreshold K m)).1,rfl⟩
def nativePrime (K m : ℕ) : ℕ := (nativePrimeData K m).val
theorem nativePrime_eq_selected (K m : ℕ) :
    nativePrime K m=LocalCoverBounds.selectedPrime (inflatedThreshold K m) :=
  (nativePrimeData K m).property.2

theorem inflation_pos {K : ℕ} (hK : 0 < K) (m : ℕ) : 0 < inflation K m :=
  rootCeiling_pos hK (outputSize_pos m)
theorem inflation_lower {K : ℕ} (hK : 0 < K) (m : ℕ) : outputSize m ≤ inflation K m^K :=
  rootCeiling_lower hK (outputSize_pos m)
theorem inflation_upper {K : ℕ} (hK : 0 < K) (m : ℕ) : inflation K m^K ≤ 2^K*outputSize m :=
  rootCeiling_upper hK (outputSize_pos m)

theorem nativePrime_prime (K m : ℕ) : (nativePrime K m).Prime :=
  (nativePrimeData K m).property.1
instance (priority := 2000) (K m : ℕ) : Fact (nativePrime K m).Prime := ⟨nativePrime_prime K m⟩

theorem nativePrime_lower (K m : ℕ) : inflatedThreshold K m ≤ nativePrime K m^2 := by
  rw [nativePrime_eq_selected]
  exact LocalCoverBounds.selectedPrime_sq_lower _
theorem nativePrime_upper {K : ℕ} (hK : 0 < K) (m : ℕ) :
    nativePrime K m^2 ≤ 16*inflatedThreshold K m := by
  rw [nativePrime_eq_selected]
  exact LocalCoverBounds.selectedPrime_sq_upper (Nat.mul_pos (threshold_pos m) (Nat.pow_pos (inflation_pos hK m)))

theorem nativePrime_base_lower {K : ℕ} (hK : 0 < K) (m : ℕ) :
    threshold m ≤ nativePrime K m^2 := by
  have h1 : 1 ≤ inflation K m^2 := Nat.one_le_pow _ _ (inflation_pos hK m)
  have hb : threshold m ≤ threshold m*(inflation K m)^2 := by
    simpa only [mul_one] using Nat.mul_le_mul_left (threshold m) h1
  exact hb.trans (nativePrime_lower K m)

theorem nativePrime_gt_four {K m : ℕ} (hK : 0 < K) (hm : 0 < m) : 4 < nativePrime K m := by
  have hR := TernaryTypeLowerBound.partition_cap_le_prime (fixedPi m) (fixedPi_total m)
    (fixedPi_space m) (nativePrime K m) (nativePrime_base_lower hK m)
  have he : 3 ≤ fixedPi m 1 := by simp [fixedPi]; omega
  have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) he
  have ht : 2^(fixedPi m 1) ≤ 2^(fixedPi m 1)*3^(fixedPi m 2) := by
    simpa using Nat.mul_le_mul_left (2^(fixedPi m 1)) (Nat.one_le_pow (fixedPi m 2) 3 (by decide))
  norm_num at hp
  omega

def inflatedFrequency (K m : ℕ) : ℕ := frequencyFactor m*(inflation K m)^4

theorem inflated_frequency_scale {K : ℕ} (hK : 0 < K) (m : ℕ) :
    4*(nativePrime K m)^4*3^16 ≤ inflatedFrequency K m*Fintype.card (TernaryCoverGoodMaps.ActualEdge m)^2 := by
  have he := TernaryPartitionCount.fixed_edge_mass_lower m
  have hp := nativePrime_upper hK m
  have hs : nativePrime K m^2 ≤
      (16*TernaryPartitionCount.partitionLoss (7930175*m) (978249*m))*
        Fintype.card (TernaryCoverGoodMaps.ActualEdge m)*(inflation K m)^2 := by
    change nativePrime K m^2 ≤ 16*(threshold m*(inflation K m)^2) at hp
    have he' : threshold m ≤ TernaryPartitionCount.partitionLoss (7930175*m) (978249*m)*
        Fintype.card (TernaryCoverGoodMaps.ActualEdge m) := he
    have hx := Nat.mul_le_mul_right ((inflation K m)^2) (Nat.mul_le_mul_left 16 he')
    exact hp.trans (by simpa only [Nat.mul_assoc] using hx)
  have h := Nat.mul_le_mul_left (4*3^16) (Nat.pow_le_pow_left hs 2)
  unfold inflatedFrequency frequencyFactor
  convert h using 1 <;> ring

attribute [irreducible] nativePrime
instance (priority := 3000) (K m : ℕ) : NeZero (nativePrime K m) :=
  ⟨(nativePrime_prime K m).ne_zero⟩

def nativeCatalog (K m : ℕ) : List (TernaryCoverGoodMaps.Weight m (nativePrime K m)) := univ.toList
theorem nativeCatalog_complete (K m : ℕ) (w : TernaryCoverGoodMaps.Weight m (nativePrime K m)) :
    w ∈ nativeCatalog K m := by simp [nativeCatalog]

def nativeFamily (K m k : ℕ) := Cover.greedyChoices (nativeCatalog K m)
  (Covers m (nativePrime K m) (sourceCap m (nativePrime K m))
    (rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k)) univ
  (inflatedFrequency K m*(Nat.log2 (nativePrime K m^2)+1))

theorem native_family_covers {K m k : ℕ} (hK : 0 < K) (hm : 0 < m) (hk : 0 < k)
    (t : ZMod (nativePrime K m) × ZMod (nativePrime K m)) :
    ∃ w ∈ nativeFamily K m k, Covers m (nativePrime K m) (sourceCap m (nativePrime K m))
      (rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k) w t := by
  have hF : 1 < inflatedFrequency K m := by
    have hi : 1 ≤ inflation K m^4 := Nat.one_le_pow _ _ (inflation_pos hK m)
    have h := Nat.mul_le_mul_left (frequencyFactor m) hi
    exact (frequencyFactor_gt_one m).trans_le (by simpa [inflatedFrequency] using h)
  exact greedy_covers m (nativePrime K m) (nativeCatalog K m) (nativeCatalog_complete K m)
    (nativePrime_gt_four hK hm) (nativePrime_base_lower hK m)
    (sourceCap m (nativePrime K m)) k
    (rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k)
    (inflatedFrequency K m) hF (rawThreshold_pos _ _ _) (sourceCap_threshold _ _ (nativePrime_prime K m).pos)
    (actual_pruning_guard _ _ _ _ hk) (inflated_frequency_scale hK m) t

theorem native_family_length (K m k : ℕ) :
    (nativeFamily K m k).length=inflatedFrequency K m*(Nat.log2 (nativePrime K m^2)+1) :=
  Cover.greedyChoices_length _ _ _ _

end ThreeSum.TernaryOversizePrime
