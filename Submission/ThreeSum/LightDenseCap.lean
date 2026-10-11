import Submission.ThreeSum.LightCoverKeyData
import Submission.ThreeSum.LightNatPower

/-!
# Compute the representation cap from the actual retained cover

The two factors are read from the verified cover header. An actual scalar
power loop computes the J-fold cap; no cap value is supplied as an input.
-/

namespace ThreeSum.LightDenseCap

open Light GlobalEncoding LocalCoverBounds

def base (h : ℕ) : ℕ := scheduleSize h*localBucketCap h^2

def word (h J : ℕ) : ℕ :=
  (base h+1)^(J+1)+base h+J+scheduleSize h+localBucketCap h^2+localBucketCap h+20

def body (pPower : ℕ) : Stmt :=
  .set 2 (M (v 0 +' k 7)) ;;
  .set 3 (M (v 0 +' k 10)) ;;
  .set 4 (v 2 *' v 2) ;;
  .set 5 (v 3 *' v 4) ;;
  .call pPower [v 5,v 1] 0

def time (J : ℕ) : ℕ := LightNatPower.time J+150

theorem header_cap {μ : ℕ → ℤ} {free h J : ℕ}
    (H : LightCoverKeyData.Stored μ free h J) : μ (free+7)=(localBucketCap h : ℤ) := by
  have hv := H.header 7 (by simp [LightLocalCoverInit.values,LightLocalParameters.values,
    LightLocalCounts.values,LightLocalCoverMetadata.values])
  simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
    LightLocalCoverMetadata.values] using hv

theorem header_schedule {μ : ℕ → ℤ} {free h J : ℕ}
    (H : LightCoverKeyData.Stored μ free h J) : μ (free+10)=(scheduleSize h : ℤ) := by
  have hv := H.header 10 (by simp [LightLocalCoverInit.values,LightLocalParameters.values,
    LightLocalCounts.values,LightLocalCoverMetadata.values])
  simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
    LightLocalCoverMetadata.values] using hv

theorem header_group {μ : ℕ → ℤ} {free h J : ℕ}
    (H : LightCoverKeyData.Stored μ free h J) : μ (free+3)=(groupSize h : ℤ) := by
  have hv := H.header 3 (by simp [LightLocalCoverInit.values,LightLocalParameters.values,
    LightLocalCounts.values,LightLocalCoverMetadata.values])
  simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
    LightLocalCoverMetadata.values] using hv

variable {lim : Limits} {P : Program} {μ : ℕ → ℤ} {free h J d : ℕ}

theorem meets {pMain pPower : ℕ} (hp : P[pMain]?=some (body pPower))
    (hPower : P[pPower]?=some LightNatPower.body)
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : free+11 ≤ lim.space)
    (hword : (word h J : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (H : LightCoverKeyData.Stored μ free h J) :
    Meets lim P pMain d [free,J] μ (time J)
      (fun result ν => result=(representationCap h J : ℤ) ∧ ν=μ) := by
  have budget (a : ℕ) (ha : a ≤ word h J) : (a : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ha).trans hword
  have hcap := budget (localBucketCap h) (by unfold word; omega)
  have hsq := budget (localBucketCap h^2) (by unfold word; omega)
  have hS := budget (scheduleSize h) (by unfold word; omega)
  have hb := budget (base h) (by unfold word; omega)
  have hJ := budget J (by unfold word; omega)
  have hpow := budget ((base h+1)^(J+1)) (by unfold word; omega)
  have hsqZ : (localBucketCap h : ℤ)*(localBucketCap h : ℤ) ≤ lim.word := by
    simpa only [Nat.cast_pow,pow_two,Nat.cast_mul] using hsq
  have hbZ : (scheduleSize h : ℤ)*(localBucketCap h : ℤ)^2 ≤ lim.word := by
    simpa only [base,Nat.cast_mul,Nat.cast_pow] using hb
  have hsqN : (0 : ℤ) ≤ (localBucketCap h : ℤ)*(localBucketCap h : ℤ) := by positivity
  have hbN : (0 : ℤ) ≤ (scheduleSize h : ℤ)*(localBucketCap h : ℤ)^2 := by positivity
  have hcapRead : μ (((free : ℤ)+7).toNat)=(localBucketCap h : ℤ) := by
    rw [show ((free : ℤ)+7).toNat=free+7 by omega]
    exact header_cap H
  have hSRead : μ (((free : ℤ)+10).toNat)=(scheduleSize h : ℤ) := by
    rw [show ((free : ℤ)+10).toNat=free+10 by omega]
    exact header_schedule H
  apply Meets.of_body hp
  unfold body time
  light_set (localBucketCap h : ℕ) using hcapRead
  light_set (scheduleSize h : ℕ) using hSRead
  light_set (localBucketCap h^2 : ℕ) using pow_two
  light_set (base h : ℕ) using base
  light_call (LightNatPower.bounded_meets (d := d+1) hPower μ hJ hpow)
    with result ν ⟨hr,hν⟩
  exact ⟨hr,hν⟩

def program : Program := [body 1,LightNatPower.body]

theorem program_meets (hw : (lim.space : ℤ) ≤ lim.word) (hspace : free+11 ≤ lim.space)
    (hword : (word h J : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (H : LightCoverKeyData.Stored μ free h J) :
    Meets lim program 0 d [free,J] μ (time J)
      (fun result ν => result=(representationCap h J : ℤ) ∧ ν=μ) :=
  meets rfl rfl hw hspace hword hd H

end ThreeSum.LightDenseCap
