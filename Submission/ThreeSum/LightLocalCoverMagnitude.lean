import Submission.ThreeSum.LightLocalCoverLayout
import Submission.ThreeSum.LocalParameterBounds

/-! # One uniform exponential bound for all finite local-cover dimensions -/

namespace ThreeSum.LightLocalCoverMagnitude

open LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverLayout

def magnitude (h : ℕ) : ℕ := 2^(600000*(h+1)^2)

structure Bounds (h B : ℕ) : Prop where
  positive : 1 ≤ B
  width : 512*h+1 ≤ B
  vertices : LightLocalCoverLayout.vertices h+1 ≤ B
  prime : localPrime h+1 ≤ B
  cap : localBucketCap h+1 ≤ B
  candidates : rows h+1 ≤ B
  rounds : scheduleSize h+1 ≤ B
  decodePower : (localPrime h)^(2*(512*h)+1)+1 ≤ B
  maskPower : 2^(512*h+1)+1 ≤ B

theorem succ_pow_bound {x e : ℕ} (hx : x ≤ 2^e) : x+1 ≤ 2^(e+1) := by
  have hp := Nat.two_pow_pos e
  rw [pow_succ]
  omega

theorem cap_bound (h : ℕ) : localBucketCap h ≤ 2^(514*h+6) := by
  have hp := LocalParameterBounds.prime_bound h
  have hv : LightLocalCoverLayout.vertices h ≤ 2^(514*h+2) :=
    (LocalParameterBounds.vertex_bound h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hc : localBucketCap h ≤ 5*localPrime h+4*LightLocalCoverLayout.vertices h := by
    unfold localBucketCap bucketCap
    exact (Nat.div_le_self _ _).trans (by
      change 4*(localPrime h+LightLocalCoverLayout.vertices h)+localPrime h-1 ≤ _
      omega)
  calc
    localBucketCap h ≤ 16*2^(514*h+2) := by omega
    _ = 2^(514*h+6) := by
      simp only [pow_add]
      norm_num <;> ring

theorem rounds_bound (h : ℕ) : scheduleSize h ≤ 2^(1029*h+16) := by
  have hp := LocalParameterBounds.prime_bound h
  have hp2 : localPrime h^2 ≤ 2^(2*(514*h+2)) := by
    calc
      _ ≤ (2^(514*h+2))^2 := Nat.pow_le_pow_left hp 2
      _ = _ := by rw [← pow_mul]; congr 1 <;> omega
  have hl : Nat.log2 (localPrime h^2) ≤ localPrime h^2 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_le_self 2 _
  have hlog : Nat.log2 (localPrime h^2)+1 ≤ 2^(2*(514*h+2)+1) :=
    (Nat.add_le_add_right hl 1).trans (succ_pow_bound hp2)
  have hlin : 2*h+1 ≤ 2^(h+2) := by
    have hh := Nat.lt_two_pow_self (n := h)
    have hpow := Nat.two_pow_pos h
    rw [pow_add]
    norm_num
    omega
  calc
    scheduleSize h = 320*(2*h+1)*(Nat.log2 (localPrime h^2)+1) := rfl
    _ ≤ (2^9)*(2^(h+2))*(2^(2*(514*h+2)+1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by decide) hlin) hlog
    _ = 2^(1029*h+16) := by
      rw [← pow_add,← pow_add]
      congr 1
      omega

theorem bounds (h : ℕ) : Bounds h (magnitude h) := by
  have hs : 0 ≤ h*h := Nat.zero_le _
  have raise (e : ℕ) (he : e ≤ 600000*(h+1)^2) : 2^e ≤ magnitude h :=
    Nat.pow_le_pow_right (by decide) he
  have hp := LocalParameterBounds.prime_bound h
  have hN : rows h ≤ 2^((514*h+2)*(2*(512*h))) := by
    unfold rows
    calc
      _ ≤ (2^(514*h+2))^(2*(512*h)) := Nat.pow_le_pow_left hp _
      _ = _ := by rw [← pow_mul]
  have hP : (localPrime h)^(2*(512*h)+1) ≤ 2^((514*h+2)*(2*(512*h)+1)) := by
    calc
      _ ≤ (2^(514*h+2))^(2*(512*h)+1) := Nat.pow_le_pow_left hp _
      _ = _ := by rw [← pow_mul]
  refine ⟨by exact Nat.two_pow_pos _,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (LocalParameterBounds.width_bound h).trans (raise _ (by nlinarith only [hs]))
  · have hv : LightLocalCoverLayout.vertices h ≤ 2^(512*h) := Nat.choose_le_two_pow _ _
    exact (succ_pow_bound hv).trans (raise _ (by nlinarith only [hs]))
  · exact (succ_pow_bound hp).trans (raise _ (by nlinarith only [hs]))
  · exact (succ_pow_bound (cap_bound h)).trans (raise _ (by nlinarith only [hs]))
  · exact (succ_pow_bound hN).trans (raise _ (by nlinarith only [hs]))
  · exact (succ_pow_bound (rounds_bound h)).trans (raise _ (by nlinarith only [hs]))
  · exact (succ_pow_bound hP).trans (raise _ (by nlinarith only [hs]))
  · exact (succ_pow_bound (le_rfl : 2^(512*h+1) ≤ 2^(512*h+1))).trans
      (raise _ (by nlinarith only [hs]))

end ThreeSum.LightLocalCoverMagnitude
