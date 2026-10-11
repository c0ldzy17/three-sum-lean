import Submission.ThreeSum.LightLocalParameters
import Submission.ThreeSum.Scales

/-!
# Local parameter construction fits the uniform subpolynomial budget

These bounds apply to the actual operational contracts, including the
primality scans and integer division. The deliberately loose envelope is
only used for a microblock whose half-size is a cube root of `log n`.
-/

namespace ThreeSum.LocalParameterBounds

open LocalCoverBounds

set_option maxHeartbeats 1000000

def base (h : ℕ) : ℕ := 2^(2048*(h+1))
def envelope (h : ℕ) : ℕ := 2^(2048*(h+1)+2)

theorem pow_pos (e : ℕ) : 1 ≤ (2 : ℕ)^e := Nat.pos_iff_ne_zero.mpr (pow_ne_zero _ (by decide))

theorem threshold_bound (h : ℕ) : localThreshold h ≤ 2^(514*h) := by
  calc
    localThreshold h ≤ 2^(512*h)*2^(2*h) :=
      Nat.mul_le_mul_right _ (Nat.choose_le_two_pow _ _)
    _ = 2^(514*h) := by rw [← pow_add]; congr 1 <;> omega

theorem vertex_bound (h : ℕ) : vertexCount (512*h) h ≤ 2^(514*h) :=
  (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by decide) (by omega))

theorem root_bound (h : ℕ) : rootCeiling (localThreshold h) ≤ 2*2^(514*h) := by
  have hs := Nat.sqrt_le_self (localThreshold h-1)
  have ht := threshold_bound h
  have hp := pow_pos (514*h)
  unfold rootCeiling
  omega

theorem prime_bound (h : ℕ) : localPrime h ≤ 2^(514*h+2) := by
  have hp := (selectedPrime_spec (localThreshold h)).2.2
  have hr := root_bound h
  change localPrime h ≤ _ at hp
  rw [pow_add]
  norm_num
  omega

theorem width_bound (h : ℕ) : 512*h+1 ≤ 2^(h+10) := by
  have hh : h < 2^h := Nat.lt_two_pow_self
  have hp := pow_pos h
  rw [pow_add]
  norm_num
  omega

theorem count_time_bound (h : ℕ) : LightLocalCounts.time h ≤ 2^(2*h+31) := by
  calc
    LightLocalCounts.time h ≤ 1700*(512*h+1)^2 := LightLocalCounts.time_bound h
    _ ≤ 2^11*(2^(h+10))^2 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left (width_bound h) 2)
    _ = 2^(2*h+31) := by rw [← pow_mul,← pow_add]; congr 1 <;> omega

theorem selected_time_bound (h : ℕ) :
    LightSelectedPrime.time (localThreshold h) ≤ 2^(1542*h+19) := by
  have ht := threshold_bound h
  have hx := pow_pos (514*h)
  have ha : localThreshold h+2 ≤ 2^(514*h+2) := by
    rw [pow_add]
    norm_num
    omega
  calc
    _ ≤ 6000*(localThreshold h+2)^3 := LightSelectedPrime.time_bound _
    _ ≤ 2^13*(2^(514*h+2))^3 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left ha 3)
    _ = 2^(1542*h+19) := by rw [← pow_mul,← pow_add]; congr 1 <;> omega

theorem cap_time_bound (h : ℕ) :
    LightSmallDivide.time (LightLocalParameters.numerator h) (localPrime h) ≤ 2^(514*h+10) := by
  have hp := prime_bound h
  have hv := vertex_bound h
  have hx := pow_pos (514*h)
  rw [pow_add] at hp
  norm_num at hp
  have hn : LightLocalParameters.numerator h ≤ 24*2^(514*h) := by
    unfold LightLocalParameters.numerator
    omega
  have hq := Nat.div_le_self (LightLocalParameters.numerator h) (localPrime h)
  unfold LightSmallDivide.time
  rw [pow_add]
  norm_num
  omega

theorem time_bound (h : ℕ) : LightLocalParameters.time h ≤ envelope h := by
  have hc : LightLocalCounts.time h ≤ base h :=
    (count_time_bound h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hp : LightSelectedPrime.time (localThreshold h) ≤ base h :=
    (selected_time_bound h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hd : LightSmallDivide.time (LightLocalParameters.numerator h) (localPrime h) ≤ base h :=
    (cap_time_bound h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hk : 200 ≤ base h := (by decide : 200 ≤ 2^8).trans
    (Nat.pow_le_pow_right (by decide) (by omega))
  have he : envelope h = 4*base h := by unfold envelope base; rw [pow_add]; norm_num; omega
  unfold LightLocalParameters.time
  rw [he]
  omega

theorem count_word_bound (h : ℕ) : LightLocalCounts.word h ≤ 2^(1024*h+11) := by
  have ha : (1024 : ℕ) ≤ 2^(1024*h+10) := by
    exact (by decide : 1024 ≤ 2^10).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hb : 4*(2^(512*h+1))^2 = 2^(1024*h+4) := by
    change 2^2*(2^(512*h+1))^2 = _
    rw [← pow_mul,← pow_add]
    congr 1 <;> omega
  have hc : 2^(1024*h+4) ≤ 2^(1024*h+10) := Nat.pow_le_pow_right (by decide) (by omega)
  have hd : 2^(1024*h+11) = 2*2^(1024*h+10) := by
    rw [show 1024*h+11 = (1024*h+10)+1 by omega,pow_succ]
    omega
  unfold LightLocalCounts.word
  rw [hb,hd]
  omega

theorem selected_word_bound (h : ℕ) :
    LightSelectedPrime.word (localThreshold h) ≤ 2^(514*h+8) := by
  have ht := threshold_bound h
  have hx := pow_pos (514*h)
  unfold LightSelectedPrime.word
  rw [pow_add]
  norm_num
  omega

theorem cap_word_bound (h : ℕ) :
    20*(localPrime h+vertexCount (512*h) h+1) ≤ 2^(514*h+7) := by
  have hp := prime_bound h
  have hv := vertex_bound h
  have hx := pow_pos (514*h)
  rw [pow_add] at hp
  norm_num at hp
  rw [pow_add]
  norm_num
  omega

theorem word_bound (h : ℕ) : LightLocalParameters.word h ≤ envelope h := by
  have hc : LightLocalCounts.word h ≤ base h :=
    (count_word_bound h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hp : LightSelectedPrime.word (localThreshold h) ≤ base h :=
    (selected_word_bound h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hd : 20*(localPrime h+vertexCount (512*h) h+1) ≤ base h :=
    (cap_word_bound h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have he : envelope h = 4*base h := by unfold envelope base; rw [pow_add]; norm_num; omega
  unfold LightLocalParameters.word
  rw [he]
  omega

theorem space_bound (work h : ℕ) : LightLocalParameters.space work h ≤ work+envelope h := by
  have hw := width_bound h
  have hs : (512*h+1)^2 ≤ 2^(2*h+20) := by
    have hp := Nat.pow_le_pow_left hw 2
    simpa only [← pow_mul,show (h+10)*2 = 2*h+20 by omega] using hp
  have hw' : 512*h+1 ≤ 2^(2*h+20) := hw.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hc : LightLocalCounts.space work h ≤ work+base h := by
    have hsum : (512*h+1)^2+(512*h+1) ≤ 2^(2*h+21) := by
      have he : (2 : ℕ)^(2*h+21) = 2*2^(2*h+20) := by
        rw [show 2*h+21 = (2*h+20)+1 by omega,pow_succ]
        omega
      rw [he]
      omega
    have hb : 2^(2*h+21) ≤ base h := Nat.pow_le_pow_right (by decide) (by omega)
    unfold LightLocalCounts.space LightPascal.tableSize
    omega
  have hr := root_bound h
  have hx := pow_pos (514*h)
  have hl := Nat.log_le_self 2 (4*rootCeiling (localThreshold h)+1)
  have hp : LightSelectedPrime.space work (localThreshold h) ≤ work+base h := by
    have hp' : LightSelectedPrime.space work (localThreshold h) ≤ work+2^(514*h+5) := by
      unfold LightSelectedPrime.space LightPrimePool.space
      rw [pow_add]
      norm_num
      omega
    exact hp'.trans (Nat.add_le_add_left (Nat.pow_le_pow_right (by decide) (by omega)) work)
  unfold LightLocalParameters.space
  exact (max_le hc hp).trans (Nat.add_le_add_left (Nat.pow_le_pow_right (by decide) (by omega)) work)

theorem envelope_le_search {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    envelope (Scales.microHalf (Scales.inputBits n)) ≤ Scales.localSearch 2000 n := by
  unfold envelope Scales.localSearch
  rw [Scales.muZero_eq_twice_half]
  apply Nat.pow_le_pow_right (by decide)
  nlinarith

theorem time_le_search {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    LightLocalParameters.time (Scales.microHalf (Scales.inputBits n)) ≤ Scales.localSearch 2000 n :=
  (time_bound _).trans (envelope_le_search hh)

theorem word_le_search {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    LightLocalParameters.word (Scales.microHalf (Scales.inputBits n)) ≤ Scales.localSearch 2000 n :=
  (word_bound _).trans (envelope_le_search hh)

theorem space_le_search {n work : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    LightLocalParameters.space work (Scales.microHalf (Scales.inputBits n)) ≤
      work+Scales.localSearch 2000 n :=
  (space_bound _ _).trans (Nat.add_le_add_left (envelope_le_search hh) work)

end ThreeSum.LocalParameterBounds
