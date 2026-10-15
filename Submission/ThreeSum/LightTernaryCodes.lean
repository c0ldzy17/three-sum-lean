import Submission.ThreeSum.LightMaskErase
import Submission.ThreeSum.LightMaskBits

/-!
# Actual lower-code computation for canonical two-bit trits

No interval of numeric codes is traversed. Two calls to the verified bit
deletion routine compute the zero digit code. The upper-bit deletion computes
the digit-one code. The original code serves as the clamped digit-two code.
-/

namespace ThreeSum.LightTernaryCodes

open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase

variable {lim : Limits} {P : Program}

def zeroCode (W low high m : ℕ) : ℕ := eraseMask W low (eraseMask W high m)

def oneCode (W high m : ℕ) : ℕ := eraseMask W high m

def digit (W low high m : ℕ) : ℕ :=
  LightMaskBits.bit W m low + LightMaskBits.bit W m high

theorem digit_le_two (W low high m : ℕ) : digit W low high m ≤ 2 := by
  have h0 := LightMaskBits.bit_le W m low
  have h1 := LightMaskBits.bit_le W m high
  unfold digit
  omega

def zeroBody (pErase : ℕ) : Stmt :=
  .call pErase [v 0,v 2,v 3,v 0,v 4] 5 ;;
  .call pErase [v 0,v 1,v 5,v 0,v 4] 0

def zeroTime (W : ℕ) : ℕ := 2*LightMaskErase.time W + 80

theorem zero_meets {pMain pErase W low high m powers d : ℕ}
    (hmain : P[pMain]? = some (zeroBody pErase))
    (herase : P[pErase]? = some (LightMaskErase.body pErase))
    (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hpowers : Powers μ powers W)
    (hlow : low ≤ W) (hhigh : high ≤ W) (hm : m < 2^W)
    (hd : d+W+1 ≤ lim.depth) :
    Meets lim P pMain d [W,low,high,m,powers] μ (zeroTime W)
      (fun r μ' => r = (zeroCode W low high m : ℤ) ∧ μ' = μ) := by
  have hupper := LightMaskErase.meets herase μ hw hspace hword hpowers
    W high m le_rfl hhigh hm (d+1) (by omega)
  have hu : eraseMask W high m < 2^W := (eraseMask_le hm).trans_lt hm
  have hlower := LightMaskErase.meets herase μ hw hspace hword hpowers
    W low (eraseMask W high m) le_rfl hlow hu (d+1) (by omega)
  apply Meets.of_body hmain
  unfold zeroBody zeroTime
  light_call hupper using LightMaskErase.time with r1 μ1 ⟨hr1,hm1⟩
  subst μ1
  light_call hlower using hr1,LightMaskErase.time with r μ' ⟨hr,hm'⟩
  exact ⟨hr,hm'⟩

def digitBody (pErase : ℕ) : Stmt :=
  .call pErase [v 0,v 1,v 3,v 0,v 4] 5 ;;
  .call pErase [v 0,v 2,v 3,v 0,v 4] 6 ;;
  .set 7 (k 0) ;;
  .ite (v 5 =' v 3) .skip (.set 7 (k 1)) ;;
  .ite (v 6 =' v 3) .skip (.set 7 (v 7 +' k 1)) ;;
  .set 0 (v 7)

def digitTime (W : ℕ) : ℕ := 2*LightMaskErase.time W + 130

theorem digit_meets {pMain pErase W low high m powers d : ℕ}
    (hmain : P[pMain]? = some (digitBody pErase))
    (herase : P[pErase]? = some (LightMaskErase.body pErase))
    (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hpowers : Powers μ powers W)
    (hlow : low ≤ W) (hhigh : high ≤ W) (hm : m < 2^W)
    (hd : d+W+1 ≤ lim.depth) (htwo : 2 ≤ lim.word) :
    Meets lim P pMain d [W,low,high,m,powers] μ (digitTime W)
      (fun r μ' => r = (digit W low high m : ℤ) ∧ μ' = μ) := by
  have hlower := LightMaskErase.meets herase μ hw hspace hword hpowers
    W low m le_rfl hlow hm (d+1) (by omega)
  have hupper := LightMaskErase.meets herase μ hw hspace hword hpowers
    W high m le_rfl hhigh hm (d+1) (by omega)
  apply Meets.of_body hmain
  unfold digitBody digitTime
  light_call hlower using LightMaskErase.time with r0 μ0 ⟨hr0,hm0⟩
  subst μ0
  light_call hupper using LightMaskErase.time with r1 μ1 ⟨hr1,hm1⟩
  subst μ1
  light_set 0 using LightMaskErase.time
  light_if he0 hn0 : (eraseMask W low m : ℤ) = (m : ℤ) using hr0,LightMaskErase.time
  · have hn0 : eraseMask W low m = m := by exact_mod_cast he0
    light_if he1 hn1 : (eraseMask W high m : ℤ) = (m : ℤ)
      using hr1,LightMaskErase.time
    · have hn1 : eraseMask W high m = m := by exact_mod_cast he1
      light_set 0 using LightMaskErase.time
      exact ⟨by simp [digit,LightMaskBits.bit,hn0,hn1],rfl⟩
    · have hn1 : eraseMask W high m ≠ m := by
        intro h
        exact hn1 (by exact_mod_cast h)
      light_set 1 using LightMaskErase.time
      light_set 1 using LightMaskErase.time
      exact ⟨by simp [digit,LightMaskBits.bit,hn0,hn1],rfl⟩
  · have hn0 : eraseMask W low m ≠ m := by
      intro h
      exact hn0 (by exact_mod_cast h)
    light_set 1 using LightMaskErase.time
    light_if he1 hn1 : (eraseMask W high m : ℤ) = (m : ℤ)
      using hr1,LightMaskErase.time
    · have hn1 : eraseMask W high m = m := by exact_mod_cast he1
      light_set 1 using LightMaskErase.time
      exact ⟨by simp [digit,LightMaskBits.bit,hn0,hn1],rfl⟩
    · have hn1 : eraseMask W high m ≠ m := by
        intro h
        exact hn1 (by exact_mod_cast h)
      light_set 2 using LightMaskErase.time
      light_set 2 using LightMaskErase.time
      exact ⟨by simp [digit,LightMaskBits.bit,hn0,hn1],rfl⟩

def program : Program := [zeroBody 2,digitBody 2,LightMaskErase.body 2]

theorem zero_time_bound (W : ℕ) : zeroTime W ≤ 400*(W+1) := by
  unfold zeroTime LightMaskErase.time
  omega

theorem digit_time_bound (W : ℕ) : digitTime W ≤ 400*(W+1) := by
  unfold digitTime LightMaskErase.time
  omega

end ThreeSum.LightTernaryCodes
