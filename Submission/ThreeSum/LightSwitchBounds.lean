import Submission.ThreeSum.Switch
import Submission.ThreeSumApsp.Lang.Lib.Logs

/-!
# Finite scalar bounds and minimality for the executed cubic switch

These are the exact cleared integer comparisons of `Switch.switchIndex`.
No real arithmetic is executed by the eventual program.
-/

namespace ThreeSum.LightSwitch

open Light

set_option maxHeartbeats 1800000

def left (J j r : ℕ) : ℕ := (291*J+1000*j)*r*r*r
def cubic (r q : ℕ) : ℕ := q*(799*r*r+q*(72*r+24*q))
def factor (J j : ℕ) : ℕ := 10*(J-j)
def word (J r : ℕ) : ℕ := (J+r+1001)^64

theorem cubic_eq (r q : ℕ) : cubic r q=Switch.cubicNumerator r q := by
  unfold cubic Switch.cubicNumerator
  ring

theorem accepts_iff (J j r q : ℕ) :
    Switch.accepts J j r q ↔ left J j r ≤ factor J j*cubic r q := by
  have hl : left J j r=(291*J+1000*j)*r^3 := by unfold left; ring
  rw [hl,cubic_eq]
  rfl

theorem before_rejects {J j r q : ℕ}
    (hne : (Switch.candidates J j r).Nonempty) (hq : q < Switch.switchIndex J j r) :
    factor J j*cubic r q < left J j r := by
  have hb := (Switch.mem_candidates.mp (Switch.switchIndex_mem hne)).1
  have hno : ¬ Switch.accepts J j r q := by
    intro h
    have hm := Switch.switchIndex_le (Switch.mem_candidates.mpr ⟨by omega,h⟩)
    omega
  rw [accepts_iff] at hno
  omega

theorem at_accepts {J j r : ℕ} (hne : (Switch.candidates J j r).Nonempty) :
    left J j r ≤ factor J j*cubic r (Switch.switchIndex J j r) :=
  (accepts_iff _ _ _ _).mp (Switch.mem_candidates.mp (Switch.switchIndex_mem hne)).2

theorem index_le_residual {J j r : ℕ} (hne : (Switch.candidates J j r).Nonempty) :
    Switch.switchIndex J j r ≤ r :=
  (Switch.mem_candidates.mp (Switch.switchIndex_mem hne)).1.trans (Nat.div_le_self _ _)

theorem actual_candidates_nonempty {n j : ℕ} (hj : j ≤ Switch.terminalDepth n) :
    (Switch.candidates (Scales.blockCount (Scales.inputBits n)) j
      (Switch.residualSize n j)).Nonempty := by
  by_cases hz : Switch.residualSize n j=0
  · refine ⟨0,Switch.mem_candidates.mpr ⟨by omega,?_⟩⟩
    simp [Switch.accepts,Switch.cubicNumerator,hz]
  · have hJ : 0 < Scales.blockCount (Scales.inputBits n) := by
      have hh := Switch.actual_depth_condition hj
      unfold Switch.residualSize at hz
      by_contra h
      have he : Scales.blockCount (Scales.inputBits n)=0 := by omega
      simp [he] at hz
    exact Switch.candidates_nonempty hJ (Switch.actual_depth_condition hj)
      (by omega) (Switch.actual_residual_even n j)

end ThreeSum.LightSwitch
