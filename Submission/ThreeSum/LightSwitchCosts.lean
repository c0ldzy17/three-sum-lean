import Submission.ThreeSum.LightSwitchDepth
import Submission.ThreeSum.SharedReportingCostBounds

/-! # Uniform finite and exponent bounds for the actual switch controls -/

namespace ThreeSum.LightSwitchCosts

open Scales StageBounds ArithmeticStageBounds Filter
open scoped Topology

def timeBudget (n : ℕ) : ℕ := 100*(inputBits n+1)+50
def depthBudget (n : ℕ) : ℕ := 5200*inputBits n+90
def wordBudget (n : ℕ) : ℕ := (300*inputBits n+1001)^64
def allTimeBudget (n : ℕ) : ℕ :=
  depthBudget n+(20*inputBits n+1)*timeBudget n

theorem residual_le_bits (n j : ℕ) : Switch.residualSize n j ≤ inputBits n := by
  calc
    _ ≤ blockCount (inputBits n)*muZero n :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _ ≤ inputBits n := LightScales.totalSize_le_self (inputBits n)

theorem time_le_budget (n j : ℕ) :
    LightSwitch.time (Switch.residualSize n j) ≤ timeBudget n := by
  have hh := residual_le_bits n j
  unfold LightSwitch.time timeBudget
  omega

theorem depth_time_le_budget (n : ℕ) :
    LightSwitchDepth.time (blockCount (inputBits n)) ≤ depthBudget n := by
  have hh := LightSwitchDepth.time_bound (blockCount (inputBits n))
  have hJ := LightScales.blockCount_le (inputBits n)
  unfold depthBudget
  omega

theorem word_le_budget (n j : ℕ) :
    LightSwitch.word (blockCount (inputBits n)) (Switch.residualSize n j) ≤ wordBudget n := by
  have hr := residual_le_bits n j
  have hJ := LightScales.blockCount_le (inputBits n)
  exact Nat.pow_le_pow_left (by omega) 64

theorem depth_word_le_budget (n : ℕ) :
    LightSwitchDepth.word (blockCount (inputBits n)) ≤ wordBudget n := by
  have hJ := LightScales.blockCount_le (inputBits n)
  have hbase : 300*inputBits n+1001 ≤ wordBudget n :=
    Nat.le_self_pow (by decide : (64 : ℕ) ≠ 0) _
  unfold LightSwitchDepth.word
  omega

theorem all_time_le_budget (n : ℕ) :
    LightSwitchDepth.time (blockCount (inputBits n))+
      (∑ j ∈ Finset.range (Switch.terminalDepth n+1), LightSwitch.time (Switch.residualSize n j)) ≤
        allTimeBudget n := by
  have ht : (∑ j ∈ Finset.range (Switch.terminalDepth n+1),
      LightSwitch.time (Switch.residualSize n j)) ≤
      (Switch.terminalDepth n+1)*timeBudget n := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (Switch.terminalDepth n+1), timeBudget n :=
        Finset.sum_le_sum (fun j _ => time_le_budget n j)
      _ = _ := by simp
  have hJ := (SharedReportingCosts.terminal_le_blocks n).trans
    (LightScales.blockCount_le (inputBits n))
  have hm := Nat.mul_le_mul_right (timeBudget n) (Nat.add_le_add_right hJ 1)
  have hd := depth_time_le_budget n
  unfold allTimeBudget
  omega

noncomputable section

theorem time_powerBound : PowerBound timeBudget 0 := by
  have hh := ((PowerBound.const 100).mul
    (SharedReportingCosts.bits_powerBound.add_same (PowerBound.const 1)))
  have hh' : PowerBound (fun n => 100*(inputBits n+1)) 0 := by
    simpa only [zero_add] using hh
  exact hh'.add_same (PowerBound.const 50)

theorem depth_powerBound : PowerBound depthBudget 0 := by
  have hh : PowerBound (fun n => 5200*inputBits n) 0 := by
    simpa only [zero_add] using (PowerBound.const 5200).mul SharedReportingCosts.bits_powerBound
  exact hh.add_same (PowerBound.const 90)

theorem word_powerBound : PowerBound wordBudget 0 := by
  have hh : PowerBound (fun n => 300*inputBits n) 0 := by
    simpa only [zero_add] using (PowerBound.const 300).mul SharedReportingCosts.bits_powerBound
  change PowerBound (fun n => (300*inputBits n+1001)^64) 0
  simpa only [mul_zero] using (hh.add_same (PowerBound.const 1001)).pow 64

theorem all_time_powerBound : PowerBound allTimeBudget 0 := by
  have hj : PowerBound (fun n => 20*inputBits n) 0 := by
    simpa only [zero_add] using (PowerBound.const 20).mul SharedReportingCosts.bits_powerBound
  have hh : PowerBound (fun n => (20*inputBits n+1)*timeBudget n) 0 := by
    simpa only [zero_add] using (hj.add_same (PowerBound.const 1)).mul time_powerBound
  exact depth_powerBound.add_same hh

end
end ThreeSum.LightSwitchCosts
