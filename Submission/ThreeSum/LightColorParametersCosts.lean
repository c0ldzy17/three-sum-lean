import Submission.ThreeSum.LightColorParameters
import Submission.ThreeSum.SharedReportingCostBounds

/-! # Finite and asymptotic cost of executing the small coloring family -/

namespace ThreeSum.LightColorParametersCosts

open ColorParameters Scales StageBounds

def width (n : ℕ) : ℕ := inputBits n+1

theorem width_sufficient (n : ℕ) : n ≤ 2^width n := Nat.lt_log2_self.le

def allTime (W : ℕ) : ℕ := count W*(100*count W+3000)+100
def timeBudget (n : ℕ) : ℕ := allTime (width n)
def wordBudget (n : ℕ) : ℕ := count (width n)+width n+10

theorem sum_time_le (W : ℕ) :
    (∑ t ∈ Finset.range (count W), LightColorParameters.time t) ≤ allTime W := by
  calc
    _ ≤ ∑ _t ∈ Finset.range (count W), (100*count W+2000) := by
      apply Finset.sum_le_sum
      intro t ht
      have hh := Finset.mem_range.mp ht
      unfold LightColorParameters.time
      omega
    _ ≤ _ := by simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]; unfold allTime; nlinarith

theorem slot_word_le {n t : ℕ} (ht : t < count (width n)) :
    t+width n+10 ≤ wordBudget n := by unfold wordBudget; omega

open Filter Real
open scoped Topology

noncomputable section

theorem width_powerBound : PowerBound width 0 :=
  SharedReportingCosts.bits_powerBound.add_same (PowerBound.const 1)

theorem count_powerBound : PowerBound (fun n => count (width n)) 0 := by
  simpa only [count,mul_zero,zero_add] using (PowerBound.const 81).mul (width_powerBound.pow 2)

theorem timeBudget_powerBound : PowerBound timeBudget 0 := by
  have ht : PowerBound (fun n => 100*count (width n)+3000) 0 := by
    have hh := (PowerBound.const 100).mul count_powerBound
    have hh' : PowerBound (fun n => 100*count (width n)) 0 := by simpa only [zero_add] using hh
    exact hh'.add_same (PowerBound.const 3000)
  have hp : PowerBound (fun n => count (width n)*(100*count (width n)+3000)) 0 := by
    simpa only [zero_add] using count_powerBound.mul ht
  exact hp.add_same (PowerBound.const 100)

theorem wordBudget_powerBound : PowerBound wordBudget 0 :=
  (count_powerBound.add_same width_powerBound).add_same (PowerBound.const 10)

end
end ThreeSum.LightColorParametersCosts
