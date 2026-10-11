import Submission.ThreeSum.LightReportingSuffixSetup

/-! # The actual local box construction is charged to the suffix binomial layer -/

namespace ThreeSum.ReportingHostSuffixCosts

open ThreeSum.SubsetAddress ThreeSum.LightBlockQuery ThreeSum.BlockIndexedQuery
open scoped BigOperators

theorem choose_le_cut {V j cut : ℕ} (hj : j ≤ cut) (hhalf : cut ≤ V/2) :
    V.choose j ≤ V.choose cut := by
  induction cut,hj using Nat.le_induction with
  | base => exact le_rfl
  | succ cut hj ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

theorem downsetCap_le_layer {V cut : ℕ} (hhalf : cut ≤ V/2) :
    downsetCap V cut ≤ (cut+1)*V.choose cut := by
  have hcut : cut ≤ V := hhalf.trans (Nat.div_le_self _ _)
  simp only [downsetCap,Nat.min_eq_left hcut,layerOffset]
  calc
    _ ≤ ∑ _j ∈ Finset.range (cut+1), V.choose cut := by
      apply Finset.sum_le_sum
      intro j hj
      exact choose_le_cut (by have := Finset.mem_range.mp hj; omega) hhalf
    _ = _ := by simp

theorem downsetCap_add_one_le_layer {V cut : ℕ} (hhalf : cut ≤ V/2) :
    downsetCap V cut+1 ≤ (V+2)*V.choose cut := by
  have hcut : cut ≤ V := hhalf.trans (Nat.div_le_self _ _)
  have hp := Nat.choose_pos hcut
  have hd := downsetCap_le_layer hhalf
  have hm := Nat.mul_le_mul_right (V.choose cut) (Nat.succ_le_succ hcut)
  nlinarith

theorem storedCells_le_layer {V cut : ℕ} (hhalf : cut ≤ V/2) :
    (V+1)*downsetCap V cut ≤ (V+1)*(cut+1)*V.choose cut := by
  have hm := Nat.mul_le_mul_left (V+1) (downsetCap_le_layer hhalf)
  simpa only [Nat.mul_assoc] using hm

theorem setup_time_le_layer {W V offset cut : ℕ} (hfit : offset+V ≤ W)
    (hhalf : cut ≤ V/2) :
    LightReportingSuffixSetup.time W V cut offset ≤ 40000*(W+1)^5*V.choose cut := by
  have hcut : cut ≤ V := hhalf.trans (Nat.div_le_self _ _)
  have ht := LightReportingSuffixSetup.time_bound hfit hcut
  have hd := downsetCap_add_one_le_layer hhalf
  have hm := Nat.mul_le_mul_left (20000*(W+1)^4) hd
  have hv : V+2 ≤ 2*(W+1) := by omega
  have hm₂ := Nat.mul_le_mul_left (20000*(W+1)^4)
    (Nat.mul_le_mul_right (V.choose cut) hv)
  calc
    _ ≤ 20000*(W+1)^4*((V+2)*V.choose cut) := ht.trans hm
    _ ≤ 20000*(W+1)^4*((2*(W+1))*V.choose cut) := hm₂
    _ = _ := by ring

theorem suffix_width_eq (h J k : ℕ) :
    suffixStage J (512*h) k = 256*residualSize h J k := by
  unfold suffixStage residualSize
  ring

theorem block_setup_time_le_layer {h J k cut : ℕ} (hk : k ≤ J)
    (hcut : cut ≤ residualSize h J k) :
    LightReportingSuffixSetup.time (width h J) (suffixStage J (512*h) k) cut (k*(512*h)) ≤
      40000*(width h J+1)^5*(256*residualSize h J k).choose cut := by
  have hhalf : cut ≤ suffixStage J (512*h) k/2 := by
    rw [suffix_width_eq]
    omega
  calc
    _ ≤ 40000*(width h J+1)^5*(suffixStage J (512*h) k).choose cut :=
      setup_time_le_layer (W := width h J) (V := suffixStage J (512*h) k)
        (offset := k*(512*h)) (ReportingHostSuffix.block_fit hk) hhalf
    _ = _ := by rw [suffix_width_eq]

end ThreeSum.ReportingHostSuffixCosts
