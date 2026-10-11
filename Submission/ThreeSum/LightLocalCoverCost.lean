import Submission.ThreeSum.LightLocalCoverLayout
import Submission.ThreeSum.LocalParameterBounds

/-! # Polynomial bounds for the actual local-cover procedures -/

namespace ThreeSum.LightLocalCoverCost

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverLayout

set_option maxHeartbeats 1500000

theorem hash_time_bound (L n p : ℕ) :
    LightHashHistogram.time L n p p ≤ 1000*(L+1)*(n+1)*(p+1) := by
  have hm := Nat.mul_le_mul_left n (Nat.log_le_self 2 (L*p+1))
  unfold LightHashHistogram.time LightMaskHashes.time LightOneHot.time
    LightResidues.residuesTime LightResidues.residueBudget LightHistogram.histogramTime
    LightHistogram.countTime powTableTime fillTime
  ring_nf at hm ⊢
  omega

theorem greedy_time_bound (N C T : ℕ) :
    LightCoverGreedy.time N C T ≤ 1000*(N+1)*(C+1)*(T+1) := by
  unfold LightCoverGreedy.time LightCoverGreedy.roundTime LightCoverSelect.time
    LightCoverScores.time LightBooleanDot.time LightMinimum.time LightCoverUpdate.time fillTime
  ring_nf
  omega

theorem mask_table_time_bound (L n : ℕ) :
    LightMaskBitTable.time L n ≤ 400*(n+1)*(L+1)^2 := by
  have hm := Nat.mul_le_mul_left n (LightMaskBits.time_bound L)
  have hs : n ≤ n*(L+1)^2 := Nat.le_mul_of_pos_right _ (by positivity)
  unfold LightMaskBitTable.time
  ring_nf at hm hs ⊢
  omega

theorem candidate_time_bound {L n p N B : ℕ}
    (hB : 1 ≤ B) (hL : L+1 ≤ B) (hn : n+1 ≤ B) (hp : p+1 ≤ B) (hN : N+1 ≤ B) :
    LightLocalCoverCandidate.time L n p N ≤ 5000*B^4 := by
  have hdecode : LightWeightDecode.time L N ≤ 600*B^2 := by
    calc
      _ ≤ 600*(L+1)*(N+1) := LightWeightDecode.time_bound L N
      _ ≤ 600*B*B := by gcongr
      _ = _ := by ring
  have hhash : LightHashHistogram.time L n p p ≤ 1000*B^3 := by
    calc
      _ ≤ 1000*(L+1)*(n+1)*(p+1) := hash_time_bound L n p
      _ ≤ 1000*B*B*B := by gcongr
      _ = _ := by ring
  have hn2 : n*n+1 ≤ B^2 := by
    have hm := Nat.pow_le_pow_left hn 2
    nlinarith
  have hp2 : p*p ≤ B^2 := by
    have hm := Nat.pow_le_pow_left hp 2
    nlinarith
  have hB2 : B ≤ B^2 := Nat.le_self_pow (by decide) B
  have hrest : L+n+p*p+1 ≤ 3*B^2 := by omega
  have hrow : LightLocalCoverRow.time L n p ≤ 1800*B^4 := by
    calc
      _ ≤ 600*(n*n+1)*(L+n+p*p+1) := LightLocalCoverRow.time_bound L n p
      _ ≤ 600*(B^2)*(3*B^2) := Nat.mul_le_mul (Nat.mul_le_mul_left 600 hn2) hrest
      _ = _ := by ring
  have hb24 := Nat.pow_le_pow_right hB (by decide : 2 ≤ 4)
  have hb34 := Nat.pow_le_pow_right hB (by decide : 3 ≤ 4)
  have hb4 : 1 ≤ B^4 := Nat.pow_pos (by omega)
  unfold LightLocalCoverCandidate.time
  omega

theorem matrix_time_bound {L n p N B : ℕ}
    (hB : 1 ≤ B) (hL : L+1 ≤ B) (hn : n+1 ≤ B) (hp : p+1 ≤ B) (hN : N+1 ≤ B) :
    LightLocalCoverMatrix.time L n p N ≤ 6000*B^5 := by
  have hc := candidate_time_bound hB hL hn hp hN
  have hm := Nat.mul_le_mul (show N ≤ B by omega) (Nat.add_le_add_right hc 200)
  have hb5 : B ≤ B^5 := Nat.le_self_pow (by decide) B
  have hb5' : 1 ≤ B^5 := Nat.pow_pos (by omega)
  unfold LightLocalCoverMatrix.time
  ring_nf at hm ⊢
  omega

theorem host_time_bound {h B : ℕ}
    (hB : 1 ≤ B) (hL : 512*h+1 ≤ B) (hn : vertices h+1 ≤ B)
    (hp : localPrime h+1 ≤ B) (hN : rows h+1 ≤ B) (hT : scheduleSize h+1 ≤ B) :
    LightLocalCoverHost.time h ≤ 8000*B^5 := by
  have hm := matrix_time_bound hB hL hn hp hN
  have hp2 : cols h+1 ≤ B^2 := by
    have hs := Nat.pow_le_pow_left hp 2
    unfold cols
    nlinarith
  have hg : LightCoverGreedy.time (rows h) (cols h) (scheduleSize h) ≤ 1000*B^4 := by
    calc
      _ ≤ 1000*(rows h+1)*(cols h+1)*(scheduleSize h+1) := greedy_time_bound _ _ _
      _ ≤ 1000*B*(B^2)*B := by gcongr
      _ = _ := by ring
  have hh : LightWeightGather.time (scheduleSize h) (2*(512*h)) ≤ 260*B^2 := by
    calc
      _ ≤ 130*(scheduleSize h+1)*(2*(512*h)+1) := LightWeightGather.time_bound _ _
      _ ≤ 130*B*(2*B) := Nat.mul_le_mul (Nat.mul_le_mul_left 130 hT) (by omega)
      _ = _ := by ring
  have hb25 := Nat.pow_le_pow_right hB (by decide : 2 ≤ 5)
  have hb45 := Nat.pow_le_pow_right hB (by decide : 4 ≤ 5)
  have hb5 : 1 ≤ B^5 := Nat.pow_pos (by omega)
  unfold LightLocalCoverHost.time
  change LightLocalCoverMatrix.time (512*h) (vertices h) (localPrime h) (rows h)+
    LightCoverGreedy.time (rows h) (cols h) (scheduleSize h)+
    LightWeightGather.time (scheduleSize h) (2*(512*h))+200 ≤ _
  omega

theorem build_time_bound {h B : ℕ}
    (hB : 1 ≤ B) (hL : 512*h+1 ≤ B) (hn : vertices h+1 ≤ B)
    (hp : localPrime h+1 ≤ B) (hN : rows h+1 ≤ B) (hT : scheduleSize h+1 ≤ B) :
    LightLocalCoverBuild.time h ≤ 10000*B^5 := by
  have hc := host_time_bound hB hL hn hp hN hT
  have he : LightSubsetEnumerationSetup.time (512*h) h ≤ 800*B^2 := by
    calc
      _ ≤ 800*(512*h+1)*((512*h).choose h+1) := LightSubsetEnumerationSetup.time_bound _ _
      _ ≤ 800*B*B := Nat.mul_le_mul (Nat.mul_le_mul_left 800 hL) hn
      _ = _ := by ring
  have hb : LightMaskBitTable.time (512*h) (vertices h) ≤ 400*B^3 := by
    calc
      _ ≤ 400*(vertices h+1)*(512*h+1)^2 := mask_table_time_bound _ _
      _ ≤ 400*B*(B^2) := by gcongr
      _ = _ := by ring
  have hb25 := Nat.pow_le_pow_right hB (by decide : 2 ≤ 5)
  have hb35 := Nat.pow_le_pow_right hB (by decide : 3 ≤ 5)
  have hb5 : 1 ≤ B^5 := Nat.pow_pos (by omega)
  unfold LightLocalCoverBuild.time
  change LightSubsetEnumerationSetup.time (512*h) h+
    LightMaskBitTable.time (512*h) (vertices h)+LightLocalCoverHost.time h+200 ≤ _
  omega

end ThreeSum.LightLocalCoverCost
