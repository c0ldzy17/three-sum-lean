import Submission.ThreeSum.LightLocalCoverTables
import Submission.ThreeSum.BlockSourceFlags

/-!
# Constructed local-cover output as source-encoding input

This adapter connects the actual cover builder's retained candidate tables
and gathered occurrence rows to the exact reads used by source preparation.
Occurrence order, repeated candidates, and both independent bucket tables
are preserved without further searching or histogram construction.
-/

namespace ThreeSum.BlockSourceCoverInput

open Light GlobalEncoding LocalCoverBounds BlockCoefficientRows BlockSourceFlags

structure Input (μ : ℕ → ℤ) (h maps candidates histL histR : ℕ) : Prop where
  candidates : ∀ s : Occurrence h,
    μ (candidates+s.val) = (LightLocalCoverSchedule.candidateAt h s : ℤ)
  leftRows : ∀ s < scheduleSize h, ∀ t < 512*h,
    μ (maps+2*(512*h)*s+t) = (mapRow h false s t : ℤ)
  rightRows : ∀ s < scheduleSize h, ∀ t < 512*h,
    μ (maps+2*(512*h)*s+512*h+t) = (mapRow h true s t : ℤ)
  leftCounts : ∀ k < LightLocalCoverSchedule.rows h, ∀ r < localPrime h,
    μ (histL+k*localPrime h+r) = (leftCount h k r : ℤ)
  rightCounts : ∀ k < LightLocalCoverSchedule.rows h, ∀ r < localPrime h,
    μ (histR+k*localPrime h+r) = (rightCount h k r : ℤ)

theorem of_cover {μ : ℕ → ℤ} {h allMaps matrix maps candidates histL histR : ℕ}
    (H : LightLocalCoverTables.Data μ h allMaps histL histR matrix)
    (R : LightLocalCoverTables.ScheduleRows μ h maps)
    (I : ∀ s : Occurrence h,
      μ (candidates+s.val) = (LightLocalCoverSchedule.candidateAt h s : ℤ)) :
    Input μ h maps candidates histL histR := by
  refine ⟨I,?_,?_,?_,?_⟩
  · intro s hs t ht
    simpa only [Nat.mul_comm s (2*(512*h))] using (R s hs t ht).1
  · intro s hs t ht
    simpa only [Nat.mul_comm s (2*(512*h))] using (R s hs t ht).2
  · intro k hk r hr
    exact (H.counts_read hk hr).1
  · intro k hk r hr
    exact (H.counts_read hk hr).2

theorem Input.of_kept {μ ν : ℕ → ℤ} {h maps candidates histL histR bound : ℕ}
    (H : Input μ h maps candidates histL histR) (K : Kept μ ν bound)
    (hmaps : maps+2*(512*h)*scheduleSize h ≤ bound)
    (hcandidates : candidates+scheduleSize h ≤ bound)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h ≤ bound)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h ≤ bound) :
    Input ν h maps candidates histL histR := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro s
    rw [K _ (by have hs := s.isLt; omega)]
    exact H.candidates s
  · intro s hs t ht
    have he := Nat.mul_le_mul_left (2*(512*h)) (show s+1 ≤ scheduleSize h by omega)
    simp only [Nat.mul_add,Nat.mul_one] at he
    rw [K _ (by omega)]
    exact H.leftRows s hs t ht
  · intro s hs t ht
    have he := Nat.mul_le_mul_left (2*(512*h)) (show s+1 ≤ scheduleSize h by omega)
    simp only [Nat.mul_add,Nat.mul_one] at he
    rw [K _ (by omega)]
    exact H.rightRows s hs t ht
  · intro k hk r hr
    have he := Nat.mul_le_mul_right (localPrime h) (show k+1 ≤ LightLocalCoverSchedule.rows h by omega)
    simp only [Nat.add_mul,Nat.one_mul] at he
    rw [K _ (by omega)]
    exact H.leftCounts k hk r hr
  · intro k hk r hr
    have he := Nat.mul_le_mul_right (localPrime h) (show k+1 ≤ LightLocalCoverSchedule.rows h by omega)
    simp only [Nat.add_mul,Nat.one_mul] at he
    rw [K _ (by omega)]
    exact H.rightCounts k hk r hr

end ThreeSum.BlockSourceCoverInput
