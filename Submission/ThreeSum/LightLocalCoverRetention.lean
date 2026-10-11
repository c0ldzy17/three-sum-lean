import Submission.ThreeSum.LightLocalCoverInit

/-! # Retained local-cover tables survive reuse of the returned free region -/

namespace ThreeSum.LightLocalCoverRetention

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMetadata

set_option maxHeartbeats 1000000

theorem base_le_nextFree (base h : ℕ) : base ≤ nextFree base h := by
  unfold nextFree scheduleMaps work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr
    LightCoverGreedy.total
  omega

theorem table_ends_le (base h : ℕ) :
    maps base h+rows h*(2*(512*h)) ≤ nextFree base h ∧
    hist0 base h+rows h*localPrime h ≤ nextFree base h ∧
    hist1 base h+rows h*localPrime h ≤ nextFree base h ∧
    matrixPtr base h+rows h*cols h ≤ nextFree base h ∧
    candidates base h+scheduleSize h ≤ nextFree base h := by
  unfold nextFree scheduleMaps candidates work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr
    LightCoverGreedy.total LightCoverGreedy.out
  omega

theorem data_of_kept {μ ν : ℕ → ℤ} {base h : ℕ}
    (H : Data μ h (maps base h) (hist0 base h) (hist1 base h) (matrixPtr base h))
    (K : Kept μ ν (nextFree base h)) :
    Data ν h (maps base h) (hist0 base h) (hist1 base h) (matrixPtr base h) := by
  obtain ⟨hm,hl,hr,hx,_⟩ := table_ends_le base h
  exact H.of_kept K hm hl hr hx

theorem rows_of_kept {μ ν : ℕ → ℤ} {base h : ℕ}
    (H : ScheduleRows μ h (scheduleMaps base h))
    (K : Kept μ ν (nextFree base h)) :
    ScheduleRows ν h (scheduleMaps base h) := by
  intro s hs i hi
  have hm := Nat.mul_le_mul_right (2*(512*h)) (show s+1 ≤ scheduleSize h by omega)
  simp only [Nat.add_mul,one_mul] at hm
  rw [K _ (by unfold nextFree; omega),K _ (by unfold nextFree; omega)]
  exact H s hs i hi

theorem indices_of_kept {μ ν : ℕ → ℤ} {base h : ℕ}
    (H : ∀ s : Occurrence h, μ (candidates base h+s.val) = (candidateAt h s : ℤ))
    (K : Kept μ ν (nextFree base h)) :
    ∀ s : Occurrence h, ν (candidates base h+s.val) = (candidateAt h s : ℤ) := by
  intro s
  have he := (table_ends_le base h).2.2.2.2
  rw [K _ (by have hs := s.isLt; omega)]
  exact H s

theorem header_of_kept {μ ν : ℕ → ℤ} {free h : ℕ}
    (H : Seg μ free (LightLocalCoverInit.values free h))
    (K : Kept μ ν (nextFree (LightLocalCoverInit.base free) h)) :
    Seg ν free (LightLocalCoverInit.values free h) := by
  have he : free+20 ≤ nextFree (LightLocalCoverInit.base free) h :=
    base_le_nextFree (LightLocalCoverInit.base free) h
  apply H.congr
  intro i hi
  have hi' : i < 20 := by
    simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,values] using hi
  exact K _ (by omega)

theorem nextFree_le_space (base h : ℕ) : nextFree base h ≤ space base h :=
  schedule_end_le_space base h

end ThreeSum.LightLocalCoverRetention
