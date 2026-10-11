import Submission.ThreeSum.ReportingHostPositive
import Submission.ThreeSum.ReportingHostTerminalCosts

/-! # Exact physical frontier slots and a capacity computed from root raw mass -/

namespace ThreeSum.ReportingHostFrontierLayout

open Light Finset ThreeSum.SubsetAddress
open BlockRows BlockIndex BlockIndexedQuery BlockForced StoredReporting GlobalEncoding LocalCoverBounds
open RawIncidences RawReporting LightBlockQuery ReportingHostMasks

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

def slot (base cap k : ℕ) : ℕ := base+k*(4+2*cap)
def left (base cap k : ℕ) : ℕ := slot base cap k+4
def right (base cap k : ℕ) : ℕ := left base cap k+cap

@[simp] theorem slot_zero (base cap : ℕ) : slot base cap 0=base := by simp [slot]
theorem slot_succ (base cap k : ℕ) : slot base cap (k+1)=slot base cap k+4+2*cap := by
  unfold slot; ring

theorem slot_mono {base cap i j : ℕ} (hij : i≤j) : slot base cap i≤slot base cap j := by
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _

theorem right_end (base cap k : ℕ) : right base cap k+cap=slot base cap (k+1) := by
  rw [slot_succ]
  unfold right left
  omega

theorem old_end {base cap i k : ℕ} (hik : i<k) :
    right base cap i+cap≤slot base cap k := by
  rw [right_end]
  exact slot_mono (by omega)

@[simp] theorem left_zero {J L : ℕ} (u : Fin J→Finset (Fin L)) : leftPrefix 0 u=∅ := by
  ext x
  simp [leftPrefix,prefixLeft,prefixIndices,join,indexSet]

@[simp] theorem right_zero {J L : ℕ} (Q u : Fin J→Finset (Fin L)) : rightPrefix 0 Q u=∅ := by
  exact left_zero (fun i => Q i\u i)

@[simp] theorem query_zero {J L : ℕ} (Q : Fin J→Finset (Fin L)) :
    querySet 0 Q=indexSet (flat Q) := by
  simp [querySet,remaining,prefixIndices,flat]

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

abbrev rootMass {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) : ℕ :=
  prefixQuery I w 0 []

theorem rootMass_eq {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) :
    rootMass I w=(domain I w).card := by
  simp [rootMass,prefixQuery,Reporting.mass,Subset.fiberMass]

def capacity {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) : ℕ :=
  (rootMass I w+1)*groupSize h

theorem group_pos (h : ℕ) : 0<groupSize h := Nat.choose_pos (by omega)

theorem capacity_pos {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) :
    0<capacity I w := Nat.mul_pos (by omega) (group_pos h)

theorem mass_lt_capacity {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) :
    rootMass I w<capacity I w :=
  (Nat.lt_succ_self _).trans_le (Nat.le_mul_of_pos_right _ (group_pos h))

theorem frontier_capacity {h J k : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (hk : k≤J) : (ReportingHostFrontier.frontier I w k).length≤capacity I w := by
  have hh := ReportingHostFrontier.frontier_length_le_domain I w hk
  rw [← rootMass_eq I w] at hh
  exact hh.trans (mass_lt_capacity I w).le

theorem expansion_capacity {h J k : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (hk : k≤J) : (ReportingHostFrontier.frontier I w k).length*groupSize h≤capacity I w := by
  have hh := ReportingHostFrontier.frontier_length_le_domain I w hk
  rw [← rootMass_eq I w] at hh
  exact Nat.mul_le_mul_right (groupSize h) (hh.trans (Nat.le_succ _))

theorem frontier_zero {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) :
    ReportingHostFrontier.frontier I w 0=if 0<rootMass I w then [[]] else [] := rfl

def leftMasks {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) (k : ℕ) : List ℕ :=
  (ReportingHostFrontier.frontier I w k).map fun pre => subsetMask (leftPrefix k (prefixRows (J := J) pre))

def rightMasks {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) (k : ℕ) : List ℕ :=
  (ReportingHostFrontier.frontier I w k).map fun pre =>
    subsetMask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) pre))

@[simp] theorem leftMasks_length {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) (k : ℕ) :
    (leftMasks I w k).length=(ReportingHostFrontier.frontier I w k).length := by simp [leftMasks]
@[simp] theorem rightMasks_length {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) (k : ℕ) :
    (rightMasks I w k).length=(ReportingHostFrontier.frontier I w k).length := by simp [rightMasks]

theorem leftMasks_zero {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) :
    leftMasks I w 0=if 0<rootMass I w then [0] else [] := by
  unfold leftMasks
  rw [frontier_zero]
  split <;> simp

theorem rightMasks_zero {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) :
    rightMasks I w 0=if 0<rootMass I w then [0] else [] := by
  unfold rightMasks
  rw [frontier_zero]
  split <;> simp

structure At {h J : ℕ} (μ : ℕ→ℤ) (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (base cap k : ℕ) : Prop where
  count : μ (slot base cap k)=((ReportingHostFrontier.frontier I w k).length : ℤ)
  query : μ (slot base cap k+1)=(subsetMask (querySet k (outputRows w.2.2)) : ℤ)
  left : SegN μ (ReportingHostFrontierLayout.left base cap k) (leftMasks I w k)
  right : SegN μ (ReportingHostFrontierLayout.right base cap k) (rightMasks I w k)

theorem At.of_kept {h J k base cap stop : ℕ} {μ ν : ℕ→ℤ}
    {I : Finset (RawItem h J α β γ)} {w : Wanted h J α}
    (H : At μ I w base cap k) (hcap : (ReportingHostFrontier.frontier I w k).length≤cap)
    (hend : slot base cap (k+1)≤stop) (hkeep : Kept μ ν stop) : At ν I w base cap k := by
  have he := right_end base cap k
  have hL : ReportingHostFrontierLayout.left base cap k+cap≤stop := by unfold ReportingHostFrontierLayout.right at he; omega
  have hR : ReportingHostFrontierLayout.right base cap k+cap≤stop := by omega
  constructor
  · exact (hkeep _ (by unfold ReportingHostFrontierLayout.left at hL; omega)).trans H.count
  · exact (hkeep _ (by unfold ReportingHostFrontierLayout.left at hL; omega)).trans H.query
  · intro i hi
    have hi' : i<(ReportingHostFrontier.frontier I w k).length := by simpa only [List.length_map,leftMasks_length] using hi
    exact (hkeep _ (by omega)).trans (H.left i hi)
  · intro i hi
    have hi' : i<(ReportingHostFrontier.frontier I w k).length := by simpa only [List.length_map,rightMasks_length] using hi
    exact (hkeep _ (by omega)).trans (H.right i hi)

end ThreeSum.ReportingHostFrontierLayout
