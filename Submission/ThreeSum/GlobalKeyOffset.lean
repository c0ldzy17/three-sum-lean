import Submission.ThreeSum.GlobalKeyEnumeration
import Submission.ThreeSum.LightOriginalOffset
import Submission.ThreeSum.RawReporting

/-!
# The actual array-selected offset balances original output records

The program's right histogram is indexed by literal key-array positions.
This module transports that count bijectively to the original global output
type, retaining distinct outputs that happen to have equal integer keys.
-/

namespace ThreeSum.GlobalKeyOffset

open GlobalEncoding GlobalKeyEnumeration
open scoped BigOperators

set_option maxHeartbeats 1800000

noncomputable def recordEquiv (h J : ℕ) : Fin (globalRecords h J).length ≃ GlobalOutput h J :=
  Equiv.ofBijective (globalRecords h J).get
    ⟨(globalRecords_nodup h J).injective_get,fun q => List.mem_iff_get.mp (mem_globalRecords h J q)⟩

theorem keys_length_records (h J : ℕ) : (globalKeys h J).length=(globalRecords h J).length := by
  rw [globalKeys_eq_map,List.length_map]

theorem key_getD_record (h J : ℕ) (i : Fin (globalRecords h J).length) :
    (globalKeys h J).getD i.val 0=globalKey (recordEquiv h J i) := by
  rw [globalKeys_eq_map,List.getD_eq_getElem _ _ (by simpa only [List.length_map] using i.isLt),
    List.getElem_map]
  rfl

/-- Raw left incidences are array positions, even when their values coincide. -/
def wantedCount (p : ℕ) (left : List ℤ) (h J : ℕ) (d : ℤ) : ℕ :=
  ∑ i : Fin left.length, ∑ q : GlobalOutput h J,
    if (globalKey q : ZMod p)-(left.getD i.val 0 : ZMod p)=(d : ZMod p) then 1 else 0

theorem pairMass_eq_wantedCount (p : ℕ) [NeZero p] (left : List ℤ) (h J : ℕ) (d : ℤ) :
    Histograms.pairMass (Finset.range left.length) (Finset.range (globalKeys h J).length)
      (fun i => (left.getD i 0 : ZMod p))
      (fun i => ((globalKeys h J).getD i 0 : ZMod p))
      (fun _ => 1) (fun _ => 1) (d : ZMod p) = wantedCount p left h J d := by
  unfold Histograms.pairMass wantedCount
  rw [keys_length_records,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Fin.sum_univ_eq_sum_range]
  apply Fintype.sum_equiv (recordEquiv h J)
  intro j
  dsimp only
  simp only [key_getD_record,one_mul]

def selected (p : ℕ) [NeZero p] (left : List ℤ) (h J : ℕ) : ℕ :=
  LightOriginalOffset.selected p (fun i => left.getD i 0)
    (fun i => (globalKeys h J).getD i 0) left.length (globalKeys h J).length

theorem selected_lt (p : ℕ) [NeZero p] (left : List ℤ) (h J : ℕ) :
    selected p left h J < p := LightOriginalOffset.selected_lt ..

theorem selected_wanted_bound (p : ℕ) [NeZero p] (left : List ℤ) (h J : ℕ) :
    p*wantedCount p left h J (selected p left h J) ≤
      left.length*(scheduleSize h^J*LocalCoverBounds.outputCount (512*h) h^J) := by
  have hh := LightOriginalOffset.selected_pairMass_bound p
    (fun i => left.getD i 0) (fun i => (globalKeys h J).getD i 0)
    left.length (globalKeys h J).length
  have hmass := pairMass_eq_wantedCount p left h J (selected p left h J)
  simp only [Int.cast_natCast] at hmass
  rw [← hmass]
  simpa only [selected,globalKeys_length] using hh

theorem residue_relation_iff (p : ℕ) (left right d : ℤ) :
    (right : ZMod p)-(left : ZMod p)=(d : ZMod p) ↔ (p : ℤ) ∣ left+d-right := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,Int.cast_sub,Int.cast_add,sub_eq_zero]
  constructor
  · intro hh
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp hh).symm
  · intro hh
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using hh.symm

theorem wantedCount_eq_divisibility (p : ℕ) (left : List ℤ) (h J : ℕ) (d : ℤ) :
    wantedCount p left h J d =
      ∑ i : Fin left.length, ∑ q : GlobalOutput h J,
        if (p : ℤ) ∣ left.getD i.val 0+d-globalKey q then 1 else 0 := by
  simp only [wantedCount,residue_relation_iff]

end ThreeSum.GlobalKeyOffset
