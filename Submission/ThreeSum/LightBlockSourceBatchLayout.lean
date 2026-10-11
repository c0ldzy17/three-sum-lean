import Submission.ThreeSum.LightZetaStages

/-!
# Packed retained source banks indexed by occurrence vectors

Each bank retains its compact masks, coefficients, endpoints, flags, and
both complete source-stage families. Shared temporary transform workspace
follows all banks. Two header cells per occurrence contain the stage bases.
This layout lets the next actual source call preserve every earlier bank.
-/

namespace ThreeSum.LightBlockSourceBatchLayout

open SubsetAddress LightZetaStages

def family (W cut : ℕ) : ℕ := (W+1)*downsetCap W cut
def stride (W cut : ℕ) : ℕ := 5*downsetCap W cut+2*W+2+2*family W cut
def banks (base count : ℕ) : ℕ := base+2*count
def slot (base count W cut i : ℕ) : ℕ := banks base count+i*stride W cut
def coeff0 (base count W cut i : ℕ) : ℕ := slot base count W cut i+downsetCap W cut
def coeff1 (base count W cut i : ℕ) : ℕ := coeff0 base count W cut i+W
def rawLeft (base count W cut i : ℕ) : ℕ := coeff1 base count W cut i+W
def rawRight (base count W cut i : ℕ) : ℕ := rawLeft base count W cut i+downsetCap W cut
def flags (base count W cut i : ℕ) : ℕ := rawRight base count W cut i+downsetCap W cut
def leftBase (base count W cut i : ℕ) : ℕ := flags base count W cut i+2*downsetCap W cut+2
def rightBase (base count W cut i : ℕ) : ℕ := leftBase base count W cut i+family W cut
def maskBase (base count W cut : ℕ) : ℕ := slot base count W cut count
def bitBase (base count W cut : ℕ) : ℕ := maskBase base count W cut+downsetCap W cut
def rowOut (base count W cut : ℕ) : ℕ := bitBase base count W cut+W
def work (base count W cut : ℕ) : ℕ := rowOut base count W cut+2

theorem banks_le_slot (base count W cut i : ℕ) : banks base count ≤ slot base count W cut i :=
  Nat.le_add_right _ _

theorem slot_mono (base count W cut : ℕ) : Monotone (slot base count W cut) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _

theorem left_ge_slot (base count W cut i : ℕ) :
    slot base count W cut i ≤ leftBase base count W cut i := by
  unfold leftBase flags rawRight rawLeft coeff1 coeff0
  omega

theorem right_ge_left (base count W cut i : ℕ) :
    leftBase base count W cut i ≤ rightBase base count W cut i := Nat.le_add_right _ _

theorem right_end (base count W cut i : ℕ) :
    rightBase base count W cut i+family W cut = slot base count W cut (i+1) := by
  unfold rightBase leftBase flags rawRight rawLeft coeff1 coeff0 slot stride
  ring

theorem right_end_le_masks {base count W cut i : ℕ} (hi : i < count) :
    rightBase base count W cut i+family W cut ≤ maskBase base count W cut := by
  rw [right_end]
  exact slot_mono base count W cut (by omega)

theorem slot_le_masks {base count W cut i : ℕ} (hi : i ≤ count) :
    slot base count W cut i ≤ maskBase base count W cut := slot_mono base count W cut hi

theorem banks_le_work (base count W cut : ℕ) : banks base count ≤ work base count W cut := by
  have hm := banks_le_slot base count W cut count
  unfold work rowOut bitBase maskBase
  omega

theorem slot_width_le_work {base count W cut i : ℕ} (hi : i < count) :
    slot base count W cut i+W ≤ work base count W cut := by
  have hr := right_end_le_masks (base := base) (W := W) (cut := cut) hi
  unfold rightBase leftBase flags rawRight rawLeft coeff1 coeff0 family at hr
  unfold work rowOut bitBase
  omega

theorem header_end_le_slot {base count W cut i : ℕ} (hi : i < count) :
    base+2*i+2 ≤ slot base count W cut i := by
  have hb := banks_le_slot base count W cut i
  unfold banks at hb
  omega

theorem masks_le_work (base count W cut : ℕ) :
    maskBase base count W cut ≤ work base count W cut := by
  unfold work rowOut bitBase
  omega

theorem addresses_le_work {base count W cut i : ℕ} (hi : i < count) :
    coeff0 base count W cut i ≤ work base count W cut ∧
    coeff1 base count W cut i ≤ work base count W cut ∧
    rawLeft base count W cut i ≤ work base count W cut ∧
    rawRight base count W cut i ≤ work base count W cut ∧
    flags base count W cut i ≤ work base count W cut ∧
    leftBase base count W cut i ≤ work base count W cut ∧
    rightBase base count W cut i ≤ work base count W cut := by
  have he := (right_end_le_masks hi).trans (masks_le_work base count W cut)
  unfold rightBase leftBase flags rawRight rawLeft coeff1 coeff0 at he ⊢
  omega

theorem stage_cell_lt_end {W cut base j : ℕ} {S : Finset (Fin W)}
    (hj : j ≤ W) (hS : S.card ≤ cut) :
    stageBase base (downsetCap W cut) j+subsetRank S < base+family W cut := by
  have hr := subsetRank_lt hS
  have hm := Nat.mul_le_mul_right (downsetCap W cut) (Nat.succ_le_succ hj)
  calc
    _ < base+j*downsetCap W cut+downsetCap W cut := Nat.add_lt_add_left hr _
    _ = base+(j+1)*downsetCap W cut := by ring
    _ ≤ base+(W+1)*downsetCap W cut := Nat.add_le_add_left hm _
    _ = _ := rfl

theorem left_cell_lt_next {base count W cut i j : ℕ} {S : Finset (Fin W)}
    (hj : j ≤ W) (hS : S.card ≤ cut) :
    stageBase (leftBase base count W cut i) (downsetCap W cut) j+subsetRank S <
      slot base count W cut (i+1) := by
  have hs := stage_cell_lt_end (base := leftBase base count W cut i) hj hS
  have he := right_end base count W cut i
  unfold rightBase at he
  omega

theorem right_cell_lt_next {base count W cut i j : ℕ} {S : Finset (Fin W)}
    (hj : j ≤ W) (hS : S.card ≤ cut) :
    stageBase (rightBase base count W cut i) (downsetCap W cut) j+subsetRank S <
      slot base count W cut (i+1) := by
  rw [← right_end]
  exact stage_cell_lt_end hj hS

theorem left_cell_lt_later {base count W cut i k j : ℕ} {S : Finset (Fin W)}
    (hik : i < k) (hj : j ≤ W) (hS : S.card ≤ cut) :
    stageBase (leftBase base count W cut i) (downsetCap W cut) j+subsetRank S <
      slot base count W cut k :=
  (left_cell_lt_next hj hS).trans_le (slot_mono base count W cut (by omega))

theorem right_cell_lt_later {base count W cut i k j : ℕ} {S : Finset (Fin W)}
    (hik : i < k) (hj : j ≤ W) (hS : S.card ≤ cut) :
    stageBase (rightBase base count W cut i) (downsetCap W cut) j+subsetRank S <
      slot base count W cut k :=
  (right_cell_lt_next hj hS).trans_le (slot_mono base count W cut (by omega))

theorem banks_le_left_cell (base count W cut i j : ℕ) (S : Finset (Fin W)) :
    banks base count ≤ stageBase (leftBase base count W cut i) (downsetCap W cut) j+subsetRank S := by
  have hs := (banks_le_slot base count W cut i).trans (left_ge_slot base count W cut i)
  unfold stageBase
  omega

theorem banks_le_right_cell (base count W cut i j : ℕ) (S : Finset (Fin W)) :
    banks base count ≤ stageBase (rightBase base count W cut i) (downsetCap W cut) j+subsetRank S := by
  have hs := ((banks_le_slot base count W cut i).trans
    (left_ge_slot base count W cut i)).trans (right_ge_left base count W cut i)
  unfold stageBase
  omega

end ThreeSum.LightBlockSourceBatchLayout
