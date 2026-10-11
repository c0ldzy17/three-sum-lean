import Submission.ThreeSum.LightBlockSourceCatalogProgram
import Submission.ThreeSum.BlockSourceStageCosts

/-!
# Exact shared-bank dimensions and charge of the actual catalog

There are two stage families for each original band and occurrence vector.
The decoder and bank-loop overhead are included. Neither the number of
complete output subsets nor the three-valued query lift multiplies this
construction.
-/

namespace ThreeSum.BlockSourceCatalogCosts

open Scales TrimScales StageBounds CostLedger BlockSourceSharing SubsetAddress
open LightBlockSourceBatchLayout

theorem count_eq_scheduleCount (n : ℕ) :
    LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n)) =
      scheduleCount n := by
  unfold LightBlockSourceCatalog.count
  rw [← occurrence_card,occurrence_card_eq_scheduleCount]

theorem work_address (base count W cut : ℕ) :
    LightBlockSourceBatchLayout.work base count W cut =
      base+count*(stride W cut+2)+downsetCap W cut+W+2 := by
  unfold LightBlockSourceBatchLayout.work rowOut bitBase maskBase slot banks
  ring

theorem stride_add_two_le (W cut : ℕ) :
    stride W cut+2 ≤ (2*W+7)*(downsetCap W cut+1) := by
  unfold stride family
  nlinarith

/-- The number of retained stage families, before counting their cells. -/
def stageFamilyCount (n : ℕ) : ℕ :=
  2*bandCount n*LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n))

theorem stageFamilyCount_eq (n : ℕ) : stageFamilyCount n = 2*bandCount n*scheduleCount n := by
  unfold stageFamilyCount
  rw [count_eq_scheduleCount]

/-- Every family has one compact table for each suffix stage. -/
def stageCellCount (n : ℕ) : ℕ :=
  stageFamilyCount n*family (256*mu n) (mu n)

theorem stageCellCount_eq (n : ℕ) :
    stageCellCount n = 2*bandCount n*scheduleCount n*(256*mu n+1)*
      downsetCap (256*mu n) (mu n) := by
  unfold stageCellCount family
  rw [stageFamilyCount_eq]
  ring

theorem stageCellCount_le_encoderCount (n : ℕ) :
    stageCellCount n ≤ (256*mu n+1)*(mu n+1)*encoderCount n := by
  rw [stageCellCount_eq]
  calc
    _ ≤ 2*bandCount n*scheduleCount n*(256*mu n+1)*((mu n+1)*fullOutputs n) :=
      Nat.mul_le_mul_left _ (downset_le_fullOutputs n)
    _ = _ := by unfold encoderCount; ring

def work (n : ℕ) : ℕ := bandCount n*LightBlockSourceCatalog.time
  (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n)

theorem work_le_encoderCount (n : ℕ) :
    work n ≤ LightBlockSourceCatalogProgram.factor
      (microHalf (inputBits n)) (blockCount (inputBits n))*(256*mu n+2)*encoderCount n := by
  have hcut : mu n ≤ blockCount (inputBits n)*(512*microHalf (inputBits n)) := by
    rw [width_eq]
    omega
  have ht := LightBlockSourceCatalogProgram.time_bound hcut
  rw [width_eq] at ht
  have hcpos : 0 < LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n)) :=
    pow_pos (OutputDecodeRecords.schedule_pos (microHalf (inputBits n))) _
  have hc : LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n))+1 ≤
      2*LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n)) := by omega
  have hd := downset_add_one_le_fullOutputs n
  unfold work
  calc
    _ ≤ bandCount n*((LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n))+1)*
        LightBlockSourceCatalogProgram.factor (microHalf (inputBits n)) (blockCount (inputBits n))*
        (downsetCap (256*mu n) (mu n)+1)) := Nat.mul_le_mul_left _ ht
    _ ≤ bandCount n*((2*LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n)))*
        LightBlockSourceCatalogProgram.factor (microHalf (inputBits n)) (blockCount (inputBits n))*
        ((256*mu n+2)*fullOutputs n)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul_right _ hc) hd)
    _ = _ := by rw [count_eq_scheduleCount]; unfold encoderCount; ring

/-- Occurrence rows and persistent bank records, excluding reusable scratch. -/
def catalogCells (n : ℕ) : ℕ :=
  bandCount n*scheduleCount n*(blockCount (inputBits n)+stride (256*mu n) (mu n)+2)

theorem catalogCells_le_encoderCount (n : ℕ) :
    catalogCells n ≤ (blockCount (inputBits n)+2*(256*mu n)+7)*(256*mu n+2)*encoderCount n := by
  have hstride := stride_add_two_le (256*mu n) (mu n)
  have hJ : blockCount (inputBits n) ≤
      blockCount (inputBits n)*(downsetCap (256*mu n) (mu n)+1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hslot : blockCount (inputBits n)+stride (256*mu n) (mu n)+2 ≤
      (blockCount (inputBits n)+2*(256*mu n)+7)*(downsetCap (256*mu n) (mu n)+1) := by
    nlinarith
  have hd := downset_add_one_le_fullOutputs n
  have he : bandCount n*scheduleCount n*fullOutputs n ≤ encoderCount n := by
    calc
      _ ≤ 2*(bandCount n*scheduleCount n*fullOutputs n) :=
        Nat.le_mul_of_pos_left _ (by omega)
      _ = encoderCount n := by unfold encoderCount; ring
  unfold catalogCells
  calc
    _ ≤ bandCount n*scheduleCount n*((blockCount (inputBits n)+2*(256*mu n)+7)*
        ((256*mu n+2)*fullOutputs n)) :=
      Nat.mul_le_mul_left _ (hslot.trans (Nat.mul_le_mul_left _ hd))
    _ = (blockCount (inputBits n)+2*(256*mu n)+7)*(256*mu n+2)*
        (bandCount n*scheduleCount n*fullOutputs n) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ he

end ThreeSum.BlockSourceCatalogCosts
