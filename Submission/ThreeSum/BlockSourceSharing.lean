import Submission.ThreeSum.BlockIndexedQuery
import Submission.ThreeSum.LightZetaStages
import Submission.ThreeSum.LightSourceGather
import Submission.ThreeSum.ReportingHostSuffixCosts
import Submission.ThreeSum.StageBounds

/-!
# Exact sharing of source transforms and the encoder ledger

Source stages are indexed by a source band and an occurrence vector. The
output subset and the three-valued A lift do not enter the source function.
Compact table and zeta charges below match the existing `encoderCount`
without introducing a factor for all complete global outputs.
-/

namespace ThreeSum.BlockSourceSharing

open BlockEncoding GlobalEncoding BlockIndexedQuery SubsetAddress
open Scales TrimScales CostLedger StageBounds

theorem leftSource_eq_of_occurrences {β : Type*} [Fintype β] [DecidableEq β]
    {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ) {q q' : GlobalOutput h J}
    (he : outputOccurrences q = outputOccurrences q') :
    leftSource P B b q = leftSource P B b q' := by
  unfold leftSource
  rw [he]

theorem rightSource_eq_of_occurrences {β : Type*} [Fintype β] [DecidableEq β]
    {h J : ℕ} (P d : ℤ) (B : Finset β) (b : β → ℤ) {q q' : GlobalOutput h J}
    (he : outputOccurrences q = outputOccurrences q') :
    rightSource P d B b q = rightSource P d B b q' := by
  unfold rightSource
  rw [he]

theorem stored_left_reuse {β : Type*} [Fintype β] [DecidableEq β]
    {h J base cut : ℕ} {μ : ℕ → ℤ} (P : ℤ) (B : Finset β) (b : β → ℤ)
    {q q' : GlobalOutput h J} (he : outputOccurrences q = outputOccurrences q')
    (hs : LightZetaStages.StoredThrough μ base cut (leftSource P B b q) (J*(512*h))) :
    LightZetaStages.StoredThrough μ base cut (leftSource P B b q') (J*(512*h)) := by
  rw [← leftSource_eq_of_occurrences P B b he]
  exact hs

theorem stored_right_reuse {β : Type*} [Fintype β] [DecidableEq β]
    {h J base cut : ℕ} {μ : ℕ → ℤ} (P d : ℤ) (B : Finset β) (b : β → ℤ)
    {q q' : GlobalOutput h J} (he : outputOccurrences q = outputOccurrences q')
    (hs : LightZetaStages.StoredThrough μ base cut (rightSource P d B b q) (J*(512*h))) :
    LightZetaStages.StoredThrough μ base cut (rightSource P d B b q') (J*(512*h)) := by
  rw [← rightSource_eq_of_occurrences P d B b he]
  exact hs

theorem occurrence_card (h J : ℕ) : Fintype.card (Occurrences h J) = scheduleSize h^J := by
  simp only [Occurrences,Occurrence,Fintype.card_fun,Fintype.card_fin]

theorem occurrence_card_eq_scheduleCount (n : ℕ) :
    Fintype.card (Occurrences (microHalf (inputBits n)) (blockCount (inputBits n))) = scheduleCount n := by
  rw [occurrence_card,scheduleCount,replicatedHalf,localLength,scheduleSize_eq_length]

theorem width_eq (n : ℕ) :
    blockCount (inputBits n)*(512*microHalf (inputBits n)) = 256*mu n := by
  unfold mu totalSize microSize microHalf
  ring

theorem cutoff_eq (n : ℕ) :
    2*microHalf (inputBits n)*blockCount (inputBits n) = mu n := by
  unfold mu totalSize microSize microHalf
  ring

theorem downset_le_fullOutputs (n : ℕ) :
    downsetCap (256*mu n) (mu n) ≤ (mu n+1)*fullOutputs n :=
  ReportingHostSuffixCosts.downsetCap_le_layer (by omega)

theorem downset_add_one_le_fullOutputs (n : ℕ) :
    downsetCap (256*mu n) (mu n)+1 ≤ (256*mu n+2)*fullOutputs n :=
  ReportingHostSuffixCosts.downsetCap_add_one_le_layer (by omega)

def sourceCells (n : ℕ) : ℕ :=
  2*bandCount n*scheduleCount n*downsetCap (256*mu n) (mu n)

theorem sourceCells_le_encoderCount (n : ℕ) :
    sourceCells n ≤ (mu n+1)*encoderCount n := by
  calc
    _ ≤ 2*bandCount n*scheduleCount n*((mu n+1)*fullOutputs n) :=
      Nat.mul_le_mul_left _ (downset_le_fullOutputs n)
    _ = _ := by unfold encoderCount; ring

def zetaWork (n : ℕ) : ℕ :=
  2*bandCount n*scheduleCount n*LightZetaStages.time (256*mu n) (mu n)

theorem zetaWork_le_encoderCount (n : ℕ) :
    zetaWork n ≤ 12000*(256*mu n+1)^5*encoderCount n := by
  have ht := LightZetaStages.time_bound (show mu n ≤ 256*mu n by omega)
  have hd := downset_add_one_le_fullOutputs n
  have hh : LightZetaStages.time (256*mu n) (mu n) ≤
      12000*(256*mu n+1)^5*fullOutputs n := by
    calc
      _ ≤ 6000*(256*mu n+1)^4*((256*mu n+2)*fullOutputs n) :=
        ht.trans (Nat.mul_le_mul_left _ hd)
      _ ≤ 6000*(256*mu n+1)^4*((2*(256*mu n+1))*fullOutputs n) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      _ = _ := by ring
  calc
    _ ≤ 2*bandCount n*scheduleCount n*(12000*(256*mu n+1)^5*fullOutputs n) :=
      Nat.mul_le_mul_left _ hh
    _ = _ := by unfold encoderCount; ring

def gatherWork (n E : ℕ) : ℕ :=
  2*bandCount n*scheduleCount n*LightSourceGather.time (downsetCap (256*mu n) (mu n)) E

theorem gatherWork_le_encoderCount (n E : ℕ) :
    gatherWork n E ≤ 326*(256*mu n+1)*(Nat.log 2 (E+1)+1)*encoderCount n := by
  have ht := LightSourceGather.time_bound (downsetCap (256*mu n) (mu n)) E
  have hd := downset_add_one_le_fullOutputs n
  have hh : LightSourceGather.time (downsetCap (256*mu n) (mu n)) E ≤
      326*(256*mu n+1)*(Nat.log 2 (E+1)+1)*fullOutputs n := by
    calc
      _ ≤ 163*(downsetCap (256*mu n) (mu n)+1)*(Nat.log 2 (E+1)+1) := by nlinarith
      _ ≤ 163*((256*mu n+2)*fullOutputs n)*(Nat.log 2 (E+1)+1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 163 hd)
      _ ≤ 163*((2*(256*mu n+1))*fullOutputs n)*(Nat.log 2 (E+1)+1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 163 (Nat.mul_le_mul_right _ (by omega)))
      _ = _ := by ring
  calc
    _ ≤ 2*bandCount n*scheduleCount n*(326*(256*mu n+1)*(Nat.log 2 (E+1)+1)*fullOutputs n) :=
      Nat.mul_le_mul_left _ hh
    _ = _ := by unfold encoderCount; ring

end ThreeSum.BlockSourceSharing
