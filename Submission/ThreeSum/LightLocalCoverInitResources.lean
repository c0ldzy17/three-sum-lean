import Submission.ThreeSum.LightLocalCoverInit
import Submission.ThreeSum.LightLocalCoverResources

/-! # Resource bounds for the complete h-and-free local-cover initializer -/

namespace ThreeSum.LightLocalCoverInitResources

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout

set_option maxHeartbeats 1500000

def envelope (h : ℕ) : ℕ := 2^(5000000*(h+1)^2)

theorem parameters_envelope_le (h : ℕ) :
    LocalParameterBounds.envelope h ≤ LightLocalCoverResources.envelope h := by
  unfold LocalParameterBounds.envelope LightLocalCoverResources.envelope
  apply Nat.pow_le_pow_right (by decide)
  nlinarith only [Nat.zero_le (h*h)]

theorem constant_le (h : ℕ) : 600 ≤ LightLocalCoverResources.envelope h := by
  have hs : 1 ≤ (h+1)^2 := Nat.pow_pos (by omega)
  exact (by decide : 600 ≤ 2^10).trans
    (Nat.pow_le_pow_right (by decide) (by omega))

theorem four_envelope_le (h : ℕ) :
    4*LightLocalCoverResources.envelope h ≤ envelope h := by
  have hs : 1 ≤ (h+1)^2 := Nat.pow_pos (by omega)
  calc
    _ = 2^2*2^(4000000*(h+1)^2) := rfl
    _ = 2^(2+4000000*(h+1)^2) := (pow_add _ _ _).symm
    _ ≤ envelope h := Nat.pow_le_pow_right (by decide) (by omega)

theorem metadata_time_le (h : ℕ) :
    LightLocalCoverMetadata.time h ≤ LightLocalCoverSetup.time h+500 := by
  unfold LightLocalCoverMetadata.time LightLocalCoverSetup.time
  omega

theorem time_bound (h : ℕ) : LightLocalCoverInit.time h ≤ envelope h := by
  have hp := (LocalParameterBounds.time_bound h).trans (parameters_envelope_le h)
  have hc := LightLocalCoverResources.time_bound h
  have hm := metadata_time_le h
  have hk := constant_le h
  apply (show LightLocalCoverInit.time h ≤ 4*LightLocalCoverResources.envelope h from ?_).trans
    (four_envelope_le h)
  unfold LightLocalCoverInit.time
  omega

theorem word_bound (h : ℕ) : LightLocalCoverInit.word h ≤ envelope h := by
  have hp := (LocalParameterBounds.word_bound h).trans (parameters_envelope_le h)
  have hc := LightLocalCoverResources.word_bound h
  apply (show LightLocalCoverInit.word h ≤ 4*LightLocalCoverResources.envelope h from ?_).trans
    (four_envelope_le h)
  unfold LightLocalCoverInit.word
  omega

theorem space_bound (free h : ℕ) : LightLocalCoverInit.space free h ≤ free+envelope h := by
  have hp := (LocalParameterBounds.space_bound (LightLocalCoverInit.base free) h).trans
    (Nat.add_le_add_left (parameters_envelope_le h) (LightLocalCoverInit.base free))
  have hc := LightLocalCoverResources.space_bound (LightLocalCoverInit.base free) h
  have hk := constant_le h
  have hm : LightLocalCoverInit.space free h ≤ free+4*LightLocalCoverResources.envelope h := by
    unfold LightLocalCoverInit.space LightLocalCoverInit.base at *
    omega
  exact hm.trans (Nat.add_le_add_left (four_envelope_le h) free)

theorem depth_bound (h : ℕ) : 512*h+9 ≤ envelope h := by
  have hc := LightLocalCoverResources.depth_bound h
  have hk := constant_le h
  exact (by omega : 512*h+9 ≤ 4*LightLocalCoverResources.envelope h).trans (four_envelope_le h)

theorem envelope_le_search {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    envelope (Scales.microHalf (Scales.inputBits n)) ≤ Scales.localSearch 5000000 n := by
  unfold envelope Scales.localSearch
  rw [Scales.muZero_eq_twice_half]
  apply Nat.pow_le_pow_right (by decide)
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  omega

theorem time_le_search {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    LightLocalCoverInit.time (Scales.microHalf (Scales.inputBits n)) ≤ Scales.localSearch 5000000 n :=
  (time_bound _).trans (envelope_le_search hh)

theorem word_le_search {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    LightLocalCoverInit.word (Scales.microHalf (Scales.inputBits n)) ≤ Scales.localSearch 5000000 n :=
  (word_bound _).trans (envelope_le_search hh)

theorem space_le_search {n free : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    LightLocalCoverInit.space free (Scales.microHalf (Scales.inputBits n)) ≤
      free+Scales.localSearch 5000000 n :=
  (space_bound _ _).trans (Nat.add_le_add_left (envelope_le_search hh) free)

theorem depth_le_search {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    512*Scales.microHalf (Scales.inputBits n)+9 ≤ Scales.localSearch 5000000 n :=
  (depth_bound _).trans (envelope_le_search hh)

/-- Actual parameter selection and exact local cover from only h and free. -/
theorem meets_search {lim : Limits} {P : Program} {d pMain n free : ℕ}
    {μ : ℕ → ℤ} (S : LightLocalCoverInit.Procs P pMain)
    (hh : 1 ≤ Scales.microHalf (Scales.inputBits n))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d+Scales.localSearch 5000000 n ≤ lim.depth)
    (hspace : free+Scales.localSearch 5000000 n ≤ lim.space)
    (hword : (Scales.localSearch 5000000 n : ℤ) ≤ lim.word) :
    let h := Scales.microHalf (Scales.inputBits n)
    let base := LightLocalCoverInit.base free
    Meets lim P pMain d [h,free] μ (Scales.localSearch 5000000 n)
      (fun r ν => r = (LightLocalCoverMetadata.nextFree base h : ℤ) ∧
        Seg ν free (LightLocalCoverInit.values free h) ∧
        Data ν h (maps base h) (hist0 base h) (hist1 base h) (matrixPtr base h) ∧
        ScheduleRows ν h (scheduleMaps base h) ∧
        (∀ s : Occurrence h, ν (candidates base h+s.val) = (candidateAt h s : ℤ)) ∧
        Kept μ ν free) := by
  have hd' := depth_le_search hh
  exact (S.meets hw (by omega) ((space_le_search hh).trans hspace)
    ((Int.ofNat_le.mpr (word_le_search hh)).trans hword)).mono_time (time_le_search hh)


/-- The closed fixed program has no supplied procedure or data oracle. -/
theorem program_meets_search {lim : Limits} {d n free : ℕ} {μ : ℕ → ℤ}
    (hh : 1 ≤ Scales.microHalf (Scales.inputBits n))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d+Scales.localSearch 5000000 n ≤ lim.depth)
    (hspace : free+Scales.localSearch 5000000 n ≤ lim.space)
    (hword : (Scales.localSearch 5000000 n : ℤ) ≤ lim.word) :
    let h := Scales.microHalf (Scales.inputBits n)
    let base := LightLocalCoverInit.base free
    Meets lim LightLocalCoverInit.program 52 d [h,free] μ (Scales.localSearch 5000000 n)
      (fun r ν => r = (LightLocalCoverMetadata.nextFree base h : ℤ) ∧
        Seg ν free (LightLocalCoverInit.values free h) ∧
        Data ν h (maps base h) (hist0 base h) (hist1 base h) (matrixPtr base h) ∧
        ScheduleRows ν h (scheduleMaps base h) ∧
        (∀ s : Occurrence h, ν (candidates base h+s.val) = (candidateAt h s : ℤ)) ∧
        Kept μ ν free) :=
  meets_search LightLocalCoverInit.programProcs hh hw hd hspace hword

end ThreeSum.LightLocalCoverInitResources
