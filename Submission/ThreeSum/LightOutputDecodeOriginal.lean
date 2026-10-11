import Submission.ThreeSum.LightOutputDecode

/-!
# The actual decoder specializes to the original global output record

The physical right-hand key index selects exactly the unchanged original
record, even when several records have equal key values. This module
identifies the two constructed rows with that record's original schedule
occurrences and Q masks, and exposes the source occurrence array directly.
-/

namespace ThreeSum.LightOutputDecodeOriginal

open Light GlobalEncoding OutputDecodeRecords

set_option maxHeartbeats 1200000

abbrev output (h J k : ℕ) : GlobalOutput h J :=
  (GlobalKeyEnumeration.globalRecords h J).getD k (outputDefault h J)

structure Rows (ν : ℕ → ℤ) (dst h J k : ℕ) : Prop where
  occurrences : ∀ j : Fin J, ν (dst+j.val)=(((output h J k j).1.val : ℕ) : ℤ)
  masks : ∀ j : Fin J,
    ν (dst+J+j.val)=(SubsetAddress.subsetMask (output h J k j).2.val : ℤ)

theorem Rows.source_occurrences {ν : ℕ → ℤ} {dst h J k : ℕ}
    (H : Rows ν dst h J k) {j : ℕ} (hj : j < J) :
    ν (dst+j)=
      (BlockCoefficientRows.occurrenceIndices
        (BlockEncoding.outputOccurrences (output h J k)) j : ℤ) := by
  rw [BlockCoefficientRows.occurrenceIndices_fin _ ⟨j,hj⟩]
  exact H.occurrences ⟨j,hj⟩

theorem Rows.of_kept {ν ξ : ℕ → ℤ} {dst h J k fr : ℕ}
    (H : Rows ν dst h J k) (hkeep : Kept ν ξ fr) (hfit : dst+J+J ≤ fr) :
    Rows ξ dst h J k := by
  constructor
  · intro j
    rw [hkeep _ (by have hj := j.isLt; omega)]
    exact H.occurrences j
  · intro j
    rw [hkeep _ (by have hj := j.isLt; omega)]
    exact H.masks j

theorem mask_bound (h : ℕ) {s : ℕ} (hs : s < layerCount h) :
    LocalMaskGraph.maskAt (512*h) (2*h) s ≤ 2^(512*h) :=
  (LocalMaskGraph.maskAt_spec hs).1.le

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {h J k masks dst work V : ℕ}

theorem meets {pMain : ℕ} (S : LightOutputDecode.Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hk : k < localCount h^J) (hkV : k ≤ V)
    (hmask : masks+layerCount h ≤ dst) (hsep : dst+J+J ≤ work)
    (hspace : LightOutputDecode.space work V ≤ lim.space)
    (hword : (LightOutputDecode.word V (scheduleSize h) (layerCount h) J (2^(512*h)) : ℤ) ≤ lim.word)
    (hread : ∀ s < layerCount h,
      μ (masks+s)=(LocalMaskGraph.maskAt (512*h) (2*h) s : ℤ)) :
    Meets lim P pMain d [k,J,scheduleSize h,layerCount h,masks,dst,work] μ
      (LightOutputDecode.time J V)
      (fun r ν =>
        r=(OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J k : ℤ) ∧
        Rows ν dst h J k ∧ Kept μ ν dst) := by
  refine (S.meets hw hd (schedule_pos h) (layerCount_pos h) hkV hmask hsep
    hspace hword (fun s hs => mask_bound h hs) hread).mono le_rfl ?_
  rintro r ν ⟨hr,hocc,hmasks,hkeep⟩
  refine ⟨hr,⟨?_,?_⟩,hkeep⟩
  · intro j
    rw [original_occurrence_index hk j]
    exact hocc j.val j.isLt
  · intro j
    rw [original_output_mask hk j]
    exact hmasks j.val j.isLt

theorem program_meets
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hk : k < localCount h^J) (hkV : k ≤ V)
    (hmask : masks+layerCount h ≤ dst) (hsep : dst+J+J ≤ work)
    (hspace : LightOutputDecode.space work V ≤ lim.space)
    (hword : (LightOutputDecode.word V (scheduleSize h) (layerCount h) J (2^(512*h)) : ℤ) ≤ lim.word)
    (hread : ∀ s < layerCount h,
      μ (masks+s)=(LocalMaskGraph.maskAt (512*h) (2*h) s : ℤ)) :
    Meets lim LightOutputDecode.program 0 d
      [k,J,scheduleSize h,layerCount h,masks,dst,work] μ
      (LightOutputDecode.time J V)
      (fun r ν =>
        r=(OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J k : ℤ) ∧
        Rows ν dst h J k ∧ Kept μ ν dst) :=
  meets LightOutputDecode.programProcs hw hd hk hkV hmask hsep hspace hword hread

end ThreeSum.LightOutputDecodeOriginal
