import Submission.ThreeSum.LightCoverKeys

/-!
# The retained cover, output layers, and exact global key array

This bundle is produced by the actual cover/key host and remains valid when
later phases use its computed next free address. In particular the output
index decoder can read the original layer masks without reconstructing them.
-/

namespace ThreeSum.LightCoverKeyData

open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000

def keyEnd (free h J : ℕ) : ℕ :=
  LightCoverKeys.keyHeader free h J+1+LightGlobalKeys.localCount h^J

theorem global_length (h J : ℕ) : (globalKeys h J).length=LightGlobalKeys.localCount h^J := by
  simp only [globalKeys_length,LightGlobalKeys.localCount,mul_pow]

theorem layer_end_le_header (free h J : ℕ) :
    LightCoverKeys.afterCover free h+outputCount (512*h) h ≤ LightCoverKeys.keyHeader free h J := by
  unfold LightCoverKeys.keyHeader LightGlobalKeys.scratch
  omega

theorem afterCover_le_keyEnd (free h J : ℕ) : LightCoverKeys.afterCover free h ≤ keyEnd free h J := by
  have hh := layer_end_le_header free h J
  unfold keyEnd
  omega

theorem free_le_keyEnd (free h J : ℕ) : free ≤ keyEnd free h J := by
  have hh := LightLocalCoverRetention.base_le_nextFree (LightLocalCoverInit.base free) h
  have hk := afterCover_le_keyEnd free h J
  change free+20 ≤ LightCoverKeys.afterCover free h at hh
  omega

theorem keyEnd_le_space (free h J : ℕ) : keyEnd free h J ≤ LightCoverKeys.space free h J := by
  have hg : LightRadixKeys.space (LightGlobalKeys.scratch (LightCoverKeys.afterCover free h) h)
      (LightGlobalKeys.localCount h) J ≤ LightGlobalKeys.space (LightCoverKeys.afterCover free h) h J :=
    le_max_right _ _
  exact hg.trans (le_max_right _ _)

structure Stored (μ : ℕ → ℤ) (free h J : ℕ) : Prop where
  count : μ (LightCoverKeys.keyHeader free h J)=((LightGlobalKeys.localCount h^J : ℕ) : ℤ)
  keys : Seg μ (LightCoverKeys.keyHeader free h J+1) (globalKeys h J)
  header : Seg μ free (LightLocalCoverInit.values free h)
  data : Data μ h (maps (LightLocalCoverInit.base free) h)
    (hist0 (LightLocalCoverInit.base free) h) (hist1 (LightLocalCoverInit.base free) h)
    (matrixPtr (LightLocalCoverInit.base free) h)
  rows : ScheduleRows μ h (scheduleMaps (LightLocalCoverInit.base free) h)
  indices : ∀ s : Occurrence h, μ (candidates (LightLocalCoverInit.base free) h+s.val)=
    (candidateAt h s : ℤ)
  masks : ∀ i < outputCount (512*h) h, μ (LightCoverKeys.afterCover free h+i)=
    (LocalMaskGraph.maskAt (512*h) (2*h) i : ℤ)

theorem Stored.of_kept {μ ν : ℕ → ℤ} {free h J : ℕ} (H : Stored μ free h J)
    (K : Kept μ ν (keyEnd free h J)) : Stored ν free h J := by
  have hafter := afterCover_le_keyEnd free h J
  have hafterK : Kept μ ν (LightCoverKeys.afterCover free h) := fun i hi => K i (by omega)
  refine ⟨?_,?_,LightLocalCoverRetention.header_of_kept H.header hafterK,
    LightLocalCoverRetention.data_of_kept H.data hafterK,
    LightLocalCoverRetention.rows_of_kept H.rows hafterK,
    LightLocalCoverRetention.indices_of_kept H.indices hafterK,?_⟩
  · rw [K _ (by unfold keyEnd; omega)]
    exact H.count
  · apply H.keys.congr
    intro i hi
    rw [global_length] at hi
    exact K _ (by unfold keyEnd; omega)
  · intro i hi
    have hh := layer_end_le_header free h J
    rw [K _ (by unfold keyEnd; omega)]
    exact H.masks i hi

theorem program_meets {lim : Limits} {μ : ℕ → ℤ} {h J free d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+J+11 ≤ lim.depth)
    (hspace : LightCoverKeys.space free h J ≤ lim.space)
    (hword : (LightCoverKeys.word h J : ℤ) ≤ lim.word) :
    Meets lim LightCoverKeys.program 67 d [h,J,free] μ (LightCoverKeys.time h J)
      (fun r ν => r=(LightCoverKeys.keyHeader free h J : ℤ) ∧ Stored ν free h J ∧ Kept μ ν free) := by
  exact (LightCoverKeys.programProcs.meets_with_masks hw hd hspace hword).mono le_rfl
    (fun _ _ ⟨hr,hc,hk,hh,hd,hs,hi,hm,hkeep⟩ => ⟨hr,⟨hc,hk,hh,hd,hs,hi,hm⟩,hkeep⟩)

end ThreeSum.LightCoverKeyData
