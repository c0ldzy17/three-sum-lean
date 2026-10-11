import Submission.ThreeSum.LightBandRawARow
import Submission.ThreeSumApsp.Lang.Tasks

/-! # The three retained parallel arrays of A-value incidences -/

namespace ThreeSum.BandRawA

open Light BandCandidateRows

set_option maxHeartbeats 1400000

structure Stored (μ : ℕ → ℤ) (vals owners positions : ℕ)
    (f : ℕ → ℤ) (ls : List Label) : Prop where
  valueRows : Seg μ vals (values f ls)
  ownerRows : Seg μ owners (ownerLabels ls)
  positionRows : Seg μ positions (positionLabels ls)

theorem Stored.empty (μ : ℕ → ℤ) (vals owners positions : ℕ) (f : ℕ → ℤ) :
    Stored μ vals owners positions f [] := ⟨by simp [values],by simp [ownerLabels],by simp [positionLabels]⟩

theorem Stored.append {μ : ℕ → ℤ} {vals owners positions : ℕ} {f : ℕ → ℤ} {as bs : List Label}
    (H : Stored μ vals owners positions f as)
    (K : Stored μ (vals+as.length) (owners+as.length) (positions+as.length) f bs) :
    Stored μ vals owners positions f (as++bs) := by
  constructor
  · rw [values,List.map_append]
    exact seg_append.mpr ⟨H.valueRows,by simpa only [values,List.length_map] using K.valueRows⟩
  · rw [ownerLabels,List.map_append]
    exact seg_append.mpr ⟨H.ownerRows,by simpa only [ownerLabels,List.length_map] using K.ownerRows⟩
  · rw [positionLabels,List.map_append]
    exact seg_append.mpr ⟨H.positionRows,by simpa only [positionLabels,List.length_map] using K.positionRows⟩

theorem row_position_lt {n g owner j : ℕ} {r : Record}
    (hj : j < (row n g owner r).length) : BandPartition.start g r.a+j < n := by
  rw [row_length] at hj
  split_ifs at hj with hf
  · have hh := BandPartition.stop_le n g r.a
    unfold bandLength at hj
    omega
  · omega

theorem row_stored {μ : ℕ → ℤ} {vals owners positions n g owner : ℕ}
    {r : Record} {f : ℕ → ℤ}
    (H : ∀ j < (row n g owner r).length,
      μ (vals+j)=f (BandPartition.start g r.a+j) ∧ μ (owners+j)=(owner : ℤ) ∧
        μ (positions+j)=((BandPartition.start g r.a+j : ℕ) : ℤ)) :
    Stored μ vals owners positions f (row n g owner r) := by
  constructor
  · intro j hj
    have hj' : j < (row n g owner r).length := by simpa only [values_length] using hj
    dsimp only [values] at hj ⊢
    rw [List.getElem_map,row_getElem hj']
    exact (H j hj').1
  · intro j hj
    have hj' : j < (row n g owner r).length := by simpa only [ownerLabels_length] using hj
    dsimp only [ownerLabels] at hj ⊢
    rw [List.getElem_map,row_getElem hj']
    exact (H j hj').2.1
  · intro j hj
    have hj' : j < (row n g owner r).length := by simpa only [positionLabels_length] using hj
    dsimp only [positionLabels] at hj ⊢
    rw [List.getElem_map,row_getElem hj']
    exact (H j hj').2.2

theorem Stored.keep_before_append {μ ν : ℕ → ℤ} {vals owners positions capacity len : ℕ}
    {f : ℕ → ℤ} {ls : List Label}
    (H : Stored μ vals owners positions f ls)
    (hk : LightBandRawARow.KeptOthers μ ν (vals+ls.length) (owners+ls.length)
      (positions+ls.length) len)
    (hvals : vals+capacity ≤ owners) (howners : owners+capacity ≤ positions)
    (hfit : ls.length+len ≤ capacity) : Stored ν vals owners positions f ls := by
  constructor
  · apply H.valueRows.congr
    intro j hj
    have hj' : j < ls.length := by simpa only [values_length] using hj
    exact hk _ ⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega)⟩
  · apply H.ownerRows.congr
    intro j hj
    have hj' : j < ls.length := by simpa only [ownerLabels_length] using hj
    exact hk _ ⟨Or.inr (by omega),Or.inl (by omega),Or.inl (by omega)⟩
  · apply H.positionRows.congr
    intro j hj
    have hj' : j < ls.length := by simpa only [positionLabels_length] using hj
    exact hk _ ⟨Or.inr (by omega),Or.inr (by omega),Or.inl (by omega)⟩

theorem Stored.of_kept {μ ν : ℕ → ℤ} {vals owners positions fr : ℕ}
    {f : ℕ → ℤ} {ls : List Label} (H : Stored μ vals owners positions f ls)
    (hk : Kept μ ν fr) (hv : vals+ls.length ≤ fr)
    (ho : owners+ls.length ≤ fr) (hp : positions+ls.length ≤ fr) :
    Stored ν vals owners positions f ls :=
  ⟨H.valueRows.of_kept hk (by simpa only [values_length] using hv),
    H.ownerRows.of_kept hk (by simpa only [ownerLabels_length] using ho),
    H.positionRows.of_kept hk (by simpa only [positionLabels_length] using hp)⟩

end ThreeSum.BandRawA
