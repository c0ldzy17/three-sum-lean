import Submission.ThreeSum.BandRawAMemory

/-!
# Physical incidence indices and their exact owner coordinates

An incidence at position `count owner + localA` retains that physical
owner and its sorted A coordinate. Every emitted index has exactly this
form, including equal values emitted by different owners.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows

set_option maxHeartbeats 1700000
set_option maxRecDepth 7000

def labelAt (n g : ℕ) (rs : List Record) (i : ℕ) : Label :=
  (items n g rs).getD i default

def ownerRecord (n g : ℕ) (rs : List Record) (i : ℕ) : Record :=
  rs.getD (labelAt n g rs i).owner default

def localA (n g : ℕ) (rs : List Record) (i : ℕ) : ℕ :=
  (labelAt n g rs i).position-BandPartition.start g (ownerRecord n g rs i).a

theorem index_lt_firstRows {n g s i j : ℕ} {rs : List Record}
    (hs : s < i) (hj : j < (row n g s (rs.getD s default)).length) :
    count n g rs s+j < (firstRows n g rs i).length := by
  have hm := count_mono n g rs (show s+1 ≤ i by omega)
  rw [count_succ] at hm
  change count n g rs s+j < count n g rs i
  omega

theorem index_lt_items {n g s j : ℕ} {rs : List Record}
    (hs : s < rs.length) (hj : j < (row n g s (rs.getD s default)).length) :
    count n g rs s+j < (items n g rs).length := index_lt_firstRows hs hj

theorem firstRows_getD {n g s i j : ℕ} {rs : List Record}
    (hs : s < i) (hj : j < (row n g s (rs.getD s default)).length) :
    (firstRows n g rs i).getD (count n g rs s+j) default=
      ⟨s,BandPartition.start g (rs.getD s default).a+j⟩ := by
  induction i with
  | zero => omega
  | succ i ih =>
    rw [firstRows_succ]
    by_cases hsi : s < i
    · rw [List.getD_append _ _ _ _ (index_lt_firstRows hsi hj)]
      exact ih hsi
    · have he : s=i := by omega
      subst s
      rw [List.getD_append_right _ _ _ _ (by change count n g rs i ≤ count n g rs i+j; omega)]
      change (row n g i (rs.getD i default)).getD (count n g rs i+j-count n g rs i) default=_
      rw [Nat.add_sub_cancel_left,List.getD_eq_getElem _ _ hj,row_getElem hj]

theorem items_getD {n g s j : ℕ} {rs : List Record}
    (hs : s < rs.length) (hj : j < (row n g s (rs.getD s default)).length) :
    labelAt n g rs (count n g rs s+j)=
      ⟨s,BandPartition.start g (rs.getD s default).a+j⟩ := firstRows_getD hs hj

theorem firstRows_index {n g i k : ℕ} {rs : List Record}
    (hk : k < (firstRows n g rs i).length) :
    ∃ s < i, ∃ j < (row n g s (rs.getD s default)).length,
      k=count n g rs s+j := by
  induction i with
  | zero => simp at hk
  | succ i ih =>
    by_cases hki : k < (firstRows n g rs i).length
    · obtain ⟨s,hs,j,hj,he⟩ := ih hki
      exact ⟨s,by omega,j,hj,he⟩
    · have hlen : (firstRows n g rs (i+1)).length=
          count n g rs i+(row n g i (rs.getD i default)).length := by
        rw [firstRows_succ,List.length_append]
        rfl
      rw [hlen] at hk
      change ¬ k < count n g rs i at hki
      exact ⟨i,by omega,k-count n g rs i,by omega,by omega⟩

theorem items_index {n g k : ℕ} {rs : List Record}
    (hk : k < (items n g rs).length) :
    ∃ s < rs.length, ∃ j < (row n g s (rs.getD s default)).length,
      k=count n g rs s+j := firstRows_index hk

theorem at_mem {n g k : ℕ} {rs : List Record}
    (hk : k < (items n g rs).length) : labelAt n g rs k ∈ items n g rs := by
  rw [labelAt,List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

theorem at_bounds {n g k : ℕ} {rs : List Record}
    (hk : k < (items n g rs).length) :
    (labelAt n g rs k).owner < rs.length ∧
      (ownerRecord n g rs k).flag=1 ∧
      BandPartition.start g (ownerRecord n g rs k).a ≤ (labelAt n g rs k).position ∧
      (labelAt n g rs k).position < BandPartition.stop n g (ownerRecord n g rs k).a := by
  have hh := mem_firstRows.mp (at_mem hk)
  have hr := mem_row.mp hh.2
  exact ⟨hh.1,hr.1,hr.2.2.1,hr.2.2.2⟩

theorem index_eq_owner_local {n g k : ℕ} {rs : List Record}
    (hk : k < (items n g rs).length) :
    k=count n g rs (labelAt n g rs k).owner+localA n g rs k := by
  obtain ⟨s,hs,j,hj,rfl⟩ := items_index hk
  rw [localA,ownerRecord,items_getD hs hj]
  dsimp only [Label.owner,Label.position]
  omega

theorem localA_lt {n g k : ℕ} {rs : List Record}
    (hk : k < (items n g rs).length) :
    localA n g rs k < bandLength n g (ownerRecord n g rs k).a := by
  have hh := at_bounds hk
  unfold localA bandLength
  omega

theorem at_injective {n g : ℕ} {rs : List Record} {i j : ℕ}
    (hi : i < (items n g rs).length) (hj : j < (items n g rs).length)
    (he : labelAt n g rs i=labelAt n g rs j) : i=j := by
  have hi' := index_eq_owner_local hi
  have hj' := index_eq_owner_local hj
  rw [localA,ownerRecord,he] at hi'
  rw [localA,ownerRecord] at hj'
  omega

theorem values_getD {n g k : ℕ} {rs : List Record} (f : ℕ → ℤ)
    (hk : k < (items n g rs).length) :
    (values f (items n g rs)).getD k 0=f (labelAt n g rs k).position := by
  unfold values labelAt
  rw [List.getD_map_of_lt _ hk default 0]

theorem values_getD_owner {n g s j : ℕ} {rs : List Record} (f : ℕ → ℤ)
    (hs : s < rs.length) (hj : j < (row n g s (rs.getD s default)).length) :
    (values f (items n g rs)).getD (count n g rs s+j) 0=
      f (BandPartition.start g (rs.getD s default).a+j) := by
  rw [values_getD f (index_lt_items hs hj),items_getD hs hj]

theorem Stored.read {μ : ℕ → ℤ} {vals owners positions n g k : ℕ}
    {rs : List Record} {f : ℕ → ℤ}
    (H : Stored μ vals owners positions f (items n g rs))
    (hk : k < (items n g rs).length) :
    μ (vals+k)=f (labelAt n g rs k).position ∧
      μ (owners+k)=((labelAt n g rs k).owner : ℤ) ∧
      μ (positions+k)=((labelAt n g rs k).position : ℤ) := by
  constructor
  · exact (H.valueRows.getD (by rw [values_length]; exact hk) 0).trans (values_getD f hk)
  · constructor
    · have hh := H.ownerRows.getD (by rw [ownerLabels_length]; exact hk) 0
      dsimp only [ownerLabels] at hh
      rw [List.getD_map_of_lt _ hk default 0] at hh
      exact hh
    · have hh := H.positionRows.getD (by rw [positionLabels_length]; exact hk) 0
      dsimp only [positionLabels] at hh
      rw [List.getD_map_of_lt _ hk default 0] at hh
      exact hh

end ThreeSum.BandRawA
