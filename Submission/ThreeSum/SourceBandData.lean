import Submission.ThreeSum.SourceBandLayout
import Submission.ThreeSum.LightBlockSourceRetainedStages

/-! # Retained original-band headers, histograms, and physical position fibers -/

namespace ThreeSum.SourceBandData

open Light BandPartition SourceBandLayout

structure At (μ : ℕ → ℤ) (f : ℕ → ℤ) (base n g p m : ℕ) (shift : ℤ) (i : ℕ) : Prop where
  headStart : μ (base+6*i) = (start g i : ℤ)
  headLength : μ (base+6*i+1) = (len n g i : ℤ)
  headCodes : μ (base+6*i+2) = (codes base n g m i : ℤ)
  headHist : μ (base+6*i+3) = (hist base n g m i : ℤ)
  headOffsets : μ (base+6*i+4) = (offsets base n g m i : ℤ)
  headFlat : μ (base+6*i+5) = (flat base n g m i : ℤ)
  codesRead : ∀ j < len n g i, μ (codes base n g m i+j) = (key f g p m shift i j : ℤ)
  histRead : ∀ r < m, μ (hist base n g m i+r) = (LightHistogram.count (key f g p m shift i) r (len n g i) : ℤ)
  buckets : SourceBuckets.Stored μ (key f g p m shift i) (len n g i) m
    (offsets base n g m i) (flat base n g m i)

theorem At.transfer {μ ν : ℕ → ℤ} {f : ℕ → ℤ} {base n g p m i : ℕ} {shift : ℤ}
    (H : At μ f base n g p m shift i) (hm : 0 < m)
    (hhead : ∀ q < 6, ν (base+6*i+q)=μ (base+6*i+q))
    (hdata : ∀ x, hist base n g m i ≤ x → x < flat base n g m i+cap n g → ν x=μ x) :
    At ν f base n g p m shift i := by
  have hcap := len_le_cap n g i
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,⟨?_,?_⟩⟩
  · simpa only [Nat.add_zero] using (hhead 0 (by omega)).trans H.headStart
  · exact (hhead 1 (by omega)).trans H.headLength
  · exact (hhead 2 (by omega)).trans H.headCodes
  · exact (hhead 3 (by omega)).trans H.headHist
  · exact (hhead 4 (by omega)).trans H.headOffsets
  · exact (hhead 5 (by omega)).trans H.headFlat
  · intro j hj
    rw [hdata _ (by unfold codes; omega) (by unfold flat cursor offsets codes; omega)]
    exact H.codesRead j hj
  · intro r hr
    rw [hdata _ (by omega) (by unfold flat cursor offsets codes; omega)]
    exact H.histRead r hr
  · intro r hr
    rw [hdata _ (by unfold offsets codes; omega) (by unfold flat cursor; omega)]
    exact H.buckets.offsets r hr
  · intro j hj
    have hp := SourceBuckets.position_lt (fun q _ => key_lt (f := f) (g := g) (p := p) (shift := shift) hm i q) hj
    rw [hdata _ (by unfold flat cursor offsets codes; omega) (by omega)]
    exact H.buckets.indices j hj

theorem At.of_later {μ ν : ℕ → ℤ} {f : ℕ → ℤ} {base n g p m i k : ℕ} {shift : ℤ}
    (H : At μ f base n g p m shift i)
    (K : KeptBut μ ν (hist base n g m k) (base+6*k) 6)
    (hm : 0 < m) (hik : i < k) (hk : k < size n g) :
    At ν f base n g p m shift i := by
  have he := header_end (m := m) (base := base) hk
  have hb := data_le_hist base n g m i
  have hf := flat_end_le_later (base := base) (n := n) (g := g) (m := m) hik
  unfold data at hb
  apply H.transfer hm
  · intro q hq
    exact K _ ⟨by omega,Or.inl (by omega)⟩
  · intro x hx hxe
    exact K _ ⟨by omega,Or.inr (by omega)⟩

theorem At.of_kept {μ ν : ℕ → ℤ} {f : ℕ → ℤ} {base n g p m i bound : ℕ} {shift : ℤ}
    (H : At μ f base n g p m shift i) (hm : 0 < m) (hi : i < size n g)
    (K : Kept μ ν bound) (hbound : work base n g m ≤ bound) :
    At ν f base n g p m shift i := by
  have he := header_end (base := base) (m := m) hi
  have hf := flat_end_le_work (base := base) (m := m) hi
  have hh : hist base n g m i ≤ flat base n g m i+cap n g := by
    unfold flat cursor offsets codes
    omega
  apply H.transfer hm
  · intro q hq
    exact K _ (by omega)
  · intro x _ hxe
    exact K _ (by omega)

theorem At.histogram_for_host {μ : ℕ → ℤ} {f : ℕ → ℤ} {base n g p m i : ℕ} {shift : ℤ}
    (H : At μ f base n g p m shift i) (r : ℕ) (hr : r < m) :
    μ (hist base n g m i+r) =
      (LightBlockSourceRetainedStages.histogram p m shift (fun j => f (start g i+j)) (len n g i) r : ℤ) :=
  H.histRead r hr

def positions (μ : ℕ → ℤ) (base n g m i r : ℕ) : List ℕ :=
  (SourceBucketView.indices μ (offsets base n g m i) (flat base n g m i) r).map (fun j => start g i+j)

theorem At.mem_positions {μ : ℕ → ℤ} {f : ℕ → ℤ} {base n g p m i r t : ℕ} {shift : ℤ}
    (H : At μ f base n g p m shift i) (hm : 0 < m) (hg : 0 < g)
    (hi : i < size n g) (hr : r < m) :
    t ∈ positions μ base n g m i r ↔
      start g i ≤ t ∧ t < stop n g i ∧ LightSourceResidues.key p m shift (f t)=r := by
  have hs := start_add_len hg hi
  unfold positions
  rw [List.mem_map]
  constructor
  · rintro ⟨j,hj,rfl⟩
    obtain ⟨hj,hkey⟩ := (SourceBucketView.mem_indices H.buckets
      (fun q _ => key_lt (f := f) (g := g) (p := p) (shift := shift) hm i q) hr).mp hj
    exact ⟨by omega,by omega,hkey⟩
  · rintro ⟨hlo,hhi,hkey⟩
    have ht : start g i+(t-start g i)=t := by omega
    refine ⟨t-start g i,?_,ht⟩
    apply (SourceBucketView.mem_indices H.buckets
      (fun q _ => key_lt (f := f) (g := g) (p := p) (shift := shift) hm i q) hr).mpr
    exact ⟨by omega,by simpa only [key,ht] using hkey⟩

theorem At.nodup_positions {μ : ℕ → ℤ} {f : ℕ → ℤ} {base n g p m i r : ℕ} {shift : ℤ}
    (H : At μ f base n g p m shift i) (hm : 0 < m) (hr : r < m) :
    (positions μ base n g m i r).Nodup := by
  apply (SourceBucketView.nodup_indices H.buckets
    (fun q _ => key_lt (f := f) (g := g) (p := p) (shift := shift) hm i q) hr).map
  intro x y hxy
  exact Nat.add_left_cancel hxy

end ThreeSum.SourceBandData
