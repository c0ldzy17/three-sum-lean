import Submission.ThreeSum.SourceBandPairData
import Submission.ThreeSum.SourceBandPartition

/-! # Padded histogram selection for independently chosen original bands -/

namespace ThreeSum.SourceBandPairSlices

open Light BandPartition SourceBandLayout SourceBandPairData

def histogramPtr (base n g m zero i : ℕ) : ℕ :=
  if i < size n g then hist base n g m i else zero

def histLeft (base NL NR g m i : ℕ) : ℕ :=
  histogramPtr (leftBase base) NL g m (zeroBase base NL NR g m) i

def histRight (base NL NR g m i : ℕ) : ℕ :=
  histogramPtr (rightBase base NL g m) NR g m (zeroBase base NL NR g m) i

def count (NL NR g : ℕ) : ℕ := max (size NL g) (size NR g)

theorem histogram_end {base n g m zero i bound : ℕ}
    (hb : work base n g m ≤ bound) (hz : zero+m ≤ bound) :
    histogramPtr base n g m zero i+m ≤ bound := by
  unfold histogramPtr
  split_ifs with hi
  · have hh := flat_end_le_work (base := base) (m := m) hi
    unfold flat cursor offsets codes at hh
    omega
  · exact hz

theorem left_end (base NL NR g m i : ℕ) :
    histLeft base NL NR g m i+m ≤ next base NL NR g m := by
  have ho := ordered base NL NR g m
  exact histogram_end (by change rightBase base NL g m ≤ next base NL NR g m; omega)
    (by unfold next; omega)

theorem right_end (base NL NR g m i : ℕ) :
    histRight base NL NR g m i+m ≤ next base NL NR g m := by
  exact histogram_end (by change zeroBase base NL NR g m ≤ next base NL NR g m; unfold next; omega)
    (by unfold next; omega)

theorem left_histogram {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g p m i : ℕ} {shift : ℤ}
    (H : Data μ fL fR base NL NR g p m shift) (hg : 0 < g) (r : ℕ) (hr : r < m) :
    μ (histLeft base NL NR g m i+r)=
      (LightBlockSourceRetainedStages.histogram p m 0
        (fun j => fL (start g i+j)) (len NL g i) r : ℤ) := by
  by_cases hi : i < size NL g
  · simpa only [histLeft,histogramPtr,if_pos hi] using (H.left i hi).histogram_for_host r hr
  · rw [histLeft,histogramPtr,if_neg hi,SourceBandPartition.len_eq_zero hg (by omega)]
    exact H.empty_histogram r hr

theorem right_histogram {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g p m i : ℕ} {shift : ℤ}
    (H : Data μ fL fR base NL NR g p m shift) (hg : 0 < g) (r : ℕ) (hr : r < m) :
    μ (histRight base NL NR g m i+r)=
      (LightBlockSourceRetainedStages.histogram p m shift
        (fun j => fR (start g i+j)) (len NR g i) r : ℤ) := by
  by_cases hi : i < size NR g
  · simpa only [histRight,histogramPtr,if_pos hi] using (H.right i hi).histogram_for_host r hr
  · rw [histRight,histogramPtr,if_neg hi,SourceBandPartition.len_eq_zero hg (by omega)]
    exact H.empty_histogram r hr

theorem heads_read {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g p m : ℕ} {shift : ℤ}
    (H : Stored μ fL fR base NL NR g p m shift) :
    μ base=(leftBase base : ℤ) ∧ μ (base+1)=(size NL g : ℤ) ∧
    μ (base+2)=(rightBase base NL g m : ℤ) ∧ μ (base+3)=(size NR g : ℤ) ∧
    μ (base+4)=(zeroBase base NL NR g m : ℤ) ∧ μ (base+5)=(next base NL NR g m : ℤ) ∧
    μ (base+6)=(NL : ℤ) ∧ μ (base+7)=(NR : ℤ) := by
  exact ⟨by simpa [header] using H.heads.getD (i := 0) (by simp [header]) 0,
    by simpa [header] using H.heads.getD (i := 1) (by simp [header]) 0,
    by simpa [header] using H.heads.getD (i := 2) (by simp [header]) 0,
    by simpa [header] using H.heads.getD (i := 3) (by simp [header]) 0,
    by simpa [header] using H.heads.getD (i := 4) (by simp [header]) 0,
    by simpa [header] using H.heads.getD (i := 5) (by simp [header]) 0,
    by simpa [header] using H.heads.getD (i := 6) (by simp [header]) 0,
    by simpa [header] using H.heads.getD (i := 7) (by simp [header]) 0⟩

end ThreeSum.SourceBandPairSlices
