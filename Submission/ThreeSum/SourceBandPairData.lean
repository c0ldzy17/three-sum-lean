import Submission.ThreeSum.SourceBandData

/-! # Two retained original-band catalogs and one shared empty histogram -/

namespace ThreeSum.SourceBandPairData

open Light BandPartition

def leftBase (base : ℕ) : ℕ := base+8
def rightBase (base NL g m : ℕ) : ℕ := SourceBandLayout.work (leftBase base) NL g m
def zeroBase (base NL NR g m : ℕ) : ℕ := SourceBandLayout.work (rightBase base NL g m) NR g m
def next (base NL NR g m : ℕ) : ℕ := zeroBase base NL NR g m+m+1

theorem work_ge (base n g m : ℕ) : base ≤ SourceBandLayout.work base n g m := by
  unfold SourceBandLayout.work SourceBandLayout.hist SourceBandLayout.data
  omega

theorem ordered (base NL NR g m : ℕ) :
    leftBase base ≤ rightBase base NL g m ∧
    rightBase base NL g m ≤ zeroBase base NL NR g m ∧
    zeroBase base NL NR g m < next base NL NR g m := by
  exact ⟨work_ge _ _ _ _,work_ge _ _ _ _,by unfold next; omega⟩

def header (base NL NR g m : ℕ) : List ℤ :=
  [leftBase base,size NL g,rightBase base NL g m,size NR g,
    zeroBase base NL NR g m,next base NL NR g m,NL,NR]

structure Data (μ : ℕ → ℤ) (fL fR : ℕ → ℤ) (base NL NR g p m : ℕ) (shift : ℤ) : Prop where
  left : ∀ i < size NL g, SourceBandData.At μ fL (leftBase base) NL g p m 0 i
  right : ∀ i < size NR g, SourceBandData.At μ fR (rightBase base NL g m) NR g p m shift i
  zero : ∀ r ≤ m, μ (zeroBase base NL NR g m+r)=0

structure Stored (μ : ℕ → ℤ) (fL fR : ℕ → ℤ) (base NL NR g p m : ℕ) (shift : ℤ)
    extends Data μ fL fR base NL NR g p m shift : Prop where
  heads : Seg μ base (header base NL NR g m)

theorem Data.transfer {μ ν : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g p m : ℕ} {shift : ℤ}
    (H : Data μ fL fR base NL NR g p m shift) (hm : 0 < m)
    (K : ∀ a, leftBase base ≤ a → ν a=μ a) : Data ν fL fR base NL NR g p m shift := by
  have ho := ordered base NL NR g m
  refine ⟨?_,?_,?_⟩
  · intro i hi
    apply (H.left i hi).transfer hm
    · intro q _
      exact K _ (by omega)
    · intro a ha _
      have hb := SourceBandLayout.data_le_hist (leftBase base) NL g m i
      unfold SourceBandLayout.data at hb
      exact K _ (by omega)
  · intro i hi
    apply (H.right i hi).transfer hm
    · intro q _
      exact K _ (by omega)
    · intro a ha _
      have hb := SourceBandLayout.data_le_hist (rightBase base NL g m) NR g m i
      unfold SourceBandLayout.data at hb
      exact K _ (by omega)
  · intro r hr
    exact (K _ (by omega)).trans (H.zero r hr)

theorem Stored.of_kept {μ ν : ℕ → ℤ} {fL fR : ℕ → ℤ}
    {base NL NR g p m bound : ℕ} {shift : ℤ}
    (H : Stored μ fL fR base NL NR g p m shift) (hm : 0 < m)
    (K : Kept μ ν bound) (hb : next base NL NR g m ≤ bound) :
    Stored ν fL fR base NL NR g p m shift := by
  have ho := ordered base NL NR g m
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · intro i hi
    exact (H.left i hi).of_kept hm hi K (by change rightBase base NL g m ≤ bound; omega)
  · intro i hi
    exact (H.right i hi).of_kept hm hi K (by change zeroBase base NL NR g m ≤ bound; omega)
  · intro r hr
    exact (K _ (by unfold next at hb; omega)).trans (H.zero r hr)
  · intro i hi
    have hi' : i < 8 := by simpa only [header,List.length_cons,List.length_nil] using hi
    exact (K _ (by unfold leftBase at ho; omega)).trans (H.heads i hi)

theorem Data.empty_buckets {μ : ℕ → ℤ} {fL fR : ℕ → ℤ}
    {base NL NR g p m : ℕ} {shift : ℤ}
    (H : Data μ fL fR base NL NR g p m shift) (key : ℕ → ℕ) :
    SourceBuckets.Stored μ key 0 m (zeroBase base NL NR g m) (next base NL NR g m) := by
  refine ⟨?_,?_⟩
  · intro r hr
    simpa only [SourceBuckets.offset,LightHistogram.count_zero,Finset.sum_const_zero,Nat.cast_zero]
      using H.zero r hr
  · intro i hi
    omega

theorem Data.empty_histogram {μ : ℕ → ℤ} {fL fR v : ℕ → ℤ}
    {base NL NR g p m : ℕ} {shift d : ℤ}
    (H : Data μ fL fR base NL NR g p m shift) (r : ℕ) (hr : r < m) :
    μ (zeroBase base NL NR g m+r)=
      (LightBlockSourceRetainedStages.histogram p m d v 0 r : ℤ) := by
  simpa only [LightBlockSourceRetainedStages.histogram,LightHistogram.count_zero,Nat.cast_zero]
    using H.zero r hr.le

end ThreeSum.SourceBandPairData
