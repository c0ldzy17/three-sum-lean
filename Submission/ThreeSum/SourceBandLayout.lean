import Submission.ThreeSum.BandPartition
import Submission.ThreeSum.LightSourceBucketOriginal
import Submission.ThreeSum.SourceBucketView

/-! # Packed original-band histograms and exact physical residue fibers -/

namespace ThreeSum.SourceBandLayout

open BandPartition LightHistogram SourceBuckets

def cap (n g : ℕ) : ℕ := min n g
def len (n g i : ℕ) : ℕ := stop n g i-start g i
def stride (n g m : ℕ) : ℕ := 3*m+1+2*cap n g
def data (base n g : ℕ) : ℕ := base+6*size n g
def hist (base n g m i : ℕ) : ℕ := data base n g+i*stride n g m
def codes (base n g m i : ℕ) : ℕ := hist base n g m i+m
def offsets (base n g m i : ℕ) : ℕ := codes base n g m i+cap n g
def cursor (base n g m i : ℕ) : ℕ := offsets base n g m i+m+1
def flat (base n g m i : ℕ) : ℕ := cursor base n g m i+m
def work (base n g m : ℕ) : ℕ := hist base n g m (size n g)

theorem len_le_cap (n g i : ℕ) : len n g i ≤ cap n g := by
  have hn := stop_le n g i
  have hg := length_le n g i
  unfold len cap
  exact le_min (by omega) hg

theorem input_index {n g i j : ℕ} (hg : 0 < g) (hi : i < size n g) (hj : j < len n g i) :
    start g i+j < n := by
  have hlo := start_lt_stop hg hi
  have hhi := stop_le n g i
  unfold len at hj
  omega

theorem start_add_len {n g i : ℕ} (hg : 0 < g) (hi : i < size n g) :
    start g i+len n g i = stop n g i := by
  have hs := start_lt_stop hg hi
  unfold len
  omega

theorem capacity_product_le (n g : ℕ) (hg : 0 < g) : size n g*cap n g ≤ 2*n := by
  by_cases hgn : g ≤ n
  · rw [cap,min_eq_right hgn]
    exact (size_mul_le n g).trans (by omega)
  · by_cases hn : n=0
    · simp [hn,cap]
    · have hdiv : (n-1)/g=0 := Nat.div_eq_of_lt (by omega)
      simp only [cap,min_eq_left (by omega : n ≤ g),size,if_neg hn,hdiv,zero_add,one_mul]
      omega

theorem hist_mono (base n g m : ℕ) : Monotone (hist base n g m) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _

theorem data_le_hist (base n g m i : ℕ) : data base n g ≤ hist base n g m i :=
  Nat.le_add_right _ _

theorem flat_end (base n g m i : ℕ) :
    flat base n g m i+cap n g = hist base n g m (i+1) := by
  unfold flat cursor offsets codes hist stride
  ring

theorem header_end {base n g m i : ℕ} (hi : i < size n g) :
    base+6*i+6 ≤ hist base n g m i := by
  have hb := data_le_hist base n g m i
  unfold data at hb
  omega

theorem flat_end_le_work {base n g m i : ℕ} (hi : i < size n g) :
    flat base n g m i+cap n g ≤ work base n g m := by
  rw [flat_end]
  exact hist_mono base n g m (by omega)

theorem flat_end_le_later {base n g m i k : ℕ} (hik : i < k) :
    flat base n g m i+cap n g ≤ hist base n g m k := by
  rw [flat_end]
  exact hist_mono base n g m (by omega)

theorem work_bound (base n g m : ℕ) (hg : 0 < g) :
    work base n g m ≤ base+4*n+size n g*(3*m+7) := by
  have hc := capacity_product_le n g hg
  unfold work hist data stride
  nlinarith

theorem count_congr {key key' : ℕ → ℕ} {N t : ℕ}
    (he : ∀ i < N, key i=key' i) (ht : t ≤ N) (r : ℕ) :
    count key r t=count key' r t := by
  unfold count
  congr 1
  apply Finset.filter_congr
  intro i hi
  rw [he i ((Finset.mem_range.mp hi).trans_le ht)]

theorem offset_congr {key key' : ℕ → ℕ} {N : ℕ}
    (he : ∀ i < N, key i=key' i) (r : ℕ) :
    SourceBuckets.offset key N r=SourceBuckets.offset key' N r := by
  unfold SourceBuckets.offset
  apply Finset.sum_congr rfl
  intro s _
  exact count_congr he le_rfl s

theorem position_congr {key key' : ℕ → ℕ} {N i : ℕ}
    (he : ∀ j < N, key j=key' j) (hi : i < N) :
    position key N i=position key' N i := by
  unfold position
  rw [he i hi,offset_congr he,count_congr he hi.le]

theorem buckets_congr {μ : ℕ → ℤ} {key key' : ℕ → ℕ} {N M offsets flat : ℕ}
    (H : Stored μ key N M offsets flat) (he : ∀ i < N, key i=key' i) :
    Stored μ key' N M offsets flat := by
  refine ⟨?_,?_⟩
  · intro r hr
    rw [← offset_congr he]
    exact H.offsets r hr
  · intro i hi
    rw [← position_congr he hi]
    exact H.indices i hi

def key (f : ℕ → ℤ) (g p m : ℕ) (shift : ℤ) (i j : ℕ) : ℕ :=
  LightSourceResidues.key p m shift (f (start g i+j))

theorem key_lt {f : ℕ → ℤ} {g p m : ℕ} {shift : ℤ} (hm : 0 < m) (i j : ℕ) :
    key f g p m shift i j < m := LightSourceResidues.key_lt hm shift _

end ThreeSum.SourceBandLayout
