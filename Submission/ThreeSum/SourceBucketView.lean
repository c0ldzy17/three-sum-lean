import Submission.ThreeSum.SourceBuckets

/-! # Header-driven exact views of the retained original-index buckets -/

namespace ThreeSum.SourceBucketView

open SourceBuckets LightHistogram

def start (μ : ℕ → ℤ) (offsets r : ℕ) : ℕ := (μ (offsets+r)).toNat
def stop (μ : ℕ → ℤ) (offsets r : ℕ) : ℕ := (μ (offsets+r+1)).toNat
def length (μ : ℕ → ℤ) (offsets r : ℕ) : ℕ := stop μ offsets r-start μ offsets r
def indices (μ : ℕ → ℤ) (offsets flat r : ℕ) : List ℕ :=
  bucketList μ flat (start μ offsets r) (length μ offsets r)

theorem start_eq {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : Stored μ key N M offsets flat) (hr : r ≤ M) :
    start μ offsets r = offset key N r := by
  simp only [start,H.offsets r hr,Int.toNat_natCast]

theorem stop_eq {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : Stored μ key N M offsets flat) (hr : r < M) :
    stop μ offsets r = offset key N (r+1) := by
  unfold stop
  rw [Nat.add_assoc,H.offsets (r+1) (by omega),Int.toNat_natCast]

theorem length_eq {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : Stored μ key N M offsets flat) (hr : r < M) :
    length μ offsets r = count key r N := by
  rw [length,start_eq H (Nat.le_of_lt hr),stop_eq H hr,offset_succ]
  omega

theorem indices_eq {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : Stored μ key N M offsets flat) (hr : r < M) :
    indices μ offsets flat r = bucketList μ flat (offset key N r) (count key r N) := by
  rw [indices,start_eq H (Nat.le_of_lt hr),length_eq H hr]

theorem indices_length {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : Stored μ key N M offsets flat) (hr : r < M) :
    (indices μ offsets flat r).length = count key r N := by
  rw [indices_eq H hr,bucketList_length]

theorem mem_indices {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r i : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M) (hr : r < M) :
    i ∈ indices μ offsets flat r ↔ i < N ∧ key i = r := by
  rw [indices_eq H hr]
  exact H.mem_bucketList hkey hr

theorem nodup_indices {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M) (hr : r < M) :
    (indices μ offsets flat r).Nodup := by
  rw [indices_eq H hr]
  exact H.nodup_bucketList hkey hr

theorem bounds {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M) (hr : r < M) :
    start μ offsets r ≤ stop μ offsets r ∧ stop μ offsets r ≤ N := by
  rw [start_eq H (Nat.le_of_lt hr),stop_eq H hr]
  exact ⟨offset_mono key N (by omega),offset_le hkey (by omega)⟩

theorem read {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r t : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M)
    (hr : r < M) (ht : t < length μ offsets r) :
    ∃ i < N, key i = r ∧ μ (flat+start μ offsets r+t) = (i : ℤ) := by
  rw [length_eq H hr] at ht
  rw [start_eq H (Nat.le_of_lt hr)]
  obtain ⟨i,hi,hki,_,hread⟩ := H.read_bucket hkey hr ht
  exact ⟨i,hi,hki,hread⟩

end ThreeSum.SourceBucketView
