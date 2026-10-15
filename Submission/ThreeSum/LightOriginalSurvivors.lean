import Submission.ThreeSum.LightOriginalCollisionCleanup

/-! Exact compact indexing of original singleton-bucket survivors. -/
noncomputable section
namespace ThreeSum.LightOriginalSurvivors
open LightOriginalBucketFilter LightOriginalCollisionCleanup
attribute [local instance] Classical.propDecidable

def indices (keys : ℕ → ℕ) (n : ℕ) : List ℕ := good keys (counts keys n) n

def index (keys : ℕ → ℕ) (n j : ℕ) : ℕ :=
  if hj : j < (indices keys n).length then (indices keys n)[j] else 0

theorem partition_lengths (keys count : ℕ → ℕ) (n : ℕ) :
    (good keys count n).length + (bad keys count n).length = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [good_succ,bad_succ]
    by_cases h : count (keys n) = 1 <;> simp [h] <;> omega

theorem length_le (keys : ℕ → ℕ) (n : ℕ) : (indices keys n).length ≤ n :=
  (lengths keys (counts keys n) n).1

theorem index_mem {keys : ℕ → ℕ} {n j : ℕ} (hj : j < (indices keys n).length) :
    index keys n j ∈ indices keys n := by
  simpa only [index,dif_pos hj] using List.getElem_mem hj

theorem index_lt {keys : ℕ → ℕ} {n j : ℕ} (hj : j < (indices keys n).length) :
    index keys n j < n := List.mem_range.mp (List.mem_filter.mp (index_mem hj)).1

theorem mem_iff (keys : ℕ → ℕ) (n i : ℕ) :
    i ∈ indices keys n ↔ ∃ j < (indices keys n).length, index keys n j = i := by
  constructor
  · intro hi
    obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hi
    exact ⟨j,hj,by simpa only [index,dif_pos hj] using he⟩
  · rintro ⟨j,hj,rfl⟩
    exact index_mem hj

theorem index_strict {keys : ℕ → ℕ} {n i j : ℕ}
    (hi : i < j) (hj : j < (indices keys n).length) : index keys n i < index keys n j := by
  have hs : (indices keys n).Pairwise (· < ·) := List.pairwise_lt_range.filter _
  have hh := (List.pairwise_iff_getElem.mp hs) i j (by omega) hj hi
  simpa only [index,dif_pos hj,dif_pos (show i < (indices keys n).length by omega)] using hh

theorem keys_injective {keys : ℕ → ℕ} {n i j : ℕ}
    (hi : i < (indices keys n).length) (hj : j < (indices keys n).length)
    (he : keys (index keys n i) = keys (index keys n j)) : i = j := by
  have hh := surviving_keys_injective (index_mem hi) (index_mem hj) he
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact (Nat.ne_of_lt (index_strict h hj)) hh
  · exact (Nat.ne_of_lt (index_strict h hi)) hh.symm

theorem sorted {keys : ℕ → ℕ} {n : ℕ} (values : ℕ → ℤ)
    (hs : ∀ i j, i < j → j < n → values i < values j) :
    ∀ i j, i < j → j < (indices keys n).length →
      values (index keys n i) < values (index keys n j) := by
  intro i j hij hj
  exact hs _ _ (index_strict hij hj) (index_lt hj)

theorem colored_decomposition (A B C : ℕ → ℤ) (keysB keysC : ℕ → ℕ) (nA nB nC : ℕ) :
    (∃ i < nA, ∃ j < nB, ∃ k < nC, C k = A i + B j) ↔
      LightDeletedTwoSum.Hit (badIndex keysB nB) B A C nC nA (badIndices keysB nB).length 1 ∨
      LightDeletedTwoSum.Hit (badIndex keysC nC) C A B nB nA (badIndices keysC nC).length (-1) ∨
      ∃ i < nA, ∃ j < (indices keysB nB).length, ∃ k < (indices keysC nC).length,
        C (index keysC nC k) = A i + B (index keysB nB j) := by
  rw [LightOriginalCollisionCleanup.colored_decomposition]
  constructor
  · rintro (h | h | ⟨i,hi,j,hj,k,hk,he⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · obtain ⟨jj,hjj,rfl⟩ := (mem_iff keysB nB j).mp hj
      obtain ⟨kk,hkk,rfl⟩ := (mem_iff keysC nC k).mp hk
      exact Or.inr (Or.inr ⟨i,hi,jj,hjj,kk,hkk,he⟩)
  · rintro (h | h | ⟨i,hi,j,hj,k,hk,he⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨i,hi,_,index_mem hj,_,index_mem hk,he⟩)

end ThreeSum.LightOriginalSurvivors
