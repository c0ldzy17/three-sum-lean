import Submission.ThreeSum.GlobalEncoding
import Submission.ThreeSum.MaskErase

/-!
# Evaluating a one-hot hash from a subset mask

The executable recursion examines exactly one bit per level using a cached
power of two.  Its result is the sum of the selected symbol coefficients,
and is connected here to the raw hashes used by the global encoding.
-/

namespace ThreeSum.OneHotMask

open Finset SubsetAddress LocalHashMoments
open scoped BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

def eval (w0 w1 : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | L+1, m =>
    if m < 2^L then eval w0 w1 L m + w0 L
    else eval w0 w1 L (m-2^L) + w1 L

theorem eval_le {L m U : ℕ} {w0 w1 : ℕ → ℕ}
    (h0 : ∀ i < L, w0 i ≤ U) (h1 : ∀ i < L, w1 i ≤ U) :
    eval w0 w1 L m ≤ L*U := by
  induction L generalizing m with
  | zero => simp [eval]
  | succ L ih =>
    have h0L := h0 L (by omega)
    have h1L := h1 L (by omega)
    have h0' : ∀ i < L, w0 i ≤ U := fun i hi => h0 i (by omega)
    have h1' : ∀ i < L, w1 i ≤ U := fun i hi => h1 i (by omega)
    unfold eval
    split
    · have hh := ih (m := m) h0' h1'
      nlinarith
    · have hh := ih (m := m-2^L) h0' h1'
      nlinarith

private theorem subset_range_pred {L : ℕ} {s : Finset ℕ}
    (hs : s ⊆ range (L+1)) (hL : L ∉ s) : s ⊆ range L := by
  intro i hi
  have h := mem_range.mp (hs hi)
  have hn : i ≠ L := by rintro rfl; exact hL hi
  exact mem_range.mpr (by omega)

theorem eval_maskOf {L : ℕ} (s : Finset ℕ) (hs : s ⊆ range L)
    (w0 w1 : ℕ → ℕ) :
    eval w0 w1 L (maskOf s) = ∑ i ∈ range L, if i ∈ s then w1 i else w0 i := by
  induction L generalizing s with
  | zero => simp [eval]
  | succ L ih =>
    by_cases hL : L ∈ s
    · have ht : s.erase L ⊆ range L :=
        subset_range_pred ((erase_subset L s).trans hs) (notMem_erase _ _)
      have he : 2^L + maskOf (s.erase L) = maskOf s :=
        add_sum_erase s (fun i => 2^i) hL
      have hlo : ¬maskOf s < 2^L := by omega
      have hsub : maskOf s-2^L = maskOf (s.erase L) := by omega
      rw [eval, if_neg hlo, hsub, ih (s.erase L) ht, sum_range_succ, if_pos hL]
      congr 1
      apply sum_congr rfl
      intro i hi
      have hiL : i ≠ L := by have := mem_range.mp hi; omega
      by_cases hiS : i ∈ s <;> simp [hiS, hiL]
    · have ht := subset_range_pred hs hL
      have hlo := (maskOf_isMask ht).1
      rw [eval, if_pos hlo, ih s ht, sum_range_succ, if_neg hL]

def extend {L : ℕ} (f : Fin L → ℕ) (i : ℕ) : ℕ :=
  if hi : i < L then f ⟨i,hi⟩ else 0

@[simp] theorem extend_fin {L : ℕ} (f : Fin L → ℕ) (i : Fin L) :
    extend f i.val = f i := by simp [extend, i.isLt]

@[simp] theorem mem_natPositions {L : ℕ} (s : Finset (Fin L)) (i : Fin L) :
    i.val ∈ natPositions s ↔ i ∈ s := by
  simp only [natPositions, mem_map]
  constructor
  · rintro ⟨a,ha,he⟩
    have hai : a = i := Fin.ext he
    simpa only [hai] using ha
  · intro hi
    exact ⟨i,hi,rfl⟩

theorem eval_subsetMask {L : ℕ} (s : Finset (Fin L)) (w0 w1 : Fin L → ℕ) :
    eval (extend w0) (extend w1) L (subsetMask s) =
      ∑ i : Fin L, if i ∈ s then w1 i else w0 i := by
  rw [subsetMask, eval_maskOf _ (natPositions_subset s), Finset.sum_range]
  apply sum_congr rfl
  intro i _
  simp only [extend_fin, mem_natPositions]

theorem eval_rawLeft {h L : ℕ}
    (w : Weight L (LocalField h)) (s : Finset (Fin L)) :
    (eval (extend fun i => (w (i,false)).val) (extend fun i => (w (i,true)).val)
      L (subsetMask s) : ℤ) = GlobalEncoding.rawHash w (LocalGraph.leftWord s) := by
  rw [eval_subsetMask]
  unfold GlobalEncoding.rawHash
  push_cast
  apply sum_congr rfl
  intro i _
  by_cases hi : i ∈ s <;> simp [LocalGraph.leftWord, hi]

theorem eval_rawRight {h L : ℕ}
    (w : Weight L (LocalField h)) (s : Finset (Fin L)) :
    (eval (extend fun i => (w (i,true)).val) (extend fun i => (w (i,false)).val)
      L (subsetMask s) : ℤ) = GlobalEncoding.rawHash w (LocalGraph.rightWord s) := by
  rw [eval_subsetMask]
  unfold GlobalEncoding.rawHash
  push_cast
  apply sum_congr rfl
  intro i _
  by_cases hi : i ∈ s <;> simp [LocalGraph.rightWord, hi]

end ThreeSum.OneHotMask
