import Submission.ThreeSum.SourceBandLayout

/-! # Exact finite original-position sources for real and padded bands -/

namespace ThreeSum.SourceBandPartition

open BandPartition SourceBandLayout

def source (n g i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun t => start g i ≤ t.val ∧ t.val < stop n g i)

theorem mem_source {n g i : ℕ} {t : Fin n} :
    t ∈ source n g i ↔ start g i ≤ t.val ∧ t.val < stop n g i := by
  simp only [source,Finset.mem_filter,Finset.mem_univ,true_and]

theorem physical_lt {n g i j : ℕ} (hj : j < len n g i) : start g i+j < n := by
  have hs := stop_le n g i
  unfold len at hj
  omega

def equiv (n g i : ℕ) : Fin (len n g i) ≃ source n g i where
  toFun j := ⟨⟨start g i+j.val,physical_lt j.isLt⟩,mem_source.mpr
    ⟨by change start g i ≤ start g i+j.val; omega,
      by change start g i+j.val < stop n g i
         have hj := j.isLt
         unfold len at hj
         omega⟩⟩
  invFun t := ⟨t.val.val-start g i,by
    obtain ⟨hlo,hhi⟩ := mem_source.mp t.property
    unfold len
    omega⟩
  left_inv j := by
    apply Fin.ext
    simp only
    omega
  right_inv t := by
    apply Subtype.ext
    apply Fin.ext
    obtain ⟨hlo,hhi⟩ := mem_source.mp t.property
    simp only
    omega

theorem equiv_value {n g i : ℕ} (f : ℕ → ℤ) (j : Fin (len n g i)) :
    f (start g i+j.val) = f ((equiv n g i j).val.val) := rfl

theorem source_card (n g i : ℕ) : (source n g i).card=len n g i := by
  simpa only [Fintype.card_fin,Fintype.card_coe] using (Fintype.card_congr (equiv n g i)).symm

theorem len_eq_zero {n g i : ℕ} (hg : 0 < g) (hi : size n g ≤ i) : len n g i=0 := by
  by_cases hn : n=0
  · simp [len,stop,hn]
  · have hdiv : (n-1)/g < i := by
      simpa only [size,if_neg hn,Nat.add_one_le_iff] using hi
    have hmul : n-1 < i*g := (Nat.div_lt_iff_lt_mul hg).mp hdiv
    have hs := stop_le n g i
    unfold len start
    omega

theorem source_eq_empty {n g i : ℕ} (hg : 0 < g) (hi : size n g ≤ i) : source n g i=∅ := by
  apply Finset.card_eq_zero.mp
  rw [source_card,len_eq_zero hg hi]

theorem source_self {n g : ℕ} (hg : 0 < g) (t : Fin n) : t ∈ source n g (t.val/g) :=
  mem_source.mpr (index_bounds hg t.isLt)

theorem source_unique {n g i j : ℕ} {t : Fin n}
    (hi : t ∈ source n g i) (hj : t ∈ source n g j) : i=j := by
  obtain ⟨hil,hih⟩ := mem_source.mp hi
  obtain ⟨hjl,hjh⟩ := mem_source.mp hj
  have his : stop n g i ≤ (i+1)*g := min_le_right _ _
  have hjs : stop n g j ≤ (j+1)*g := min_le_right _ _
  rcases lt_trichotomy i j with h | h | h
  · have hp := Nat.mul_le_mul_right g (show i+1 ≤ j by omega)
    unfold start at *
    omega
  · exact h
  · have hp := Nat.mul_le_mul_right g (show j+1 ≤ i by omega)
    unfold start at *
    omega

end ThreeSum.SourceBandPartition
