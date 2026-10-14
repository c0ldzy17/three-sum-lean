import Submission.ThreeSum.TernaryConvolution

/-!
# Original record multiplicities in the ternary query

Histograms retain their original record indices, even when several records
have the same word.  The convolution equals the literal number of indexed
record pairs, rather than the number of distinct word values.
-/

namespace ThreeSum.TernaryPhysicalSources

open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryConvolution

theorem rank_eq_type_sum {N : ℕ} (R : TritWord N) :
    rank R = ∑ d : Fin 3, d.val*digitCount R d := by
  unfold rank digitCount
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hs : ∀ r : Fin 3, r.val = ∑ d : Fin 3,
      d.val*(if r=d then 1 else 0 : ℕ) := by
    intro r
    fin_cases r <;> decide
  exact hs (R i)

theorem rank_of_type {N : ℕ} {R : TritWord N} {α : DigitType}
    (h : HasType R α) : rank R=α 1+2*α 2 := by
  change ∀ d, digitCount R d = α d at h
  rw [rank_eq_type_sum]
  simp only [h]
  simp [Fin.sum_univ_succ]

variable {ι κ : Type*}

noncomputable def histogram {N : ℕ} (S : Finset ι) (word : ι → TritWord N)
    (A : TritWord N) : ℤ :=
  ∑ i ∈ S, if word i=A then 1 else 0

theorem histogram_nonneg {N : ℕ} (S : Finset ι) (word : ι → TritWord N) (A : TritWord N) :
    0 ≤ histogram S word A := by
  apply Finset.sum_nonneg
  intro i hi
  split <;> norm_num

theorem histogram_pos_iff {N : ℕ} (S : Finset ι) (word : ι → TritWord N) (A : TritWord N) :
    0 < histogram S word A ↔ ∃ i ∈ S, word i=A := by
  unfold histogram
  rw [Finset.sum_pos_iff_of_nonneg (by intro i hi; split <;> norm_num)]
  constructor
  · rintro ⟨i,hi,hpos⟩
    have he : word i=A := by
      by_contra hn
      simp only [if_neg hn] at hpos
      omega
    exact ⟨i,hi,he⟩
  · rintro ⟨i,hi,he⟩
    exact ⟨i,hi,by simp only [if_pos he]; norm_num⟩

theorem histogram_homogeneous {N h : ℕ} (S : Finset ι) (word : ι → TritWord N)
    (hrank : ∀ i ∈ S, rank (word i)=h) :
    ∀ A, histogram S word A≠0 → rank A=h := by
  intro A hA
  have hp : 0 < histogram S word A := lt_of_le_of_ne (histogram_nonneg S word A) (Ne.symm hA)
  obtain ⟨i,hi,he⟩ := (histogram_pos_iff S word A).mp hp
  simpa only [he] using hrank i hi

theorem histogram_type_homogeneous {N : ℕ} (S : Finset ι)
    (word : ι → TritWord N) (α : DigitType)
    (htype : ∀ i ∈ S, HasType (word i) α) :
    ∀ A, histogram S word A≠0 → rank A=α 1+2*α 2 :=
  histogram_homogeneous S word (fun i hi => rank_of_type (htype i hi))

theorem histogram_sum {N : ℕ} (S : Finset ι) (word : ι → TritWord N)
    (F : TritWord N → ℤ) :
    (∑ A, histogram S word A*F A) = ∑ i ∈ S, F (word i) := by
  classical
  unfold histogram
  simp only [Finset.sum_mul,ite_mul,one_mul,zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp

noncomputable def pairCount {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι → TritWord N) (right : κ → TritWord N) (Q : TritWord N) : ℤ :=
  ∑ i ∈ S, ∑ j ∈ T, if Adds (left i) (right j) Q then 1 else 0

theorem convolution_histograms {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι → TritWord N) (right : κ → TritWord N) (Q : TritWord N) :
    convolution (histogram S left) (histogram T right) Q=pairCount S T left right Q := by
  classical
  have hcon : convolution (histogram S left) (histogram T right) Q =
      ∑ A, histogram S left A *
        (∑ B, histogram T right B*(if Adds A B Q then 1 else 0)) := by
    unfold convolution
    apply Finset.sum_congr rfl
    intro A hA
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B hB
    split <;> simp_all
  rw [hcon]
  simp_rw [histogram_sum]
  rfl

theorem pairCount_pos_iff {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι → TritWord N) (right : κ → TritWord N) (Q : TritWord N) :
    0 < pairCount S T left right Q ↔
      ∃ i ∈ S, ∃ j ∈ T, Adds (left i) (right j) Q := by
  unfold pairCount
  rw [Finset.sum_pos_iff_of_nonneg (by
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    split <;> norm_num)]
  constructor
  · rintro ⟨i,hi,hpos⟩
    rw [Finset.sum_pos_iff_of_nonneg (by intro j hj; split <;> norm_num)] at hpos
    obtain ⟨j,hj,hp⟩ := hpos
    have ha : Adds (left i) (right j) Q := by
      by_contra hn
      simp only [if_neg hn] at hp
      omega
    exact ⟨i,hi,j,hj,ha⟩
  · rintro ⟨i,hi,j,hj,ha⟩
    refine ⟨i,hi,?_⟩
    rw [Finset.sum_pos_iff_of_nonneg (by intro j hj; split <;> norm_num)]
    exact ⟨j,hj,by simp only [if_pos ha]; norm_num⟩

end ThreeSum.TernaryPhysicalSources
