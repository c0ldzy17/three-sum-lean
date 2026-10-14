import Submission.ThreeSum.TernaryNearEnumeration
import Submission.ThreeSum.TernaryBankEnumeration
import Mathlib.Data.List.Forall2

/-! Exact query-neighborhood cardinality for the pruned computable enumerator. -/

namespace ThreeSum.TernaryNearBankEnumeration

open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration

theorem wordList_forall₂ {N : ℕ} (R Q : TritWord N) :
    List.Forall₂ (· ≤ ·) (wordList R) (wordList Q) ↔ Below R Q := by
  rw [List.forall₂_iff_get]
  constructor
  · rintro ⟨_,h⟩ i
    have hiR : i.val < (wordList R).length := by simp [i.isLt]
    have hiQ : i.val < (wordList Q).length := by simp [i.isLt]
    have hh := h i.val hiR hiQ
    simpa [wordList,List.get_eq_getElem] using hh
  · intro h
    refine ⟨by simp,?_⟩
    intro i hiR hiQ
    have hi : i < N := by simpa using hiR
    simpa [wordList,List.get_eq_getElem] using h ⟨i,hi⟩

theorem wordList_deficit {N : ℕ} (Q R : TritWord N) :
    (List.zipWith Nat.sub (wordList Q) (wordList R)).sum = deficit Q R := by
  have hzip : List.zipWith Nat.sub (wordList Q) (wordList R) =
      List.ofFn (fun i : Fin N => (Q i).val-(R i).val) := by
    apply List.ext_getElem
    · simp [wordList]
    · intro i hi hj
      simp [wordList,List.getElem_zipWith]
  rw [hzip]
  simp [deficit,List.sum_ofFn]

theorem wordList_admitted {N D : ℕ} (Q R : TritWord N) :
    TernaryNearEnumeration.Admitted (wordList Q) (wordList R) D ↔
      R ∈ nearWords Q D := by
  rw [TernaryNearEnumeration.admitted_iff,wordList_forall₂,wordList_deficit,mem_nearWords]

theorem words_image_nearWords {N : ℕ} (Q : TritWord N) (D : ℕ) :
    (TernaryNearEnumeration.words (wordList Q) D).toFinset =
      (nearWords Q D).image wordList := by
  ext rs
  constructor
  · intro hrs
    have hrs' := List.mem_toFinset.mp hrs
    have had := (TernaryNearEnumeration.mem_words _ _ _).mp hrs'
    have hlen : rs.length=N := (TernaryNearEnumeration.admitted_length had).trans (wordList_length Q)
    have hdigits := TernaryNearEnumeration.admitted_digits (wordList_digits Q) had
    let R := fromList rs hlen hdigits
    have hlist : wordList R=rs := wordList_fromList rs hlen hdigits
    refine Finset.mem_image.mpr ⟨R,?_,hlist⟩
    apply (wordList_admitted Q R).mp
    simpa only [hlist] using had
  · intro hrs
    obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hrs
    exact List.mem_toFinset.mpr ((TernaryNearEnumeration.mem_words _ _ _).mpr
      ((wordList_admitted Q R).mpr hR))

theorem codes_length_eq_nearWords_card {N : ℕ} (Q : TritWord N) (D : ℕ) :
    (TernaryNearEnumeration.codes (wordList Q) D).length = (nearWords Q D).card := by
  rw [TernaryNearEnumeration.codes_length,
    ← List.toFinset_card_of_nodup (TernaryNearEnumeration.words_nodup _ _ (wordList_digits Q)),
    words_image_nearWords]
  exact Finset.card_image_of_injective _ (wordList_injective N)

theorem visits_le_nearWords {N : ℕ} (Q : TritWord N) (D : ℕ) :
    TernaryNearEnumeration.visits (wordList Q) D ≤ (N+1)*(nearWords Q D).card := by
  have h := TernaryNearEnumeration.visits_le_codes (wordList Q) D
  simpa only [wordList_length,codes_length_eq_nearWords_card] using h

theorem codes_length_gibbs {N : ℕ} (Q : TritWord N) (D : ℕ) (z : ℝ)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (TernaryNearEnumeration.codes (wordList Q) D).length*z^D ≤
      ∏ i : Fin N, (if Q i=0 then 1 else if Q i=1 then 1+z else 1+z+z^2) := by
  rw [codes_length_eq_nearWords_card]
  exact nearWords_card_gibbs Q D z hz hz1

end ThreeSum.TernaryNearBankEnumeration
