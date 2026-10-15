import Submission.ThreeSum.TernaryNearBankEnumeration
import Submission.ThreeSum.TernaryCodeSemantics
import Submission.ThreeSum.LightTernaryNearPair

/-! Canonical words in the exact pruned, physically emitted near-code order. -/
namespace ThreeSum.TernaryNearCanonical
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryCodeSemantics

set_option maxHeartbeats 2000000

def word {N : ℕ} (Q : TritWord N) (D j : ℕ) : TritWord N :=
  if hj : j<(TernaryNearEnumeration.words (wordList Q) D).length then
    fromList (TernaryNearEnumeration.words (wordList Q) D)[j]
      ((TernaryNearEnumeration.admitted_length
        ((TernaryNearEnumeration.mem_words _ _ _).mp (List.getElem_mem hj))).trans (wordList_length Q))
      (TernaryNearEnumeration.admitted_digits (wordList_digits Q)
        ((TernaryNearEnumeration.mem_words _ _ _).mp (List.getElem_mem hj)))
  else fun _ => 0

theorem wordList_word {N D j : ℕ} (Q : TritWord N)
    (hj : j<(TernaryNearEnumeration.words (wordList Q) D).length) :
    wordList (word Q D j)=(TernaryNearEnumeration.words (wordList Q) D)[j] := by
  unfold word
  rw [dif_pos hj]
  exact wordList_fromList _ _ _

theorem word_mem {N D j : ℕ} (Q : TritWord N)
    (hj : j<(TernaryNearEnumeration.words (wordList Q) D).length) :
    word Q D j∈nearWords Q D := by
  apply (TernaryNearBankEnumeration.wordList_admitted Q _).mp
  rw [wordList_word Q hj]
  exact (TernaryNearEnumeration.mem_words _ _ _).mp (List.getElem_mem hj)

theorem complete {N D : ℕ} (Q R : TritWord N) (hR : R∈nearWords Q D) :
    ∃ j<(TernaryNearEnumeration.codes (wordList Q) D).length, word Q D j=R := by
  have hm : wordList R∈TernaryNearEnumeration.words (wordList Q) D :=
    (TernaryNearEnumeration.mem_words _ _ _).mpr
      ((TernaryNearBankEnumeration.wordList_admitted Q R).mpr hR)
  obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hm
  refine ⟨j,by simpa only [TernaryNearEnumeration.codes_length] using hj,?_⟩
  exact wordList_injective N ((wordList_word Q hj).trans he)

theorem address_word {N D j : ℕ} (Q : TritWord N)
    (hj : j<(TernaryNearEnumeration.codes (wordList Q) D).length) :
    address (word Q D j)=(TernaryNearEnumeration.codes (wordList Q) D)[j] := by
  have hj' : j<(TernaryNearEnumeration.words (wordList Q) D).length := by
    simpa only [TernaryNearEnumeration.codes_length] using hj
  rw [address,wordList_word Q hj']
  simp only [TernaryNearEnumeration.codes_eq_map,List.getElem_map]

theorem sorted {N : ℕ} (Q : TritWord N) (D : ℕ) : ∀ j k, j<k →
    k<(TernaryNearEnumeration.codes (wordList Q) D).length →
    address (word Q D j)<address (word Q D k) := by
  intro j k hj hk
  rw [address_word Q (by omega),address_word Q hk]
  exact List.pairwise_iff_getElem.mp
    (TernaryNearEnumeration.codes_strictly_sorted _ _ (wordList_digits Q)) j k (by omega) hk hj

theorem read_of_seg {N D a : ℕ} (Q : TritWord N) (μ : ℕ → ℤ)
    (hseg : Light.Seg μ a ((TernaryNearEnumeration.codes (wordList Q) D).map (fun c => (c : ℤ)))) :
    ∀ j<(TernaryNearEnumeration.codes (wordList Q) D).length,
      μ (a+j)=(address (word Q D j) : ℤ) := by
  intro j hj
  have hs := hseg j (by simpa using hj)
  simpa [List.bind_eq_flatMap,←List.map_eq_flatMap,address_word Q hj] using hs

theorem outside_near_iff {N : ℕ} (Q R : TritWord N) (T : ℕ) (hQ : T<rank Q) :
    R∈nearWords Q (rank Q-(T+1)) ↔ Below R Q ∧ T<rank R := by
  rw [mem_nearWords]
  constructor
  · intro ⟨hbelow,hdef⟩
    have hsum := rank_add_deficit hbelow
    exact ⟨hbelow,by omega⟩
  · intro ⟨hbelow,hrank⟩
    have hsum := rank_add_deficit hbelow
    exact ⟨hbelow,by omega⟩

/-- With the exact cutoff, every emitted row lies outside the stored bank. -/
theorem outside_rows {N j T : ℕ} (Q : TritWord N) (hQ : T<rank Q)
    (hj : j<(TernaryNearEnumeration.codes (wordList Q) (rank Q-(T+1))).length) :
    Below (word Q (rank Q-(T+1)) j) Q ∧ T<rank (word Q (rank Q-(T+1)) j) := by
  apply (outside_near_iff Q _ T hQ).mp
  exact word_mem Q (by simpa only [TernaryNearEnumeration.codes_length] using hj)

/-- Every outside-bank descendant required by Euler or inversion is emitted. -/
theorem outside_complete {N T : ℕ} (Q R : TritWord N) (hQ : T<rank Q)
    (hRQ : Below R Q) (hR : T<rank R) :
    ∃ j<(TernaryNearEnumeration.codes (wordList Q) (rank Q-(T+1))).length,
      word Q (rank Q-(T+1)) j=R := by
  exact complete Q R ((outside_near_iff Q R T hQ).mpr ⟨hRQ,hR⟩)

end ThreeSum.TernaryNearCanonical
