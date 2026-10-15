import Submission.ThreeSum.TernaryBankStageModel
import Submission.ThreeSum.TernaryBankEnumeration

/-! The exact computably enumerated compact bank supplies the complete sorted
physical enumeration used by the assembler; no separate enumeration is assumed. -/
namespace ThreeSum.TernaryBankCanonical
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEnumeration
open ThreeSum.TernaryAddresses ThreeSum.TernaryBankEnumeration ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000

def word (N T j : ℕ) : TritWord N :=
  if hj : j<(words N T).length then
    fromList (words N T)[j] ((mem_words N T _).mp (List.getElem_mem hj)).1
      ((mem_words N T _).mp (List.getElem_mem hj)).2.1
  else fun _ => 0

theorem wordList_word {N T j : ℕ} (hj : j<(words N T).length) :
    wordList (word N T j)=(words N T)[j] := by
  unfold word
  rw [dif_pos hj]
  exact wordList_fromList _ _ _

theorem word_rank {N T j : ℕ} (hj : j<(words N T).length) : rank (word N T j)≤T := by
  have hr := ((mem_words N T _).mp (List.getElem_mem hj)).2.2
  rwa [← wordList_word hj,wordList_sum] at hr

def enumeration (N T : ℕ) : Enumeration N T (codes N T).length where
  word := word N T
  mem := fun j hj => word_rank (by simpa only [codes_length] using hj)
  complete := by
    intro R hR
    have hm : wordList R∈words N T := (wordList_mem_words R).mpr (mem_bank.mpr hR)
    obtain ⟨j,hj,heq⟩ := List.mem_iff_getElem.mp hm
    refine ⟨j,by simpa only [codes_length] using hj,?_⟩
    exact wordList_injective N ((wordList_word hj).trans heq)

theorem address_word {N T j : ℕ} (hj : j<(codes N T).length) :
    address (word N T j)=(codes N T)[j] := by
  have hj' : j<(words N T).length := by simpa only [codes_length] using hj
  rw [address,wordList_word hj']
  simp only [codes_eq_map,List.getElem_map]

theorem sorted (N T : ℕ) : ∀ j k, j<k → k<(codes N T).length →
    address ((enumeration N T).word j)<address ((enumeration N T).word k) := by
  intro j k hj hk
  change address (word N T j)<address (word N T k)
  rw [address_word (by omega),address_word hk]
  exact List.pairwise_iff_getElem.mp (codes_strictly_sorted N T) j k (by omega) hk hj

/-- The actual enumerator's segment is exactly the assembler's physical code
premise, in the same order. -/
theorem read_of_seg {N T a : ℕ} (μ : ℕ→ℤ)
    (hseg : Light.Seg μ a ((codes N T).map (fun c => (c : ℤ)))) :
    ∀ j<(codes N T).length, μ (a+j)=(address ((enumeration N T).word j) : ℤ) := by
  intro j hj
  have hs := hseg j (by simpa using hj)
  simpa [List.bind_eq_flatMap,← List.map_eq_flatMap,enumeration,address_word hj] using hs

end ThreeSum.TernaryBankCanonical
