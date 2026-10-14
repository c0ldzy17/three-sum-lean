import Submission.ThreeSum.TernaryAddresses
import Submission.ThreeSum.TernaryBank

/-!
# Exact connection between the computable enumerator and the rank bank
-/

namespace ThreeSum.TernaryBankEnumeration

open ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.TernaryJointType ThreeSum.TernaryBank

def wordList {N : ℕ} (w : TritWord N) : List ℕ := List.ofFn (fun i => (w i).val)

@[simp] theorem wordList_length {N : ℕ} (w : TritWord N) : (wordList w).length = N := by
  simp [wordList]

@[simp] theorem wordList_sum {N : ℕ} (w : TritWord N) : (wordList w).sum = rank w := by
  simp [wordList, rank, List.sum_ofFn]

theorem wordList_digits {N : ℕ} (w : TritWord N) : ∀ d ∈ wordList w, d < 3 := by
  intro d hd
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
  exact (w i).isLt

theorem wordList_injective (N : ℕ) : Function.Injective (@wordList N) := by
  intro w v h
  funext i
  apply Fin.ext
  have hh := congrArg (fun l : List ℕ => l[i.val]?) h
  simpa [wordList, i.isLt] using hh

theorem wordList_mem_words {N T : ℕ} (w : TritWord N) :
    wordList w ∈ words N T ↔ w ∈ bank N T := by
  rw [mem_words, mem_bank]
  simp only [wordList_length, wordList_sum, true_and]
  exact and_iff_right (wordList_digits w)

def fromList {N : ℕ} (xs : List ℕ) (hlen : xs.length = N)
    (hdigits : ∀ d ∈ xs, d < 3) : TritWord N := fun i =>
  ⟨xs[i.val]'(by omega), hdigits _ (List.getElem_mem (by omega))⟩

theorem wordList_fromList {N : ℕ} (xs : List ℕ) (hlen : xs.length = N)
    (hdigits : ∀ d ∈ xs, d < 3) : wordList (fromList xs hlen hdigits) = xs := by
  apply List.ext_getElem
  · simp [wordList, hlen]
  · intro i hi hj
    simp only [wordList, List.getElem_ofFn, fromList]

theorem words_image_bank (N T : ℕ) :
    (words N T).toFinset = (bank N T).image wordList := by
  ext xs
  constructor
  · intro hx
    have hx' := List.mem_toFinset.mp hx
    obtain ⟨hlen, hdigits, hsum⟩ := (mem_words N T xs).mp hx'
    let w := fromList xs hlen hdigits
    have hlist : wordList w = xs := wordList_fromList xs hlen hdigits
    apply Finset.mem_image.mpr
    refine ⟨w, ?_, hlist⟩
    apply (wordList_mem_words w).mp
    simpa only [hlist] using hx'
  · intro hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
    exact List.mem_toFinset.mpr ((wordList_mem_words w).mpr hw)

theorem words_nodup (N T : ℕ) : (words N T).Nodup := by
  have hc := codes_nodup N T
  rw [codes_eq_map] at hc
  exact List.Nodup.of_map code hc

theorem codes_length_eq_bank_card (N T : ℕ) :
    (codes N T).length = (bank N T).card := by
  rw [codes_length, ← List.toFinset_card_of_nodup (words_nodup N T), words_image_bank]
  exact Finset.card_image_of_injective _ (wordList_injective N)

theorem codes_length_gibbs (N T : ℕ) (y : ℝ) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    (codes N T).length * y ^ T ≤ (1 + y + y ^ 2) ^ N := by
  rw [codes_length_eq_bank_card]
  exact bank_card_gibbs N T y hy hy1

end ThreeSum.TernaryBankEnumeration
