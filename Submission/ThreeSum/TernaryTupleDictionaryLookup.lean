import Submission.ThreeSum.TernaryNativeTupleWitness
import Submission.ThreeSum.TernarySourceExecutionFactory

noncomputable section
namespace ThreeSum.TernaryTupleDictionaryLookup
open LightTernarySourceHost
set_option maxHeartbeats 2000000

theorem tuple_lookup {A : Type*} (base : List A) (r : ℕ) (xs : List A)
    (hx : xs∈RadixKeyLists.tuples base r) :
    ∃ j : ℕ, j<base.length^r ∧ ∀ (raw : A→ℤ) (p : ℕ),
      dictionary (base.map raw) p r j=Radix.positionalHash (p : ℤ) raw xs := by
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hx
  refine ⟨j.val,?_,?_⟩
  · simpa only [RadixKeyLists.tuples_length] using j.isLt
  · intro raw p
    unfold dictionary
    rw [RadixKeyLists.values_eq_map]
    simp only [List.getD,List.getElem?_map]
    have hget : (RadixKeyLists.tuples base r)[j.val]?=some xs := by
      rw [List.getElem?_eq_getElem j.isLt]
      simpa only [List.get_eq_getElem] using congrArg some hj
    rw [hget]
    rfl

/-- All three independently generated dictionaries use the same actual tuple
index, including collisions of the native integer keys. -/
theorem triple_lookup {A : Type*} (base : List A) (r : ℕ) (xs : List A)
    (hx : xs∈RadixKeyLists.tuples base r) (raw word group : A→ℤ) (p R F : ℕ) :
    ∃ j : ℕ, j<base.length^r ∧
      dictionary (base.map raw) p r j=Radix.positionalHash (p : ℤ) raw xs ∧
      dictionary (base.map word) R r j=Radix.positionalHash (R : ℤ) word xs ∧
      dictionary (base.map group) F r j=Radix.positionalHash (F : ℤ) group xs := by
  obtain ⟨j,hj,h⟩ := tuple_lookup base r xs hx
  exact ⟨j,hj,h raw p,h word R,h group F⟩

end ThreeSum.TernaryTupleDictionaryLookup
