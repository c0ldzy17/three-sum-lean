import Submission.ThreeSum.TernaryTupleDictionaryLookup
import Mathlib.Data.List.NodupEquivFin

noncomputable section
namespace ThreeSum.TernaryTupleDictionaryDecode
open LightTernarySourceHost

/-- This decoder uses the precise index in the actual product enumeration. -/
def decode {A : Type*} (base : List A) (r : ℕ) (j : Fin (base.length^r)) : List A :=
  (RadixKeyLists.tuples base r).get ⟨j.val,by simpa [RadixKeyLists.tuples_length] using j.isLt⟩

theorem decode_mem {A : Type*} (base : List A) (r : ℕ) (j : Fin (base.length^r)) :
    decode base r j∈RadixKeyLists.tuples base r := List.get_mem _ _

theorem decode_length {A : Type*} (base : List A) (r : ℕ) (j : Fin (base.length^r)) :
    (decode base r j).length=r := (RadixKeyLists.mem_tuples _ _ _).mp (decode_mem _ _ _) |>.1

theorem dictionary_decode {A : Type*} (base : List A) (r : ℕ) (j : Fin (base.length^r))
    (raw : A→ℤ) (p : ℕ) :
    dictionary (base.map raw) p r j.val=Radix.positionalHash (p : ℤ) raw (decode base r j) := by
  unfold dictionary
  rw [RadixKeyLists.values_eq_map]
  simp only [List.getD,List.getElem?_map]
  rw [List.getElem?_eq_getElem (show j.val<(RadixKeyLists.tuples base r).length by
    simpa only [RadixKeyLists.tuples_length] using j.isLt)]
  rfl

/-- Distinct source dictionary positions remain distinct after decoding,
including native hash collisions. -/
theorem decode_injective {A : Type*} (base : List A) (hn : base.Nodup) (r : ℕ) :
    Function.Injective (decode base r) := by
  intro i j he
  apply Fin.ext
  exact congrArg (fun t : Fin (RadixKeyLists.tuples base r).length => t.val)
    ((RadixKeyLists.tuples_nodup base hn r).injective_get he)

/-- Every retained tuple has one exact physical dictionary position. -/
def equiv {A : Type*} (base : List A) (hn : base.Nodup) (r : ℕ) :
    Fin (base.length^r) ≃ {xs // xs∈RadixKeyLists.tuples base r} := by
  classical
  exact (finCongr (RadixKeyLists.tuples_length base r).symm).trans
    ((RadixKeyLists.tuples_nodup base hn r).getEquiv _)

@[simp] theorem equiv_val {A : Type*} (base : List A) (hn : base.Nodup) (r : ℕ)
    (j : Fin (base.length^r)) : (equiv base hn r j).val=decode base r j := rfl

end ThreeSum.TernaryTupleDictionaryDecode
