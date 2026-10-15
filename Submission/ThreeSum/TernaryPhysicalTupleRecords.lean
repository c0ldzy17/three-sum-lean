import Submission.ThreeSum.TernaryTupleDictionaryDecode

noncomputable section
namespace ThreeSum.TernaryPhysicalTupleRecords
open TernaryTupleDictionaryDecode LightTernarySourceHost
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {A : Type*}

/-- Literal source join records, expressed by their original position and
retained local-record tuple. The modulus is the actual prefix modulus. -/
def Record (base : List A) (r M n : ℕ) (input : ℕ→ℤ) (raw : A→ℤ) :=
  {x : Fin n×{xs // xs∈RadixKeyLists.tuples base r} //
    (M : ℤ)∣input x.1.val-Radix.positionalHash (M : ℤ) raw x.2.val}

/-- Decoding is defined on every actual physical source record. -/
def decodeRecord (base : List A) (r M n p : ℕ) (input : ℕ→ℤ) (raw : A→ℤ)
    (x : TernarySourceHostModel.records M n (base.length^r) input
      (dictionary (base.map raw) p r)) :
    Fin n×{xs // xs∈RadixKeyLists.tuples base r} :=
  (⟨x.val.1,((TernarySourceHostModel.mem_records _ _ _ _ _ _).mp x.property).1⟩,
    ⟨decode base r ⟨x.val.2,((TernarySourceHostModel.mem_records _ _ _ _ _ _).mp x.property).2.1⟩,
      decode_mem _ _ _⟩)

theorem decodeRecord_injective (base : List A) (hn : base.Nodup)
    (r M n p : ℕ) (input : ℕ→ℤ) (raw : A→ℤ) :
    Function.Injective (decodeRecord base r M n p input raw) := by
  intro x y he
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z : Fin n×{xs // xs∈RadixKeyLists.tuples base r} => z.1.val) he
  · have hh := congrArg (fun z : Fin n×{xs // xs∈RadixKeyLists.tuples base r} => z.2.val) he
    exact congrArg Fin.val (decode_injective base hn r hh)

theorem decoded_congruence (base : List A) (r M n p : ℕ) (input : ℕ→ℤ) (raw : A→ℤ)
    (x : TernarySourceHostModel.records M n (base.length^r) input
      (dictionary (base.map raw) p r)) :
    (M : ℤ)∣input x.val.1-Radix.positionalHash (p : ℤ) raw
      (decodeRecord base r M n p input raw x).2.val := by
  have hx := ((TernarySourceHostModel.mem_records _ _ _ _ _ _).mp x.property).2.2
  rw [dictionary_decode base r ⟨x.val.2,
    ((TernarySourceHostModel.mem_records _ _ _ _ _ _).mp x.property).2.1⟩ raw p] at hx
  exact hx

/-- Three separately allocated fields decode to the same physical tuple. -/
theorem decoded_fields (base : List A) (r M n p R F : ℕ) (input : ℕ→ℤ)
    (raw word group : A→ℤ)
    (x : TernarySourceHostModel.records M n (base.length^r) input
      (dictionary (base.map raw) p r)) :
    dictionary (base.map word) R r x.val.2=
      Radix.positionalHash (R : ℤ) word (decodeRecord base r M n p input raw x).2.val ∧
    dictionary (base.map group) F r x.val.2=
      Radix.positionalHash (F : ℤ) group (decodeRecord base r M n p input raw x).2.val := by
  let j : Fin (base.length^r) := ⟨x.val.2,
    ((TernarySourceHostModel.mem_records _ _ _ _ _ _).mp x.property).2.1⟩
  exact ⟨dictionary_decode base r j word R,dictionary_decode base r j group F⟩

end ThreeSum.TernaryPhysicalTupleRecords
