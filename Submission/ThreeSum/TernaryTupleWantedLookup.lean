import Submission.ThreeSum.TernaryTupleDictionaryLookup

noncomputable section
namespace ThreeSum.TernaryTupleWantedLookup
open TernaryWantedLittleEndian
set_option maxHeartbeats 2000000

theorem encode_digits (digits : List ℕ) (R : ℕ) (is : List ℕ) (code scale : ℕ) :
    encode digits R code scale is=code+scale*Nat.ofDigits R (is.map (fun i => digits.getD i 0)) := by
  induction is generalizing code scale with
  | nil => simp [encode,Nat.ofDigits]
  | cons i is ih =>
    rw [encode,ih]
    simp only [List.map_cons,Nat.ofDigits]
    norm_cast
    ring

theorem indexed_tuple {A : Type*} (base : List A) (xs : List A)
    (hx : ∀ x∈xs, x∈base) :
    ∃ is : List ℕ, is.length=xs.length ∧ (∀ i∈is, i<base.length) ∧
      ∀ (B : Type*) (raw : A→B) (fallback : B),
        is.map (fun i => (base.map raw).getD i fallback)=xs.map raw := by
  induction xs with
  | nil => exact ⟨[],rfl,by simp,by intros; rfl⟩
  | cons x xs ih =>
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp (hx x (by simp))
    obtain ⟨is,hlen,hvalid,hmap⟩ := ih (fun y hy => hx y (by simp [hy]))
    refine ⟨i.val::is,by simpa using hlen,?_,?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl|hj
      · exact i.isLt
      · exact hvalid j hj
    · intro B raw fallback
      simp only [List.map_cons,hmap B raw fallback]
      congr 1
      simp only [List.getD,List.getElem?_map,List.getElem?_eq_getElem i.isLt,
        Option.map_some,Option.getD_some]
      simpa only [List.get_eq_getElem] using congrArg raw hi

/-- A retained output tuple is really traversed by the literal wanted DFS.
The returned word and bank IDs use exactly the aligned local array indices. -/
theorem wanted_lookup {A : Type*} (base xs : List A) (r : ℕ)
    (hx : xs∈RadixKeyLists.tuples base r) (p : ℕ) (hp : p≠0)
    (raw : A→ℤ) (word group : A→ℕ) (R F : ℕ) (x : ℤ)
    (hdiv : (p : ℤ)^r∣x-Radix.positionalHash (p : ℤ) raw xs) :
    (Nat.ofDigits R (xs.map word),Nat.ofDigits F (xs.map group))∈
      wantedCodes (p : ℤ) (base.map raw) (base.map word) (base.map group) r x R F 0 1 0 1 := by
  obtain ⟨hlen,hmem⟩ := (RadixKeyLists.mem_tuples _ _ _).mp hx
  obtain ⟨is,hi,hvalid,hmap⟩ := indexed_tuple base xs hmem
  apply (mem_wantedCodes (by exact_mod_cast hp) _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
  refine ⟨is,hi.trans hlen,?_,?_,?_,?_⟩
  · simpa only [List.length_map] using hvalid
  · have he : Radix.positionalHash (p : ℤ) (fun i => (base.map raw).getD i 0) is=
        Radix.positionalHash (p : ℤ) raw xs := by
      calc
        _ = Radix.positionalHash (p : ℤ) id (is.map (fun i => (base.map raw).getD i 0)) :=
          TernaryNativeTupleWitness.positional_map _ _ id _
        _ = Radix.positionalHash (p : ℤ) id (xs.map raw) := congrArg _ (hmap ℤ raw 0)
        _ = _ := (TernaryNativeTupleWitness.positional_map _ raw id _).symm
    simpa only [he] using hdiv
  · simp only [encode_digits,zero_add,one_mul]
    exact congrArg (Nat.ofDigits R) (hmap ℕ word 0)
  · simp only [encode_digits,zero_add,one_mul]
    exact congrArg (Nat.ofDigits F) (hmap ℕ group 0)

end ThreeSum.TernaryTupleWantedLookup
