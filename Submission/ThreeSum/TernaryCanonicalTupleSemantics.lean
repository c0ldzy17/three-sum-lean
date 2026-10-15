import Submission.ThreeSum.TernaryCanonicalDictionaries

noncomputable section
namespace ThreeSum.TernaryCanonicalTupleSemantics
open TernaryCanonicalDictionaries TernaryFixedDictionaries TernaryJointType
variable {L p : ℕ} [Fact p.Prime] {α : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Reverse the native block sequence while retaining every block's internal
trit order. This same permutation is used on both sources and wanted rows. -/
def canonicalWord (rs : List (SourceRecord L α I)) : List ℕ :=
  rs.reverse.flatMap (fun r => TernaryBankEnumeration.wordList r.2.val)

theorem canonicalWord_length (rs : List (SourceRecord L α I)) :
    (canonicalWord rs).length=rs.length*L := by
  unfold canonicalWord
  rw [RadixKeyLists.flatMap_length_uniform _ _ L (by simp),List.length_reverse]

theorem canonicalWord_digits (rs : List (SourceRecord L α I)) :
    ∀ d ∈ canonicalWord rs, d<3 := by
  intro d hd
  obtain ⟨r,hr,hd⟩ := List.mem_flatMap.mp hd
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hd
  exact hi ▸ (r.2.val i).isLt

/-- The actual parallel radix constructor's word field is precisely the
canonical ternary-bank address. No table-order advice is used. -/
theorem positional_wordCode (rs : List (SourceRecord L α I)) :
    Radix.positionalHash ((4^L : ℕ) : ℤ) wordCode rs=
      (TernaryAddresses.code (canonicalWord rs) : ℤ) := by
  induction rs with
  | nil => simp [Radix.positionalHash,canonicalWord,TernaryAddresses.code]
  | cons r rs ih =>
    rw [Radix.positionalHash,ih]
    change wordCode r+(4^L : ℕ)*(TernaryAddresses.code (canonicalWord rs) : ℤ)=_
    simp only [canonicalWord,List.reverse_cons,List.flatMap_append,List.flatMap_singleton,
      TernaryWantedCanonicalPairs.address_append,TernaryBankEnumeration.wordList_length]
    unfold wordCode
    push_cast
    ring

/-- Canonical radix digits never overflow into a neighboring native row. -/
theorem positional_bounds {A : Type*} (R : ℕ) (hR : 0<R) (raw : A → ℤ)
    (xs : List A) (hb : ∀ x ∈ xs, 0 ≤ raw x ∧ raw x < (R : ℤ)) :
    0 ≤ Radix.positionalHash (R : ℤ) raw xs ∧
      Radix.positionalHash (R : ℤ) raw xs < (R^xs.length : ℕ) := by
  induction xs with
  | nil => simp [Radix.positionalHash]
  | cons x xs ih =>
    have hx := hb x (by simp)
    have ht := ih (fun y hy => hb y (by simp [hy]))
    have hRz : (0 : ℤ)<R := by exact_mod_cast hR
    simp only [Radix.positionalHash,List.length_cons,pow_succ,Nat.cast_mul,Nat.cast_pow]
    push_cast at ht
    obtain ⟨ht0,ht1⟩ := ht
    constructor
    · exact add_nonneg hx.1 (mul_nonneg hRz.le ht0)
    · have htail : Radix.positionalHash (R : ℤ) raw xs+1 ≤ (R : ℤ)^xs.length := by omega
      have hdigit : raw x+1 ≤ (R : ℤ) := by omega
      nlinarith

theorem positional_native_bounds (right : Bool)
    (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (rs : List (SourceRecord L α I)) :
    0 ≤ Radix.positionalHash (p : ℤ) (native right maps) rs ∧
      Radix.positionalHash (p : ℤ) (native right maps) rs < (p^rs.length : ℕ) := by
  apply positional_bounds p (Fact.out : p.Prime).pos
  intro r hr
  unfold native
  exact ⟨Nat.cast_nonneg _,by exact_mod_cast ZMod.val_lt (if right then rightNative maps r else leftNative maps r)⟩

theorem positional_map_bounds (hI : 0<Fintype.card I) (rs : List (SourceRecord L α I)) :
    0 ≤ Radix.positionalHash (Fintype.card I : ℤ) mapCode rs ∧
      Radix.positionalHash (Fintype.card I : ℤ) mapCode rs < (Fintype.card I^rs.length : ℕ) := by
  apply positional_bounds (Fintype.card I) hI
  intro r hr
  unfold mapCode
  exact ⟨Nat.cast_nonneg _,by exact_mod_cast (Fintype.equivFin I r.1).isLt⟩

end ThreeSum.TernaryCanonicalTupleSemantics
