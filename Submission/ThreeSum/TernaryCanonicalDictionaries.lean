import Submission.ThreeSum.TernaryFixedDictionaries
import Submission.ThreeSum.LightTernaryParallelDictionaries
import Submission.ThreeSum.TernaryWantedLittleEndian
import Submission.ThreeSum.TernaryBankEnumeration

noncomputable section
namespace ThreeSum.TernaryCanonicalDictionaries
open Finset Light RadixKeyLists TernaryFixedDictionaries TernaryJointType
variable {L p : ℕ} [Fact p.Prime] {α : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]

def records (right : Bool) (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) : List (SourceRecord L α I) :=
  if right then trimmedRightRecords maps B else trimmedLeftRecords maps B

theorem records_length_le (right : Bool)
    (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p) (B : ℕ) :
    (records (α := α) right maps B).length ≤ Fintype.card I*(TernaryCoverLocal.vertices L α).card := by
  classical
  cases right
  · simpa [records,trimmedLeftRecords] using
      (Finset.card_filter_le (Finset.univ : Finset (SourceRecord L α I)) (acceptedLeft maps B))
  · simpa [records,trimmedRightRecords] using
      (Finset.card_filter_le (Finset.univ : Finset (SourceRecord L α I)) (acceptedRight maps B))

def native (right : Bool) (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (r : SourceRecord L α I) : ℤ :=
  ((if right then rightNative maps r else leftNative maps r).val : ℕ)

def wordCode (r : SourceRecord L α I) : ℤ :=
  (TernaryAddresses.code (TernaryBankEnumeration.wordList r.2.val) : ℕ)

def mapCode (r : SourceRecord L α I) : ℤ := ((Fintype.equivFin I r.1).val : ℕ)

theorem native_bound (right : Bool) (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (r : SourceRecord L α I) : |native right maps r| ≤ (p : ℤ) := by
  unfold native
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (ZMod.val_lt (if right then rightNative maps r else leftNative maps r)).le

theorem wordCode_lt (r : SourceRecord L α I) : wordCode r < (4^L : ℕ) := by
  unfold wordCode
  exact_mod_cast (show TernaryAddresses.code (TernaryBankEnumeration.wordList r.2.val) < 4^L from by
    have hc := TernaryAddresses.code_lt (TernaryBankEnumeration.wordList r.2.val) (by
      intro d hd
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp hd
      exact hi ▸ (r.2.val i).isLt)
    simpa only [TernaryBankEnumeration.wordList_length] using hc)

theorem wordCode_bound (r : SourceRecord L α I) : |wordCode r| ≤ (4^L : ℕ) := by
  unfold wordCode at *
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact (wordCode_lt r).le

theorem mapCode_bound (r : SourceRecord L α I) : |mapCode r| ≤ (Fintype.card I : ℤ) := by
  unfold mapCode
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (Fintype.equivFin I r.1).isLt.le

variable {lim : Limits}

/-- Concrete canonical-field source initialization: native digit hash,
canonical word address and map occurrence code are generated from the
same trimmed local-record tuples in three independently stored arrays. -/
theorem program_meets (right : Bool)
    (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p) (B : ℕ)
    {base0 dst0 base1 dst1 base2 dst2 J d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hbase0 : base0+(records (α := α) right maps B).length ≤ dst0)
    (hnext0 : LightRadixKeys.space dst0 (records (α := α) right maps B).length J ≤ base1)
    (hbase1 : base1+(records (α := α) right maps B).length ≤ dst1)
    (hnext1 : LightRadixKeys.space dst1 (records (α := α) right maps B).length J ≤ base2)
    (hbase2 : base2+(records (α := α) right maps B).length ≤ dst2)
    (hspace2 : LightRadixKeys.space dst2 (records (α := α) right maps B).length J ≤ lim.space)
    (hm : 0 < (records (α := α) right maps B).length)
    (hw0 : (LightRadixKeys.word p p J : ℤ) ≤ lim.word)
    (hw1 : (LightRadixKeys.word (4^L) (4^L) J : ℤ) ≤ lim.word)
    (hw2 : (LightRadixKeys.word (Fintype.card I) (Fintype.card I) J : ℤ) ≤ lim.word)
    (hd : d+J+4 ≤ lim.depth) :
    let rs := records (α := α) right maps B
    Meets lim (LightTernaryParallelDictionaries.program
      (rs.map (native right maps)) (rs.map wordCode) (rs.map mapCode)) 15 d
      [base0,dst0,base1,dst1,base2,dst2,J,p,4^L,Fintype.card I] μ
      (LightTernaryParallelDictionaries.time
        (rs.map (native right maps)) (rs.map wordCode) (rs.map mapCode) J)
      (fun r ν => r=((dst2+LightRadixKeys.offset rs.length J : ℕ) : ℤ) ∧
        LightTernaryParallelDictionaries.recordOutput ν dst0 rs (native right maps) p J ∧
        LightTernaryParallelDictionaries.recordOutput ν dst1 rs wordCode (4^L) J ∧
        LightTernaryParallelDictionaries.recordOutput ν dst2 rs mapCode (Fintype.card I) J ∧
        Kept μ ν base0) := by
  apply LightTernaryParallelDictionaries.program_meets_records
    (records (α := α) right maps B) (native right maps) wordCode mapCode μ hw
    hbase0 hnext0 hbase1 hnext1 hbase2 hspace2 hm
    (fun r _ => native_bound right maps r) (fun r _ => wordCode_bound r)
    (fun r _ => mapCode_bound r) hw0 hw1 hw2 hd

end ThreeSum.TernaryCanonicalDictionaries
