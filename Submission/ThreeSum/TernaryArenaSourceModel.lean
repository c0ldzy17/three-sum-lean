import Submission.ThreeSum.TernaryArenaSourceSetup
import Submission.ThreeSum.TernaryCanonicalSourceBank

noncomputable section
namespace ThreeSum.TernaryArenaSourceModel
open TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps TernaryArenaSourceSetup
open TernaryCanonicalDictionaries TernaryNativeCompleteFrontend
attribute [local instance] Classical.propDecidable
variable {p m F r : ℕ} [Fact p.Prime]

abbrev Index (maps : Fin F→Weight m p) (cap : ℕ) (right : Bool) :=
  Fin ((localRecords maps cap right).length^r)

theorem word_spec (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (j : Index (r := r) maps cap right) :
    (TernaryBankCanonical.enumeration (N m r) (cut m r)).word
      ((source (r := r) maps cap I right).key j.val)=
      TernaryCanonicalSourceBank.word right maps cap j := by
  change (TernaryBankCanonical.enumeration (N m r) (cut m r)).word
    ((bankCodes m r).idxOf (LightTernarySourceHost.dictionary
      ((localRecords maps cap right).map wordCode) (4^fixedLength m) r j.val).toNat)=_
  simp only [localRecords] at *
  rw [TernaryCanonicalSourceBank.dictionary_word right maps cap j]
  simp only [Int.toNat_natCast]
  apply TernaryCanonicalSourceBank.enumeration_word
  · intro k hk
    change TernaryCodeSemantics.address (TernaryBankCanonical.word _ _ k)=_
    rw [TernaryBankCanonical.address_word hk,List.getD_eq_getElem _ _ hk]
  · exact TernaryCanonicalSourceBank.rank_le right maps cap j

theorem group_spec (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (j : Index (r := r) maps cap right) :
    (source (r := r) maps cap I right).group j.val=
      TernaryNativeBlockPairs.occurrenceCode
        (fun i => (TernaryCanonicalSourceBank.block right maps cap j i).1) := by
  change (LightTernarySourceHost.dictionary ((localRecords maps cap right).map mapCode) F r j.val).toNat=_
  simp only [localRecords] at *
  rw [TernaryCanonicalSourceBank.dictionary_group right maps cap j,Int.toNat_natCast]

theorem key_lt (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (j : Index (r := r) maps cap right) :
    (source (r := r) maps cap I right).key j.val<(source (r := r) maps cap I right).bank :=
  (TernaryCanonicalSourceBank.source_index_spec right maps cap j).1

theorem word_code (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (j : Index (r := r) maps cap right) :
    LightTernarySourceHost.dictionary (source (r := r) maps cap I right).ys
      (source (r := r) maps cap I right).p1 r j.val=
      ((source (r := r) maps cap I right).codes ((source (r := r) maps cap I right).key j.val) : ℤ) := by
  change LightTernarySourceHost.dictionary ((localRecords maps cap right).map wordCode)
    (4^fixedLength m) r j.val=(((bankCodes m r).getD _ 0 : ℕ) : ℤ)
  change LightTernarySourceHost.dictionary ((TernaryCanonicalDictionaries.records (α := fixedAlpha m) right maps cap).map wordCode)
    (4^fixedLength m) r j.val=(((TernaryAddresses.codes (r*fixedLength m) (cut m r)).getD
      ((TernaryAddresses.codes (r*fixedLength m) (cut m r)).idxOf
        (LightTernarySourceHost.dictionary ((TernaryCanonicalDictionaries.records (α := fixedAlpha m) right maps cap).map wordCode)
          (4^fixedLength m) r j.val).toNat) 0 : ℕ) : ℤ)
  simp only [cut]
  rw [(TernaryCanonicalSourceBank.source_index_spec right maps cap j).2,
    TernaryCanonicalSourceBank.dictionary_word right maps cap j]
  rfl

theorem original_rows (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (original : ℕ→Fin r→ZMod p)
    (hin : ∀ i<(source (r := r) maps cap I right).NL,
      (source (r := r) maps cap I right).input i=(TernaryExtensionEncoding.coefficientCode (original i) : ℤ))
    (x : ℕ×ℕ) (hx : x∈(source (r := r) maps cap I right).records) :
    ∃ j : Index (r := r) maps cap right, j.val=x.2 ∧
      original x.1=TernaryCanonicalSourceBank.nativeRow right maps cap j := by
  have hv := (TernarySourceHostModel.mem_records _ _ _ _ _ _).mp hx
  let j : Index (r := r) maps cap right := ⟨x.2,by simpa [source,LightTernarySourceHost.size] using hv.2.1⟩
  refine ⟨j,rfl,?_⟩
  apply TernaryCanonicalSourceBank.source_rows
  have hh := hv.2.2
  rw [hin x.1 hv.1] at hh
  exact hh

end ThreeSum.TernaryArenaSourceModel
