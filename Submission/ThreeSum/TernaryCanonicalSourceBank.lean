import Submission.ThreeSum.TernaryCanonicalTupleCodes
import Submission.ThreeSum.TernaryNativeBlockPairs
import Submission.ThreeSum.TernaryTupleDictionaryDecode
import Submission.ThreeSum.TernaryDimensionBounds
import Submission.ThreeSum.LightTernaryPrefixSetup

noncomputable section
namespace ThreeSum.TernaryCanonicalSourceBank
open TernaryJointType TernaryCanonicalDictionaries TernaryRepeatedWords
open TernaryTupleDictionaryDecode TernaryCodeSemantics TernaryAddresses
open TernaryCoverLocal TernaryFixedDictionaries TernaryLocalParameters
attribute [local instance] Classical.propDecidable
variable {p m F r : ℕ} [Fact p.Prime]

def block (right : Bool) (maps : Fin F→TernaryCoverHashes.Coordinate (Fin (fixedLength m))→ZMod p)
    (B : ℕ) (j : Fin ((records (α := fixedAlpha m) right maps B).length^r)) :
    Fin r→SourceRecord (fixedLength m) (fixedAlpha m) (Fin F) := fun i =>
  (decode (records (α := fixedAlpha m) right maps B) r j)[i.val]'(by rw [decode_length]; exact i.isLt)

theorem ofFn_block (right : Bool)
    (maps : Fin F→TernaryCoverHashes.Coordinate (Fin (fixedLength m))→ZMod p)
    (B : ℕ) (j : Fin ((records (α := fixedAlpha m) right maps B).length^r)) :
    List.ofFn (block right maps B j)=decode (records (α := fixedAlpha m) right maps B) r j := by
  apply List.ext_getElem (by simp [decode_length])
  intro i hi hj
  simp only [List.getElem_ofFn,block]

def word (right : Bool) (maps : Fin F→TernaryCoverHashes.Coordinate (Fin (fixedLength m))→ZMod p)
    (B : ℕ) (j : Fin ((records (α := fixedAlpha m) right maps B).length^r)) :
    TritWord (r*fixedLength m) := canonical (fun i => (block right maps B j i).2.val)

theorem dictionary_word (right : Bool)
    (maps : Fin F→TernaryCoverHashes.Coordinate (Fin (fixedLength m))→ZMod p)
    (B : ℕ) (j : Fin ((records (α := fixedAlpha m) right maps B).length^r)) :
    LightTernarySourceHost.dictionary ((records (α := fixedAlpha m) right maps B).map wordCode) (4^fixedLength m) r j.val=
      (address (word right maps B j) : ℤ) := by
  rw [dictionary_decode,←ofFn_block]
  exact TernaryCanonicalTupleCodes.canonical_code (fun x : SourceRecord (fixedLength m) (fixedAlpha m) (Fin F) => x.2.val) _

theorem typed (right : Bool)
    (maps : Fin F→TernaryCoverHashes.Coordinate (Fin (fixedLength m))→ZMod p)
    (B : ℕ) (j : Fin ((records (α := fixedAlpha m) right maps B).length^r)) :
    HasType (word right maps B j) (fun d => r*fixedAlpha m d) := by
  apply canonical_typed
  intro i
  exact (Finset.mem_filter.mp (block right maps B j i).2.property).2

theorem rank_le (right : Bool)
    (maps : Fin F→TernaryCoverHashes.Coordinate (Fin (fixedLength m))→ZMod p)
    (B : ℕ) (j : Fin ((records (α := fixedAlpha m) right maps B).length^r)) :
    TernaryBank.rank (word right maps B j)≤LightTernaryPrefixSetup.T m r := by
  rw [TernaryDimensionBounds.rank_eq_counts,(typed right maps B j) 1,(typed right maps B j) 2]
  simp [fixedAlpha,LightTernaryPrefixSetup.T]
  ring_nf
  omega

theorem address_mem {N T : ℕ} (w : TritWord N) (hw : TernaryBank.rank w≤T) :
    address w∈codes N T := by
  rw [codes_eq_map]
  exact List.mem_map.mpr ⟨TernaryBankEnumeration.wordList w,
    (TernaryBankEnumeration.wordList_mem_words w).mpr (TernaryBank.mem_bank.mpr hw),rfl⟩

theorem index_spec {N T : ℕ} (w : TritWord N) (hw : TernaryBank.rank w≤T) :
    (codes N T).idxOf (address w)<(codes N T).length ∧
      (codes N T).getD ((codes N T).idxOf (address w)) 0=address w := by
  have hm := address_mem w hw
  refine ⟨List.idxOf_lt_length_iff.mpr hm,?_⟩
  simp [List.getD_eq_getElem _ _ (List.idxOf_lt_length_iff.mpr hm),hm]

theorem source_index_spec (right : Bool)
    (maps : Fin F→TernaryCoverHashes.Coordinate (Fin (fixedLength m))→ZMod p)
    (B : ℕ) (j : Fin ((records (α := fixedAlpha m) right maps B).length^r)) :
    let code := (LightTernarySourceHost.dictionary ((records (α := fixedAlpha m) right maps B).map wordCode)
      (4^fixedLength m) r j.val).toNat
    (codes (r*fixedLength m) (LightTernaryPrefixSetup.T m r)).idxOf code<
      (codes (r*fixedLength m) (LightTernaryPrefixSetup.T m r)).length ∧
      (codes (r*fixedLength m) (LightTernaryPrefixSetup.T m r)).getD
        ((codes (r*fixedLength m) (LightTernaryPrefixSetup.T m r)).idxOf code) 0=code := by
  rw [dictionary_word]
  simp only [Int.toNat_natCast]
  exact index_spec _ (rank_le right maps B j)


theorem enumeration_word {N T : ℕ} (Eword : ℕ→TritWord N)
    (hE : ∀ k<(codes N T).length, address (Eword k)=(codes N T).getD k 0)
    (w : TritWord N) (hw : TernaryBank.rank w≤T) :
    Eword ((codes N T).idxOf (address w))=w := by
  apply address_injective N
  rw [hE _ (index_spec w hw).1,(index_spec w hw).2]


def nativeRow (right : Bool)
    (maps : Fin F→TernaryCoverHashes.Coordinate (Fin (fixedLength m))→ZMod p)
    (B : ℕ) (j : Fin ((records (α := fixedAlpha m) right maps B).length^r)) : Fin r→ZMod p :=
  fun i => if right then rightNative maps (block right maps B j i)
    else leftNative maps (block right maps B j i)

theorem dictionary_native (right : Bool)
    (maps : Fin F→TernaryCoverHashes.Coordinate (Fin (fixedLength m))→ZMod p)
    (B : ℕ) (j : Fin ((records (α := fixedAlpha m) right maps B).length^r)) :
    LightTernarySourceHost.dictionary ((records (α := fixedAlpha m) right maps B).map (native right maps)) p r j.val=
      (TernaryExtensionEncoding.coefficientCode (nativeRow right maps B j) : ℤ) := by
  rw [dictionary_decode,←ofFn_block]
  apply TernaryNativeTupleWitness.positional_ofFn
  intro i
  rfl

theorem dictionary_group (right : Bool)
    (maps : Fin F→TernaryCoverHashes.Coordinate (Fin (fixedLength m))→ZMod p)
    (B : ℕ) (j : Fin ((records (α := fixedAlpha m) right maps B).length^r)) :
    LightTernarySourceHost.dictionary ((records (α := fixedAlpha m) right maps B).map mapCode) F r j.val=
      (TernaryNativeBlockPairs.occurrenceCode (fun i => (block right maps B j i).1) : ℤ) := by
  rw [dictionary_decode,←ofFn_block]
  unfold mapCode
  rw [TernaryCanonicalTupleCodes.digit_cast]
  simp only [List.map_ofFn,TernaryNativeBlockPairs.occurrenceCode]
  rfl

/-- The actual residue join forces every selected ORIGINAL hash row. -/
theorem source_rows (right : Bool)
    (maps : Fin F→TernaryCoverHashes.Coordinate (Fin (fixedLength m))→ZMod p)
    (B : ℕ) (j : Fin ((records (α := fixedAlpha m) right maps B).length^r))
    (original : Fin r→ZMod p)
    (hjoin : ((p^r : ℕ) : ℤ)∣(TernaryExtensionEncoding.coefficientCode original : ℤ)-
      LightTernarySourceHost.dictionary ((records (α := fixedAlpha m) right maps B).map (native right maps)) p r j.val) :
    original=nativeRow right maps B j := by
  rw [dictionary_native] at hjoin
  have he := Int.natCast_modEq_iff.mp (Int.modEq_iff_dvd.mpr hjoin)
  change TernaryExtensionEncoding.coefficientCode (nativeRow right maps B j)%(p^r)=
    TernaryExtensionEncoding.coefficientCode original%(p^r) at he
  rw [Nat.mod_eq_of_lt (TernaryExtensionEncoding.coefficientCode_lt _),
    Nat.mod_eq_of_lt (TernaryExtensionEncoding.coefficientCode_lt _)] at he
  exact (TernaryExtensionEncoding.coefficientCode_injective r he).symm


theorem block_mem (right : Bool)
    (maps : Fin F→TernaryCoverHashes.Coordinate (Fin (fixedLength m))→ZMod p)
    (B : ℕ) (j : Fin ((records (α := fixedAlpha m) right maps B).length^r)) (i : Fin r) :
    block right maps B j i∈records (α := fixedAlpha m) right maps B := by
  exact ((RadixKeyLists.mem_tuples _ _ _).mp (decode_mem _ _ j)).2 _ (List.getElem_mem _)

theorem records_nodup (right : Bool)
    (maps : Fin F→TernaryCoverHashes.Coordinate (Fin (fixedLength m))→ZMod p) (B : ℕ) :
    (records (α := fixedAlpha m) right maps B).Nodup := by
  cases right <;> simp only [records,Bool.false_eq_true,↓reduceIte,TernaryFixedDictionaries.trimmedLeftRecords,
    TernaryFixedDictionaries.trimmedRightRecords] <;> exact Finset.nodup_toList _

theorem block_injective (right : Bool)
    (maps : Fin F→TernaryCoverHashes.Coordinate (Fin (fixedLength m))→ZMod p) (B : ℕ) :
    Function.Injective (block (r := r) right maps B) := by
  intro i j he
  apply decode_injective _ (records_nodup right maps B) r
  rw [←ofFn_block right maps B i,←ofFn_block right maps B j,he]


def encodeBlock (right : Bool)
    (maps : Fin F→TernaryCoverHashes.Coordinate (Fin (fixedLength m))→ZMod p) (B : ℕ)
    (xs : Fin r→TernaryFixedDictionaries.SourceRecord (fixedLength m) (fixedAlpha m) (Fin F))
    (hx : ∀ i, xs i∈records (α := fixedAlpha m) right maps B) :
    Fin ((records (α := fixedAlpha m) right maps B).length^r) :=
  (TernaryTupleDictionaryDecode.equiv _ (records_nodup right maps B) r).symm
    ⟨List.ofFn xs,(RadixKeyLists.mem_tuples _ _ _).mpr ⟨by simp,by
      intro x hh
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hh
      exact hx i⟩⟩

theorem block_encodeBlock (right : Bool)
    (maps : Fin F→TernaryCoverHashes.Coordinate (Fin (fixedLength m))→ZMod p) (B : ℕ)
    (xs : Fin r→TernaryFixedDictionaries.SourceRecord (fixedLength m) (fixedAlpha m) (Fin F))
    (hx : ∀ i, xs i∈records (α := fixedAlpha m) right maps B) :
    block right maps B (encodeBlock right maps B xs hx)=xs := by
  apply List.ofFn_inj.mp
  rw [ofFn_block]
  have hh := congrArg Subtype.val
    ((TernaryTupleDictionaryDecode.equiv _ (records_nodup right maps B) r).apply_symm_apply
      (⟨List.ofFn xs,(RadixKeyLists.mem_tuples _ _ _).mpr ⟨by simp,by
        intro x hh
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hh
        exact hx i⟩⟩))
  exact hh

end ThreeSum.TernaryCanonicalSourceBank
