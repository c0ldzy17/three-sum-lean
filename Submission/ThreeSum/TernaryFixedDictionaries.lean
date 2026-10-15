import Submission.ThreeSum.TernaryGlobalEncoding
import Submission.ThreeSum.LightFixedRadixDictionary

noncomputable section
namespace ThreeSum.TernaryFixedDictionaries
open Finset TernaryJointType TernaryCoverLocal TernaryGlobalEncoding RadixKeyLists Light
variable {L p : ℕ} [Fact p.Prime] {α π : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev SourceRecord (L : ℕ) (α : DigitType) (I : Type*) := I × {a // a ∈ vertices L α}

def leftKey (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (r : SourceRecord L α I) : ℤ := -rawSource (maps r.1) false r.2.val

def rightKey (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (r : SourceRecord L α I) : ℤ := rawSource (maps r.1) true r.2.val

def sourceRecords (L : ℕ) (α : DigitType) (I : Type*) [Fintype I] : List (SourceRecord L α I) := by
  classical
  exact (univ : Finset (SourceRecord L α I)).toList

def outputRecords (L : ℕ) (π : DigitType) (I : Type*) [Fintype I] : List (OutputBlock L π I) := by
  classical
  exact (univ : Finset (OutputBlock L π I)).toList

theorem sourceRecords_length (L : ℕ) (α : DigitType) :
    (sourceRecords L α I).length = Fintype.card I*(vertices L α).card := by
  classical
  simp [sourceRecords]

theorem outputRecords_length (L : ℕ) (π : DigitType) :
    (outputRecords L π I).length = Fintype.card I*(vertices L π).card := by
  classical
  simp [outputRecords]

theorem leftKey_abs_bound (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (r : SourceRecord L α I) : |leftKey maps r| ≤ ((2*L+1)*p : ℕ) := by
  unfold leftKey
  rw [abs_neg,abs_of_nonneg (rawSource_nonnegative _ _ _)]
  exact rawSource_upper _ _ _

theorem rightKey_abs_bound (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (r : SourceRecord L α I) : |rightKey maps r| ≤ ((2*L+1)*p : ℕ) := by
  unfold rightKey
  rw [abs_of_nonneg (rawSource_nonnegative _ _ _)]
  exact rawSource_upper _ _ _

theorem outputKey_abs_bound (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (r : OutputBlock L π I) : |blockKey maps r| ≤ ((2*L+2)*p : ℕ) :=
  rawOutput_abs_bound _ _

/-- Actual sourcekey membership retains occurrence IDs separately from integer labels. -/
theorem source_choice_keys {Ω : Type*} (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (occ : Ω → I) (edge : Ω → LocalEdge L α π) (c : Ω) :
    ∃ rL rR : SourceRecord L α I,
      rL ∈ sourceRecords L α I ∧ rR ∈ sourceRecords L α I ∧
      leftKey maps rL = rawLeft maps occ edge c ∧ rightKey maps rR = rawRight maps occ edge c := by
  classical
  refine ⟨(occ c,⟨left (edge c),left_mem_vertices _⟩),
    (occ c,⟨right (edge c),right_mem_vertices _⟩), ?_, ?_, rfl, rfl⟩ <;> simp [sourceRecords]


def leftNative (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (r : SourceRecord L α I) : ZMod p :=
  TernaryCoverHashes.linearHash (TernaryCoverHashes.leftVector (fieldWord p r.2.val)) (maps r.1)

def rightNative (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (r : SourceRecord L α I) : ZMod p :=
  TernaryCoverHashes.linearHash (TernaryCoverHashes.rightVector (fieldWord p r.2.val)) (maps r.1)

def acceptedLeft (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p) (B : ℕ)
    (r : SourceRecord L α I) : Prop :=
  TernaryCoverTrimming.bucketSize (fieldVertices L p α) TernaryCoverHashes.leftVector
    (maps r.1) (leftNative maps r) ≤ B

def acceptedRight (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p) (B : ℕ)
    (r : SourceRecord L α I) : Prop :=
  TernaryCoverTrimming.bucketSize (fieldVertices L p α) TernaryCoverHashes.rightVector
    (maps r.1) (rightNative maps r) ≤ B

def trimmedLeftRecords (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) : List (SourceRecord L α I) := by
  classical
  exact ((univ : Finset (SourceRecord L α I)).filter (acceptedLeft maps B)).toList

def trimmedRightRecords (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) : List (SourceRecord L α I) := by
  classical
  exact ((univ : Finset (SourceRecord L α I)).filter (acceptedRight maps B)).toList

theorem trimmed_records_of_retained {Ω : Type*}
    (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p) (B : ℕ)
    (occ : Ω → I) (edge : Ω → LocalEdge L α π) (c : Ω)
    (hleft : TernaryCoverTrimming.bucketSize (fieldVertices L p α) TernaryCoverHashes.leftVector
      (maps (occ c)) (leftHash (maps (occ c)) (edge c)) ≤ B)
    (hright : TernaryCoverTrimming.bucketSize (fieldVertices L p α) TernaryCoverHashes.rightVector
      (maps (occ c)) (rightHash (maps (occ c)) (edge c)) ≤ B) :
    ∃ rL rR : SourceRecord L α I,
      rL ∈ trimmedLeftRecords maps B ∧ rR ∈ trimmedRightRecords maps B ∧
      leftKey maps rL = rawLeft maps occ edge c ∧ rightKey maps rR = rawRight maps occ edge c := by
  classical
  refine ⟨(occ c,⟨left (edge c),left_mem_vertices _⟩),
    (occ c,⟨right (edge c),right_mem_vertices _⟩), ?_, ?_, rfl, rfl⟩
  · simpa [trimmedLeftRecords,acceptedLeft,leftNative,leftHash,fieldLeft] using hleft
  · simpa [trimmedRightRecords,acceptedRight,rightNative,rightHash,fieldRight] using hright


def leftNativeFiber (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p) (B : ℕ)
    (a : ZMod p) : Finset (SourceRecord L α I) := by
  classical
  exact univ.filter fun r => acceptedLeft maps B r ∧ leftNative maps r = a

theorem left_native_fiber_cap (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) (hp : 2 < p) (a : ZMod p) :
    (leftNativeFiber (α := α) maps B a).card ≤ Fintype.card I*B := by
  classical
  have hi (i : I) : ((leftNativeFiber (α := α) maps B a).filter fun r => r.1 = i).card ≤ B := by
    let F := (leftNativeFiber (α := α) maps B a).filter fun r => r.1 = i
    by_cases hz : F.card = 0
    · change F.card ≤ B
      rw [hz]
      exact Nat.zero_le B
    obtain ⟨r0,hr0⟩ := card_pos.mp (Nat.pos_of_ne_zero hz)
    obtain ⟨hr0,hi0⟩ := mem_filter.mp hr0
    have hdata := (mem_filter.mp hr0).2
    have hb : TernaryCoverTrimming.bucketSize (fieldVertices L p α)
        TernaryCoverHashes.leftVector (maps i) a ≤ B := by
      have h := hdata.1
      change TernaryCoverTrimming.bucketSize (fieldVertices L p α)
        TernaryCoverHashes.leftVector (maps r0.1) (leftNative maps r0) ≤ B at h
      simpa [hi0,hdata.2] using h
    have hc : F.card ≤ TernaryCoverTrimming.bucketSize (fieldVertices L p α)
        TernaryCoverHashes.leftVector (maps i) a := by
      unfold TernaryCoverTrimming.bucketSize
      apply card_le_card_of_injOn (fun r : SourceRecord L α I => fieldWord p r.2.val)
      · intro r hr
        obtain ⟨hr,hri⟩ := mem_filter.mp hr
        have hn := (mem_filter.mp hr).2.2
        apply mem_filter.mpr
        refine ⟨?_,?_⟩
        · exact mem_image.mpr ⟨r.2.val,r.2.property,rfl⟩
        · simpa [leftNative,hri] using hn
      · intro r hr t ht h
        apply Prod.ext
        · exact (mem_filter.mp hr).2.trans (mem_filter.mp ht).2.symm
        · apply Subtype.ext
          exact fieldWord_injective hp h
    exact hc.trans hb
  calc
    _ = ∑ i : I, ((leftNativeFiber (α := α) maps B a).filter fun r => r.1 = i).card :=
      card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
    _ ≤ ∑ _i : I, B := sum_le_sum (fun i _ => hi i)
    _ = _ := by simp

variable {lim : Limits}

theorem left_dictionary_meets (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    {base dst J d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hbase : base+(sourceRecords L α I).length ≤ dst)
    (hm : 0 < (sourceRecords L α I).length)
    (hspace : LightRadixKeys.space dst (sourceRecords L α I).length J ≤ lim.space)
    (hword : (LightRadixKeys.word p ((2*L+1)*p) J : ℤ) ≤ lim.word)
    (hd : d+J+3 ≤ lim.depth) :
    Meets lim (LightFixedRadixDictionary.program ((sourceRecords L α I).map (leftKey maps)))
      4 d [base,dst,J,p] μ (LightFixedRadixDictionary.time ((sourceRecords L α I).map (leftKey maps)) J)
      (fun r ν => r=((dst+LightRadixKeys.offset (sourceRecords L α I).length J : ℕ) : ℤ) ∧
        ν (dst+LightRadixKeys.offset (sourceRecords L α I).length J)=
          (((sourceRecords L α I).length^J : ℕ) : ℤ) ∧
        Seg ν (dst+LightRadixKeys.offset (sourceRecords L α I).length J+1)
          ((tuples (sourceRecords L α I) J).map (Radix.positionalHash (p : ℤ) (leftKey maps))) ∧
        Kept μ ν base) :=
  LightFixedRadixDictionary.program_meets_records (sourceRecords L α I) (leftKey maps) μ hw hbase hm
    (fun r _ => leftKey_abs_bound maps r) hspace hword hd


theorem right_dictionary_meets (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    {base dst J d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hbase : base+(sourceRecords L α I).length ≤ dst)
    (hm : 0 < (sourceRecords L α I).length)
    (hspace : LightRadixKeys.space dst (sourceRecords L α I).length J ≤ lim.space)
    (hword : (LightRadixKeys.word p ((2*L+1)*p) J : ℤ) ≤ lim.word)
    (hd : d+J+3 ≤ lim.depth) :
    Meets lim (LightFixedRadixDictionary.program ((sourceRecords L α I).map (rightKey maps)))
      4 d [base,dst,J,p] μ (LightFixedRadixDictionary.time ((sourceRecords L α I).map (rightKey maps)) J)
      (fun r ν => r=((dst+LightRadixKeys.offset (sourceRecords L α I).length J : ℕ) : ℤ) ∧
        ν (dst+LightRadixKeys.offset (sourceRecords L α I).length J)=
          (((sourceRecords L α I).length^J : ℕ) : ℤ) ∧
        Seg ν (dst+LightRadixKeys.offset (sourceRecords L α I).length J+1)
          ((tuples (sourceRecords L α I) J).map (Radix.positionalHash (p : ℤ) (rightKey maps))) ∧
        Kept μ ν base) :=
  LightFixedRadixDictionary.program_meets_records (sourceRecords L α I) (rightKey maps) μ hw hbase hm
    (fun r _ => rightKey_abs_bound maps r) hspace hword hd


theorem output_dictionary_meets (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    {base dst J d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hbase : base+(outputRecords L π I).length ≤ dst)
    (hm : 0 < (outputRecords L π I).length)
    (hspace : LightRadixKeys.space dst (outputRecords L π I).length J ≤ lim.space)
    (hword : (LightRadixKeys.word p ((2*L+2)*p) J : ℤ) ≤ lim.word)
    (hd : d+J+3 ≤ lim.depth) :
    Meets lim (LightFixedRadixDictionary.program ((outputRecords L π I).map (blockKey maps)))
      4 d [base,dst,J,p] μ (LightFixedRadixDictionary.time ((outputRecords L π I).map (blockKey maps)) J)
      (fun r ν => r=((dst+LightRadixKeys.offset (outputRecords L π I).length J : ℕ) : ℤ) ∧
        ν (dst+LightRadixKeys.offset (outputRecords L π I).length J)=
          (((outputRecords L π I).length^J : ℕ) : ℤ) ∧
        Seg ν (dst+LightRadixKeys.offset (outputRecords L π I).length J+1)
          ((tuples (outputRecords L π I) J).map (Radix.positionalHash (p : ℤ) (blockKey maps))) ∧
        Kept μ ν base) :=
  LightFixedRadixDictionary.program_meets_records (outputRecords L π I) (blockKey maps) μ hw hbase hm
    (fun r _ => outputKey_abs_bound maps r) hspace hword hd


theorem trimmed_left_dictionary_meets (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) {base dst J d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hbase : base+(trimmedLeftRecords (α := α) maps B).length ≤ dst)
    (hm : 0 < (trimmedLeftRecords (α := α) maps B).length)
    (hspace : LightRadixKeys.space dst (trimmedLeftRecords (α := α) maps B).length J ≤ lim.space)
    (hword : (LightRadixKeys.word p ((2*L+1)*p) J : ℤ) ≤ lim.word)
    (hd : d+J+3 ≤ lim.depth) :
    Meets lim (LightFixedRadixDictionary.program ((trimmedLeftRecords (α := α) maps B).map (leftKey maps)))
      4 d [base,dst,J,p] μ (LightFixedRadixDictionary.time ((trimmedLeftRecords (α := α) maps B).map (leftKey maps)) J)
      (fun r ν => r=((dst+LightRadixKeys.offset (trimmedLeftRecords (α := α) maps B).length J : ℕ) : ℤ) ∧
        ν (dst+LightRadixKeys.offset (trimmedLeftRecords (α := α) maps B).length J)=
          (((trimmedLeftRecords (α := α) maps B).length^J : ℕ) : ℤ) ∧
        Seg ν (dst+LightRadixKeys.offset (trimmedLeftRecords (α := α) maps B).length J+1)
          ((tuples (trimmedLeftRecords (α := α) maps B) J).map (Radix.positionalHash (p : ℤ) (leftKey maps))) ∧
        Kept μ ν base) :=
  LightFixedRadixDictionary.program_meets_records (trimmedLeftRecords (α := α) maps B) (leftKey maps) μ hw hbase hm
    (fun r _ => leftKey_abs_bound maps r) hspace hword hd

theorem trimmed_right_dictionary_meets (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) {base dst J d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hbase : base+(trimmedRightRecords (α := α) maps B).length ≤ dst)
    (hm : 0 < (trimmedRightRecords (α := α) maps B).length)
    (hspace : LightRadixKeys.space dst (trimmedRightRecords (α := α) maps B).length J ≤ lim.space)
    (hword : (LightRadixKeys.word p ((2*L+1)*p) J : ℤ) ≤ lim.word)
    (hd : d+J+3 ≤ lim.depth) :
    Meets lim (LightFixedRadixDictionary.program ((trimmedRightRecords (α := α) maps B).map (rightKey maps)))
      4 d [base,dst,J,p] μ (LightFixedRadixDictionary.time ((trimmedRightRecords (α := α) maps B).map (rightKey maps)) J)
      (fun r ν => r=((dst+LightRadixKeys.offset (trimmedRightRecords (α := α) maps B).length J : ℕ) : ℤ) ∧
        ν (dst+LightRadixKeys.offset (trimmedRightRecords (α := α) maps B).length J)=
          (((trimmedRightRecords (α := α) maps B).length^J : ℕ) : ℤ) ∧
        Seg ν (dst+LightRadixKeys.offset (trimmedRightRecords (α := α) maps B).length J+1)
          ((tuples (trimmedRightRecords (α := α) maps B) J).map (Radix.positionalHash (p : ℤ) (rightKey maps))) ∧
        Kept μ ν base) :=
  LightFixedRadixDictionary.program_meets_records (trimmedRightRecords (α := α) maps B) (rightKey maps) μ hw hbase hm
    (fun r _ => rightKey_abs_bound maps r) hspace hword hd
end ThreeSum.TernaryFixedDictionaries
