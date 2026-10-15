import Submission.ThreeSum.TernaryAddressDecode
import Submission.ThreeSum.TernaryGoodOutputCatalog
import Submission.ThreeSum.TernaryWantedBatchProvenance
import Submission.ThreeSum.TernaryCanonicalTupleCodes
import Submission.ThreeSum.TernaryDimensionBounds
import Submission.ThreeSum.TernaryArenaSourceSetup

/-! Exact type and bank metadata of every query emitted by the actual wanted batch. -/
noncomputable section
namespace ThreeSum.TernaryArenaQueryModel
open TernaryJointType TernaryLocalParameters TernaryCoverLocal TernaryCoverHashes TernaryCoverGoodMaps
open TernaryWantedBatchIndex TernaryWantedBatchProvenance TernaryRepeatedWords
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
set_option maxRecDepth 18000
variable {m p F r : ℕ} [Fact p.Prime]

def queries (maps : Fin F → Weight m p) (τ : ℕ) (targets : ℕ → ℤ) (positions : ℕ → ℕ) (n : ℕ) :=
  entries p (4^fixedLength m) F r (TernaryGoodOutputCatalog.raws maps τ)
    (TernaryGoodOutputCatalog.wordCodes maps τ) (TernaryGoodOutputCatalog.mapCodes maps τ) targets positions n

def descriptor (maps : Fin F → Weight m p) (τ : ℕ) (targets : ℕ → ℤ) (positions : ℕ → ℕ) (n : ℕ)
    (j : Fin (queries (r := r) maps τ targets positions n).length) : Descriptor :=
  decode p (4^fixedLength m) F r (TernaryGoodOutputCatalog.raws maps τ)
    (TernaryGoodOutputCatalog.wordCodes maps τ) (TernaryGoodOutputCatalog.mapCodes maps τ) targets positions n j

theorem descriptor_spec (maps : Fin F → Weight m p) (τ : ℕ) (targets : ℕ → ℤ)
    (positions : ℕ → ℕ) (n : ℕ) (j : Fin (queries (r := r) maps τ targets positions n).length) :
    (descriptor maps τ targets positions n j).1 < n ∧
    (descriptor maps τ targets positions n j).2.length = r ∧
    ∀ k ∈ (descriptor maps τ targets positions n j).2,
      k < (TernaryGoodOutputCatalog.records maps τ).length := by
  have hd := (mem_descriptors p r (TernaryGoodOutputCatalog.raws maps τ) targets n _).mp
    (decode_mem p (4^fixedLength m) F r (TernaryGoodOutputCatalog.raws maps τ)
      (TernaryGoodOutputCatalog.wordCodes maps τ) (TernaryGoodOutputCatalog.mapCodes maps τ) targets positions n j)
  have ho := (TernaryWantedRadix.mem_wantedOutputs (p : ℤ)
    (by exact_mod_cast (Fact.out : p.Prime).ne_zero) (TernaryGoodOutputCatalog.raws maps τ)
    r (targets _) _).mp hd.2
  exact ⟨hd.1,ho.1,by simpa only [descriptor,TernaryGoodOutputCatalog.raws_length] using ho.2.1⟩

def block (maps : Fin F → Weight m p) (τ : ℕ) (targets : ℕ → ℤ) (positions : ℕ → ℕ) (n : ℕ)
    (j : Fin (queries (r := r) maps τ targets positions n).length) (i : Fin r) :
    TernaryGoodOutputCatalog.Record m (Fin F) :=
  (TernaryGoodOutputCatalog.records maps τ)[(descriptor maps τ targets positions n j).2[i.val]'(by
    rw [(descriptor_spec maps τ targets positions n j).2.1]; exact i.isLt)]'(by
      apply (descriptor_spec maps τ targets positions n j).2.2
      exact List.getElem_mem _)

def word (maps : Fin F → Weight m p) (τ : ℕ) (targets : ℕ → ℤ) (positions : ℕ → ℕ) (n : ℕ)
    (j : Fin (queries (r := r) maps τ targets positions n).length) : TritWord (r*fixedLength m) :=
  canonical (fun i => (block maps τ targets positions n j i).2.val)

theorem typed (maps : Fin F → Weight m p) (τ : ℕ) (targets : ℕ → ℤ)
    (positions : ℕ → ℕ) (n : ℕ) (j : Fin (queries (r := r) maps τ targets positions n).length) :
    HasType (word maps τ targets positions n j) (fun d => r*fixedPi m d) := by
  apply canonical_typed
  intro i
  exact (Finset.mem_filter.mp (block maps τ targets positions n j i).2.property).2

theorem block_map (maps : Fin F → Weight m p) (τ : ℕ) (targets : ℕ → ℤ)
    (positions : ℕ → ℕ) (n : ℕ) (j : Fin (queries (r := r) maps τ targets positions n).length)
    {A : Type*} (f : TernaryGoodOutputCatalog.Record m (Fin F) → A) (fallback : A) :
    (List.ofFn (block maps τ targets positions n j)).map f =
      (descriptor maps τ targets positions n j).2.map
        (fun k => ((TernaryGoodOutputCatalog.records maps τ).map f).getD k fallback) := by
  have hd := descriptor_spec maps τ targets positions n j
  apply List.ext_getElem (by simp [hd.2.1])
  intro i hi hi'
  have hiR : i < r := by simpa using hi
  have hiD : i < (descriptor maps τ targets positions n j).2.length := by omega
  have hk := hd.2.2 _ (List.getElem_mem hiD)
  simp only [List.getElem_map,List.getElem_ofFn,block]
  rw [List.getD_eq_getElem _ _ (by simpa using hk),List.getElem_map]

 theorem word_code (maps : Fin F → Weight m p) (τ : ℕ) (targets : ℕ → ℤ)
    (positions : ℕ → ℕ) (n : ℕ) (j : Fin (queries (r := r) maps τ targets positions n).length) :
    (get (queries (r := r) maps τ targets positions n) j.val).2.1 =
      TernaryCodeSemantics.address (word maps τ targets positions n j) := by
  have he := emit_decode p (4^fixedLength m) F r (TernaryGoodOutputCatalog.raws maps τ)
    (TernaryGoodOutputCatalog.wordCodes maps τ) (TernaryGoodOutputCatalog.mapCodes maps τ) targets positions n j
  have hw := congrArg (fun e : Entry => e.2.1) he
  change TernaryWantedLittleEndian.encode (TernaryGoodOutputCatalog.wordCodes maps τ)
    (4^fixedLength m) 0 1 (descriptor maps τ targets positions n j).2 = _ at hw
  rw [TernaryTupleWantedLookup.encode_digits,zero_add,one_mul] at hw
  change Nat.ofDigits (4^fixedLength m)
    ((descriptor maps τ targets positions n j).2.map
      (fun i => (TernaryGoodOutputCatalog.wordCodes maps τ).getD i 0)) =
      (get (queries (r := r) maps τ targets positions n) j.val).2.1 at hw
  rw [←hw]
  apply Int.ofNat_inj.mp
  have hc := TernaryCanonicalTupleCodes.canonical_code
    (fun e : TernaryGoodOutputCatalog.Record m (Fin F) => e.2.val)
    (block maps τ targets positions n j)
  rw [TernaryCanonicalTupleCodes.digit_cast] at hc
  rw [block_map maps τ targets positions n j _ 0] at hc
  exact hc

theorem decoded_word (maps : Fin F → Weight m p) (τ : ℕ) (targets : ℕ → ℤ)
    (positions : ℕ → ℕ) (n : ℕ) (j : Fin (queries (r := r) maps τ targets positions n).length) :
    TernaryAddressDecode.word (r*fixedLength m) (get (queries (r := r) maps τ targets positions n) j.val).2.1 =
      word maps τ targets positions n j := by
  rw [word_code,TernaryAddressDecode.word_address]

theorem group_code (maps : Fin F → Weight m p) (τ : ℕ) (targets : ℕ → ℤ)
    (positions : ℕ → ℕ) (n : ℕ) (j : Fin (queries (r := r) maps τ targets positions n).length) :
    (get (queries (r := r) maps τ targets positions n) j.val).2.2 =
      Nat.ofDigits F (List.ofFn fun i : Fin r =>
        (Fintype.equivFin (Fin F) (block maps τ targets positions n j i).1).val) := by
  have he := emit_decode p (4^fixedLength m) F r (TernaryGoodOutputCatalog.raws maps τ)
    (TernaryGoodOutputCatalog.wordCodes maps τ) (TernaryGoodOutputCatalog.mapCodes maps τ) targets positions n j
  have hg := congrArg (fun e : Entry => e.2.2) he
  change TernaryWantedLittleEndian.encode (TernaryGoodOutputCatalog.mapCodes maps τ)
    F 0 1 (descriptor maps τ targets positions n j).2 = _ at hg
  rw [TernaryTupleWantedLookup.encode_digits,zero_add,one_mul] at hg
  change Nat.ofDigits F ((descriptor maps τ targets positions n j).2.map
    (fun i => (TernaryGoodOutputCatalog.mapCodes maps τ).getD i 0)) =
      (get (queries (r := r) maps τ targets positions n) j.val).2.2 at hg
  rw [←hg]
  have hm := block_map maps τ targets positions n j
    (fun e : TernaryGoodOutputCatalog.Record m (Fin F) => (Fintype.equivFin (Fin F) e.1).val) 0
  unfold TernaryGoodOutputCatalog.mapCodes
  rw [←hm]
  simp only [List.map_ofFn,Function.comp_def]

theorem group_lt (maps : Fin F → Weight m p) (τ : ℕ) (targets : ℕ → ℤ)
    (positions : ℕ → ℕ) (n : ℕ) (hF : 1 < F)
    (j : Fin (queries (r := r) maps τ targets positions n).length) :
    (get (queries (r := r) maps τ targets positions n) j.val).2.2 < F^r := by
  rw [group_code]
  have hh := Nat.ofDigits_lt_base_pow_length hF (l := List.ofFn fun i : Fin r =>
    (Fintype.equivFin (Fin F) (block maps τ targets positions n j i).1).val) (by
      intro x hx
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      simpa only [Fintype.card_fin] using (Fintype.equivFin (Fin F) (block maps τ targets positions n j i).1).isLt)
  simpa only [List.length_ofFn] using hh

theorem position_code (maps : Fin F → Weight m p) (τ : ℕ) (targets : ℕ → ℤ)
    (positions : ℕ → ℕ) (n : ℕ) (j : Fin (queries (r := r) maps τ targets positions n).length) :
    (get (queries (r := r) maps τ targets positions n) j.val).1 =
      positions (descriptor maps τ targets positions n j).1 := by
  exact (congrArg (fun e : Entry => e.1) (emit_decode p (4^fixedLength m) F r
    (TernaryGoodOutputCatalog.raws maps τ) (TernaryGoodOutputCatalog.wordCodes maps τ)
    (TernaryGoodOutputCatalog.mapCodes maps τ) targets positions n j)).symm

theorem position_lt (maps : Fin F → Weight m p) (τ : ℕ) (targets : ℕ → ℤ)
    (positions : ℕ → ℕ) (n originalCount : ℕ) (hpos : ∀ t < n, positions t < originalCount)
    (j : Fin (queries (r := r) maps τ targets positions n).length) :
    (get (queries (r := r) maps τ targets positions n) j.val).1 < originalCount := by
  rw [position_code]
  exact hpos _ (descriptor_spec maps τ targets positions n j).1

theorem setup_Q {maps : Fin F → Weight m p} {τ cap : ℕ}
    {localQ : TernaryGoodOutputCatalog.Output m} {I : TernaryArenaSourceSetup.Input}
    {i : ℕ} (hi : i < (TernaryArenaSourceSetup.setup (r := r) maps τ cap localQ I).front.count) :
    (TernaryArenaSourceSetup.setup (r := r) maps τ cap localQ I).front.Q i =
      word maps τ I.targets I.positions I.requesterCount ⟨i,hi⟩ :=
  decoded_word maps τ I.targets I.positions I.requesterCount ⟨i,hi⟩

theorem setup_typed {maps : Fin F → Weight m p} {τ cap : ℕ}
    {localQ : TernaryGoodOutputCatalog.Output m} {I : TernaryArenaSourceSetup.Input}
    {i : ℕ} (hi : i < (TernaryArenaSourceSetup.setup (r := r) maps τ cap localQ I).front.count) :
    HasType ((TernaryArenaSourceSetup.setup (r := r) maps τ cap localQ I).front.Q i)
      (fun d => r*fixedPi m d) := by
  rw [setup_Q hi]
  exact typed maps τ I.targets I.positions I.requesterCount ⟨i,hi⟩

theorem setup_address {maps : Fin F → Weight m p} {τ cap : ℕ}
    {localQ : TernaryGoodOutputCatalog.Output m} {I : TernaryArenaSourceSetup.Input}
    {i : ℕ} (hi : i < (TernaryArenaSourceSetup.setup (r := r) maps τ cap localQ I).front.count) :
    TernaryCodeSemantics.address ((TernaryArenaSourceSetup.setup (r := r) maps τ cap localQ I).front.Q i) =
      (get (TernaryArenaSourceSetup.entries (r := r) maps τ I) i).2.1 := by
  rw [setup_Q hi]
  exact (word_code maps τ I.targets I.positions I.requesterCount ⟨i,hi⟩).symm

theorem setup_group_lt {maps : Fin F → Weight m p} {τ cap : ℕ}
    {localQ : TernaryGoodOutputCatalog.Output m} {I : TernaryArenaSourceSetup.Input}
    (hF : 1 < F) {i : ℕ}
    (hi : i < (TernaryArenaSourceSetup.setup (r := r) maps τ cap localQ I).front.count) :
    (TernaryArenaSourceSetup.setup (r := r) maps τ cap localQ I).front.group i < F^r :=
  group_lt maps τ I.targets I.positions I.requesterCount hF ⟨i,hi⟩

theorem setup_countTwo {maps : Fin F → Weight m p} {τ cap : ℕ}
    {localQ : TernaryGoodOutputCatalog.Output m} {I : TernaryArenaSourceSetup.Input}
    {i : ℕ} (hi : i < (TernaryArenaSourceSetup.setup (r := r) maps τ cap localQ I).front.count) :
    digitCount ((TernaryArenaSourceSetup.setup (r := r) maps τ cap localQ I).front.Q i) 2 = r*fixedPi m 2 :=
  setup_typed hi 2

theorem setup_rank {maps : Fin F → Weight m p} {τ cap : ℕ}
    {localQ : TernaryGoodOutputCatalog.Output m} {I : TernaryArenaSourceSetup.Input}
    {i : ℕ} (hi : i < (TernaryArenaSourceSetup.setup (r := r) maps τ cap localQ I).front.count) :
    TernaryBank.rank ((TernaryArenaSourceSetup.setup (r := r) maps τ cap localQ I).front.Q i) =
      r*TernaryArenaSourceSetup.alphaRank m + r*TernaryArenaSourceSetup.alphaRank m := by
  rw [TernaryDimensionBounds.rank_eq_counts,setup_typed hi 1,setup_typed hi 2]
  simp [fixedPi,fixedAlpha,TernaryArenaSourceSetup.alphaRank] <;> ring

theorem block_mem (maps : Fin F → Weight m p) (τ : ℕ) (targets : ℕ → ℤ)
    (positions : ℕ → ℕ) (n : ℕ) (j : Fin (queries (r := r) maps τ targets positions n).length)
    (i : Fin r) : block maps τ targets positions n j i ∈ TernaryGoodOutputCatalog.records maps τ :=
  List.getElem_mem _

theorem owner_blocks_injective (maps : Fin F → Weight m p) (τ : ℕ) (targets : ℕ → ℤ)
    (positions : ℕ → ℕ) (n : ℕ) :
    Function.Injective (fun j : Fin (queries (r := r) maps τ targets positions n).length =>
      ((descriptor maps τ targets positions n j).1,block maps τ targets positions n j)) := by
  intro a b hab
  apply decode_injective p (4^fixedLength m) F r (TernaryGoodOutputCatalog.raws maps τ)
    (TernaryGoodOutputCatalog.wordCodes maps τ) (TernaryGoodOutputCatalog.mapCodes maps τ) targets positions n
  change descriptor maps τ targets positions n a = descriptor maps τ targets positions n b
  apply Prod.ext
  · exact congrArg (fun x : ℕ × (Fin r → TernaryGoodOutputCatalog.Record m (Fin F)) => x.1) hab
  · have ha := descriptor_spec maps τ targets positions n a
    have hb := descriptor_spec maps τ targets positions n b
    apply List.ext_getElem (by omega)
    intro i hi hj
    have hir : i < r := by omega
    have hblock := congrFun (congrArg (fun x : ℕ × (Fin r → TernaryGoodOutputCatalog.Record m (Fin F)) => x.2) hab) ⟨i,hir⟩
    have hn : (TernaryGoodOutputCatalog.records maps τ).Nodup :=
      (TernaryGoodOutputCatalog.catalog maps τ).nodup_toList
    exact hn.getElem_inj_iff.mp hblock

theorem target_congruent (maps : Fin F → Weight m p) (τ : ℕ) (targets : ℕ → ℤ)
    (positions : ℕ → ℕ) (n : ℕ) (j : Fin (queries (r := r) maps τ targets positions n).length) :
    (p : ℤ)^r ∣ targets (descriptor maps τ targets positions n j).1 -
      Radix.positionalHash (p : ℤ) (TernaryGoodOutputCatalog.key maps)
        (List.ofFn (block maps τ targets positions n j)) := by
  have hd := (mem_descriptors p r (TernaryGoodOutputCatalog.raws maps τ) targets n _).mp
    (decode_mem p (4^fixedLength m) F r (TernaryGoodOutputCatalog.raws maps τ)
      (TernaryGoodOutputCatalog.wordCodes maps τ) (TernaryGoodOutputCatalog.mapCodes maps τ) targets positions n j)
  have ho := (TernaryWantedRadix.mem_wantedOutputs (p : ℤ)
    (by exact_mod_cast (Fact.out : p.Prime).ne_zero) (TernaryGoodOutputCatalog.raws maps τ)
    r (targets _) _).mp hd.2
  have hm := block_map maps τ targets positions n j (TernaryGoodOutputCatalog.key maps) 0
  have he : Radix.positionalHash (p : ℤ)
      (fun k => (TernaryGoodOutputCatalog.raws maps τ).getD k 0)
      (descriptor maps τ targets positions n j).2 =
      Radix.positionalHash (p : ℤ) (TernaryGoodOutputCatalog.key maps)
        (List.ofFn (block maps τ targets positions n j)) := by
    calc
      _ = Radix.positionalHash (p : ℤ) id
          ((descriptor maps τ targets positions n j).2.map
            (fun k => (TernaryGoodOutputCatalog.raws maps τ).getD k 0)) :=
        TernaryNativeTupleWitness.positional_map _ _ id _
      _ = Radix.positionalHash (p : ℤ) id
          ((List.ofFn (block maps τ targets positions n j)).map (TernaryGoodOutputCatalog.key maps)) :=
        congrArg _ hm.symm
      _ = _ := (TernaryNativeTupleWitness.positional_map _ _ id _).symm
  rw [←he]
  exact ho.2.2

theorem setup_star_typed (maps : Fin F → Weight m p) (τ cap : ℕ)
    (localQ : TernaryGoodOutputCatalog.Output m) (I : TernaryArenaSourceSetup.Input) :
    HasType ((TernaryArenaSourceSetup.setup (r := r) maps τ cap localQ I).front.Qstar)
      (fun d => r*fixedPi m d) := by
  change HasType (canonical (fun _ : Fin r => localQ.val)) _
  apply canonical_typed
  intro i
  exact (Finset.mem_filter.mp localQ.property).2

theorem setup_same_type {maps : Fin F → Weight m p} {τ cap : ℕ}
    {localQ : TernaryGoodOutputCatalog.Output m} {I : TernaryArenaSourceSetup.Input}
    {i : ℕ} (hi : i < (TernaryArenaSourceSetup.setup (r := r) maps τ cap localQ I).front.count) :
    ∀ d, digitCount ((TernaryArenaSourceSetup.setup (r := r) maps τ cap localQ I).front.Q i) d =
      digitCount ((TernaryArenaSourceSetup.setup (r := r) maps τ cap localQ I).front.Qstar) d := by
  intro d
  rw [setup_typed hi d,setup_star_typed maps τ cap localQ I d]

end ThreeSum.TernaryArenaQueryModel
