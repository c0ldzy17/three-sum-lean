import Submission.ThreeSum.TernaryArenaSourceModel
import Submission.ThreeSum.TernaryArenaQueryNative
import Submission.ThreeSum.TernaryNativePairMoments

noncomputable section
namespace ThreeSum.TernaryArenaPairModel
open Finset TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps TernaryArenaSourceSetup
open TernaryNativePairMoments TernaryArenaSourceModel TernaryCoverLocal
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
variable {p m F r : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (localQ : TernaryGoodOutputCatalog.Output m) (I : Input)

abbrev Host := setup (r := r) maps τ cap localQ I

variable {maps τ cap localQ I}

theorem left_mem {i : ℕ} (x : Pair (Host (r := r) maps τ cap localQ I) i) :
    x.val.1∈(source (r := r) maps cap I false).records := by
  exact (mem_filter.mp (mem_product.mp (mem_filter.mp x.property).1).1).1

theorem right_mem {i : ℕ} (x : Pair (Host (r := r) maps τ cap localQ I) i) :
    x.val.2∈(source (r := r) maps cap I true).records := by
  exact (mem_filter.mp (mem_product.mp (mem_filter.mp x.property).1).2).1

def leftIndex {i : ℕ} (x : Pair (Host (r := r) maps τ cap localQ I) i) :
    Index (r := r) maps cap false :=
  ⟨x.val.1.2,by
    have hh := ((TernarySourceHostModel.mem_records _ _ _ _ _ _).mp (left_mem x)).2.1
    simpa only [source,TernarySourceExecutionFactory.Setup.records,LightTernarySourceHost.size,
      List.length_map] using hh⟩

def rightIndex {i : ℕ} (x : Pair (Host (r := r) maps τ cap localQ I) i) :
    Index (r := r) maps cap true :=
  ⟨x.val.2.2,by
    have hh := ((TernarySourceHostModel.mem_records _ _ _ _ _ _).mp (right_mem x)).2.1
    simpa only [source,TernarySourceExecutionFactory.Setup.records,LightTernarySourceHost.size,
      List.length_map] using hh⟩

def outputBlock {i : ℕ} (hi : i<(Host (r := r) maps τ cap localQ I).front.count) :=
  TernaryArenaQueryModel.block maps τ I.targets I.positions I.requesterCount (⟨i,hi⟩)

theorem left_occurrence {i : ℕ} (hi : i<(Host (r := r) maps τ cap localQ I).front.count)
    (x : Pair (Host (r := r) maps τ cap localQ I) i) :
    (fun t => (TernaryCanonicalSourceBank.block false maps cap (leftIndex x) t).1)=
      (fun t => (outputBlock (maps := maps) (τ := τ) (cap := cap) (localQ := localQ) (I := I) hi t).1) := by
  apply TernaryNativeBlockPairs.occurrenceCode_injective
  have hg := (mem_filter.mp (mem_product.mp (mem_filter.mp x.property).1).1).2
  rw [←group_spec maps cap I false (leftIndex x)]
  change (source (r := r) maps cap I false).group x.val.1.2=_
  change (source (r := r) maps cap I false).group x.val.1.2=
    (TernaryWantedBatchIndex.get (entries (r := r) maps τ I) i).2.2 at hg
  rw [hg]
  exact TernaryArenaQueryModel.group_code maps τ I.targets I.positions I.requesterCount ⟨i,hi⟩

theorem right_occurrence {i : ℕ} (hi : i<(Host (r := r) maps τ cap localQ I).front.count)
    (x : Pair (Host (r := r) maps τ cap localQ I) i) :
    (fun t => (TernaryCanonicalSourceBank.block true maps cap (rightIndex x) t).1)=
      (fun t => (outputBlock (maps := maps) (τ := τ) (cap := cap) (localQ := localQ) (I := I) hi t).1) := by
  apply TernaryNativeBlockPairs.occurrenceCode_injective
  have hg := (mem_filter.mp (mem_product.mp (mem_filter.mp x.property).1).2).2
  rw [←group_spec maps cap I true (rightIndex x)]
  change (source (r := r) maps cap I true).group x.val.2.2=_
  change (source (r := r) maps cap I true).group x.val.2.2=
    (TernaryWantedBatchIndex.get (entries (r := r) maps τ I) i).2.2 at hg
  rw [hg]
  exact TernaryArenaQueryModel.group_code maps τ I.targets I.positions I.requesterCount ⟨i,hi⟩

theorem block_adds {i : ℕ} (hi : i<(Host (r := r) maps τ cap localQ I).front.count)
    (x : Pair (Host (r := r) maps τ cap localQ I) i) :
    TernaryConvolution.Adds
      (TernaryCanonicalSourceBank.word false maps cap (leftIndex x))
      (TernaryCanonicalSourceBank.word true maps cap (rightIndex x))
      (TernaryArenaQueryModel.word maps τ I.targets I.positions I.requesterCount ⟨i,hi⟩) := by
  have hh := (mem_filter.mp x.property).2
  change TernaryConvolution.Adds
    ((TernaryBankCanonical.enumeration (N m r) (cut m r)).word ((source (r := r) maps cap I false).key (leftIndex x).val))
    ((TernaryBankCanonical.enumeration (N m r) (cut m r)).word ((source (r := r) maps cap I true).key (rightIndex x).val))
    ((Host (r := r) maps τ cap localQ I).front.Q i) at hh
  rw [word_spec maps cap I false (leftIndex x),word_spec maps cap I true (rightIndex x),
    TernaryArenaQueryModel.setup_Q hi] at hh
  exact hh

def edge {i : ℕ} (hi : i<(Host (r := r) maps τ cap localQ I).front.count)
    (x : Pair (Host (r := r) maps τ cap localQ I) i) : Fin r→ActualEdge m :=
  TernaryNativeBlockPairs.edges
    (fun t => (TernaryCanonicalSourceBank.block false maps cap (leftIndex x) t).2)
    (fun t => (TernaryCanonicalSourceBank.block true maps cap (rightIndex x) t).2)
    (fun t => (outputBlock (maps := maps) (τ := τ) (cap := cap) (localQ := localQ) (I := I) hi t).2)
    (block_adds hi x)


theorem left_hash {i : ℕ} (hi : i<(Host (r := r) maps τ cap localQ I).front.count)
    (x : Pair (Host (r := r) maps τ cap localQ I) i) (t : Fin r) :
    TernaryCanonicalSourceBank.nativeRow false maps cap (leftIndex x) t=
      leftHash (maps (outputBlock (maps := maps) (τ := τ) (cap := cap) (localQ := localQ) (I := I) hi t).1)
        (edge hi x t) := by
  have ho := congrFun (left_occurrence hi x) t
  change TernaryCoverHashes.linearHash
    (TernaryCoverHashes.leftVector (fieldWord p (TernaryCanonicalSourceBank.block false maps cap (leftIndex x) t).2.val))
    (maps (TernaryCanonicalSourceBank.block false maps cap (leftIndex x) t).1)=_
  rw [ho]
  rfl

theorem right_hash {i : ℕ} (hi : i<(Host (r := r) maps τ cap localQ I).front.count)
    (x : Pair (Host (r := r) maps τ cap localQ I) i) (t : Fin r) :
    TernaryCanonicalSourceBank.nativeRow true maps cap (rightIndex x) t=
      rightHash (maps (outputBlock (maps := maps) (τ := τ) (cap := cap) (localQ := localQ) (I := I) hi t).1)
        (edge hi x t) := by
  have ho := congrFun (right_occurrence hi x) t
  change TernaryCoverHashes.linearHash
    (TernaryCoverHashes.rightVector (fieldWord p (TernaryCanonicalSourceBank.block true maps cap (rightIndex x) t).2.val))
    (maps (TernaryCanonicalSourceBank.block true maps cap (rightIndex x) t).1)=_
  rw [ho]
  rfl

theorem pair_encoding_injective {i : ℕ}
    (hi : i<(Host (r := r) maps τ cap localQ I).front.count) :
    Function.Injective (fun x : Pair (Host (r := r) maps τ cap localQ I) i =>
      ((x.val.1.1,x.val.2.1),edge hi x)) := by
  intro x y he
  have heB := congrArg (fun z : (ℕ×ℕ)×(Fin r→ActualEdge m) => z.1.1) he
  have heC := congrArg (fun z : (ℕ×ℕ)×(Fin r→ActualEdge m) => z.1.2) he
  have heE := congrArg (fun z : (ℕ×ℕ)×(Fin r→ActualEdge m) => z.2) he
  have hl : leftIndex x=leftIndex y := by
    apply TernaryCanonicalSourceBank.block_injective false maps cap
    funext t
    apply Prod.ext
    · exact (congrFun (left_occurrence hi x) t).trans (congrFun (left_occurrence hi y) t).symm
    · apply Subtype.ext
      exact congrArg left (congrFun heE t)
  have hr : rightIndex x=rightIndex y := by
    apply TernaryCanonicalSourceBank.block_injective true maps cap
    funext t
    apply Prod.ext
    · exact (congrFun (right_occurrence hi x) t).trans (congrFun (right_occurrence hi y) t).symm
    · apply Subtype.ext
      exact congrArg right (congrFun heE t)
  apply Subtype.ext
  exact Prod.ext (Prod.ext heB (congrArg Fin.val hl)) (Prod.ext heC (congrArg Fin.val hr))


theorem original_hash_sum {i : ℕ} (hi : i<(Host (r := r) maps τ cap localQ I).front.count)
    (x : Pair (Host (r := r) maps τ cap localQ I) i)
    (B C O : ℕ→Fin r→ZMod p)
    (hB : ∀ j<I.nB, I.leftInput j=(TernaryExtensionEncoding.coefficientCode (B j) : ℤ))
    (hC : ∀ j<I.nC, I.rightInput j=(TernaryExtensionEncoding.coefficientCode (C j) : ℤ))
    (hO : ∀ j<I.requesterCount, I.targets j=(TernaryExtensionEncoding.coefficientCode (O j) : ℤ)) :
    B x.val.1.1+C x.val.2.1=
      O (TernaryArenaQueryModel.descriptor maps τ I.targets I.positions I.requesterCount ⟨i,hi⟩).1 := by
  obtain ⟨jL,hjL,hL⟩ := TernaryArenaSourceModel.original_rows maps cap I false B hB _ (left_mem x)
  obtain ⟨jR,hjR,hR⟩ := TernaryArenaSourceModel.original_rows maps cap I true C hC _ (right_mem x)
  have heL : jL=leftIndex x := Fin.ext hjL
  have heR : jR=rightIndex x := Fin.ext hjR
  rw [heL] at hL
  rw [heR] at hR
  have ho := TernaryArenaQueryModel.target_row maps τ I.targets I.positions I.requesterCount ⟨i,hi⟩
    (O (TernaryArenaQueryModel.descriptor maps τ I.targets I.positions I.requesterCount ⟨i,hi⟩).1)
    (hO _ (TernaryArenaQueryModel.descriptor_spec maps τ I.targets I.positions I.requesterCount ⟨i,hi⟩).1)
  rw [hL,hR,←ho]
  funext t
  change TernaryCanonicalSourceBank.nativeRow false maps cap (leftIndex x) t+
    TernaryCanonicalSourceBank.nativeRow true maps cap (rightIndex x) t=_
  rw [left_hash hi x t,right_hash hi x t,TernaryCoverLocal.hashes_add]
  rfl

end ThreeSum.TernaryArenaPairModel
