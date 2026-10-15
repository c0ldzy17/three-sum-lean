import Submission.ThreeSum.TernaryArenaPairModel
import Submission.ThreeSum.TernaryArenaQueryEncode
import Submission.ThreeSum.TernaryNativePrefixLineage

noncomputable section
namespace ThreeSum.TernaryArenaPrefixGroups
open Finset TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps TernaryCoverLocal
open TernaryArenaSourceSetup TernaryExtensionEncoding TernaryCanonicalDictionaries
open TernaryNativePrefixLineage
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
variable {p m F Λ : ℕ} [Fact p.Prime]

def keepLeft (maps : Fin F→Weight m p) (cap : ℕ) (i : Fin F) (w : TritWord (fixedLength m)) : Prop :=
  TernaryCoverTrimming.bucketSize (fieldVertices (fixedLength m) p (fixedAlpha m))
    TernaryCoverHashes.leftVector (maps i)
    (TernaryCoverHashes.linearHash (TernaryCoverHashes.leftVector (fieldWord p w)) (maps i))≤cap

def keepRight (maps : Fin F→Weight m p) (cap : ℕ) (i : Fin F) (w : TritWord (fixedLength m)) : Prop :=
  TernaryCoverTrimming.bucketSize (fieldVertices (fixedLength m) p (fixedAlpha m))
    TernaryCoverHashes.rightVector (maps i)
    (TernaryCoverHashes.linearHash (TernaryCoverHashes.rightVector (fieldWord p w)) (maps i))≤cap

def model (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input)
    (L R : ℕ→Fin Λ→ℤ) (row : ℕ→(Fin Λ→ZMod p)→ₗ[ZMod p] ZMod p)
    (root : ℕ→ℕ→ZMod p) : Model p Λ (fixedLength m) F (fixedAlpha m) (fixedPi m)
      (Fin I.requesterCount) (Fin I.nB) (Fin I.nC) where
  maps := maps
  originalLeft := fun i => L i.val
  originalRight := fun i => R i.val
  row := row
  root := fun i j => root i.val j
  good := fun i => maps i∉rawBadMaps m p τ
  keepLeft := keepLeft maps cap
  keepRight := keepRight maps cap

def input (I : Input) (L R : ℕ→Fin Λ→ℤ)
    (row : ℕ→(Fin Λ→ZMod p)→ₗ[ZMod p] ZMod p) (root : ℕ→ℕ→ZMod p) (r : ℕ) : Input :=
  {I with
    leftInput:=fun i => (coefficientCode (fun j : Fin r => row j.val (fun t => (L i t : ZMod p))) : ℤ)
    rightInput:=fun i => (coefficientCode (fun j : Fin r => row j.val (fun t => (R i t : ZMod p))) : ℤ)
    targets:=fun i => (coefficientCode (fun j : Fin r => root i j.val) : ℤ)}

variable (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input) (L R : ℕ→Fin Λ→ℤ)
    (row : ℕ→(Fin Λ→ZMod p)→ₗ[ZMod p] ZMod p) (root : ℕ→ℕ→ZMod p)

abbrev M := model maps τ cap I L R row root

def group (r : ℕ) (j : Fin (TernaryArenaQueryModel.queries (r := r) maps τ
    (input I L R row root r).targets I.positions I.requesterCount).length) :
    (M maps τ cap I L R row root).Group r :=
  let out := TernaryArenaQueryModel.block maps τ (input I L R row root r).targets I.positions I.requesterCount j
  let owner := TernaryArenaQueryModel.descriptor maps τ (input I L R row root r).targets I.positions I.requesterCount j
  ⟨(⟨owner.1,(TernaryArenaQueryModel.descriptor_spec maps τ _ _ _ j).1⟩,out),by
    intro t
    refine ⟨(TernaryGoodOutputCatalog.mem_records maps τ _).mp
      (TernaryArenaQueryModel.block_mem maps τ _ _ _ j t),?_⟩
    have hh := TernaryArenaQueryModel.target_row maps τ (input I L R row root r).targets
      I.positions I.requesterCount j (fun t : Fin r => root owner.1 t.val) rfl
    exact congrFun hh t⟩

theorem group_injective (r : ℕ) : Function.Injective (group maps τ cap I L R row root r) := by
  intro i j he
  apply TernaryArenaQueryModel.owner_blocks_injective maps τ _ _ _
  apply Prod.ext
  · exact congrArg (fun g : (M maps τ cap I L R row root).Group r => g.val.1.val) he
  · exact congrArg (fun g : (M maps τ cap I L R row root).Group r => g.val.2) he

theorem group_surjective (r : ℕ) : Function.Surjective (group maps τ cap I L R row root r) := by
  intro g
  have hm (j : Fin r) : g.val.2 j∈TernaryGoodOutputCatalog.records maps τ :=
    (TernaryGoodOutputCatalog.mem_records maps τ _).mpr (g.property j).1
  have hdiv : (p : ℤ)^r∣(input I L R row root r).targets g.val.1.val-
      Radix.positionalHash (p : ℤ) (TernaryGoodOutputCatalog.key maps) (List.ofFn g.val.2) := by
    have hh := TernaryNativeTupleWitness.positional_ofFn g.val.2 (TernaryGoodOutputCatalog.key maps)
      (fun j : Fin r => root g.val.1.val j.val) (fun j => by
        unfold TernaryGoodOutputCatalog.key TernaryGoodOutputCatalog.native
        have hr : outputHash (maps (g.val.2 j).1) (g.val.2 j).2.val=root g.val.1.val j.val :=
          (g.property j).2
        rw [hr])
    rw [hh]
    change (p : ℤ)^r∣(coefficientCode (fun j : Fin r => root g.val.1.val j.val) : ℤ)-
      (coefficientCode (fun j : Fin r => root g.val.1.val j.val) : ℤ)
    rw [sub_self]
    exact dvd_zero _
  obtain ⟨j,ho,hout⟩ := TernaryArenaQueryEncode.exists_query maps τ (input I L R row root r).targets
    I.positions I.requesterCount g.val.1.val g.val.1.isLt g.val.2 hm hdiv
  refine ⟨j,?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact Fin.ext ho
  · exact hout

def groupEquiv (r : ℕ) := Equiv.ofBijective (group maps τ cap I L R row root r)
  ⟨group_injective maps τ cap I L R row root r,group_surjective maps τ cap I L R row root r⟩

end ThreeSum.TernaryArenaPrefixGroups
