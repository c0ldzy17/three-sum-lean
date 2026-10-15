import Submission.ThreeSum.TernaryNativePairedLineage

noncomputable section
namespace ThreeSum.TernaryNativePrefixLineage
open Finset TernaryJointType TernaryCoverLocal TernaryCoverOutputCap
open TernaryOriginalRowMenu TernaryPairedPotential TernaryPairedContraction
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000

variable {p Λ L F : ℕ} [Fact p.Prime] {α π : DigitType}
variable {O B C : Type*} [Fintype O] [Fintype B] [Fintype C]

abbrev Out (L F : ℕ) (π : DigitType) := Fin F×{q // q∈vertices L π}

structure Model (p Λ L F : ℕ) [Fact p.Prime] (α π : DigitType) (O B C : Type*) where
  maps : Fin F→TernaryCoverHashes.Coordinate (Fin L)→ZMod p
  originalLeft : B→Fin Λ→ℤ
  originalRight : C→Fin Λ→ℤ
  row : ℕ→(Fin Λ→ZMod p)→ₗ[ZMod p] ZMod p
  root : O→ℕ→ZMod p
  good : Fin F→Prop
  keepLeft : Fin F→TritWord L→Prop
  keepRight : Fin F→TritWord L→Prop

namespace Model

variable (M : Model p Λ L F α π O B C)

def Group (r : ℕ) := {g : O×(Fin r→Out L F π) // ∀ j,
  M.good (g.2 j).1 ∧ outputHash (M.maps (g.2 j).1) (g.2 j).2.val=M.root g.1 j.val}

instance groupFinite (r : ℕ) : Fintype (M.Group r) := by
  classical
  unfold Group
  infer_instance

def Pair {r : ℕ} (g : M.Group r) := {x : (B×C)×(Fin r→LocalEdge L α π) // ∀ j,
  output (x.2 j)=(g.val.2 j).2.val ∧
  M.row j.val (fun a => (M.originalLeft x.1.1 a : ZMod p))=leftHash (M.maps (g.val.2 j).1) (x.2 j) ∧
  M.row j.val (fun a => (M.originalRight x.1.2 a : ZMod p))=rightHash (M.maps (g.val.2 j).1) (x.2 j) ∧
  M.keepLeft (g.val.2 j).1 (left (x.2 j)) ∧ M.keepRight (g.val.2 j).1 (right (x.2 j))}

instance pairFinite {r : ℕ} (g : M.Group r) : Fintype (M.Pair g) := by
  classical
  unfold Pair
  infer_instance

abbrev Index (r K : ℕ) := Σ g : M.Group r, Fin K→M.Pair g


def parentGroup {r : ℕ} (g : M.Group (r+1)) : M.Group r :=
  ⟨(g.val.1,fun j => g.val.2 j.castSucc),fun j => g.property j.castSucc⟩

def parentPair {r : ℕ} {g : M.Group (r+1)} (x : M.Pair g) : M.Pair (M.parentGroup g) :=
  ⟨(x.val.1,fun j => x.val.2 j.castSucc),fun j => x.property j.castSucc⟩

def parent {r K : ℕ} (x : M.Index (r+1) K) : M.Index r K :=
  ⟨M.parentGroup x.1,fun i => M.parentPair (x.2 i)⟩

def child {r K : ℕ} (x : M.Index (r+1) K) : Child L K F α π :=
  ((x.1.val.2 (Fin.last r)).1,
    ⟨(x.1.val.2 (Fin.last r)).2,fun i => ⟨(x.2 i).val.2 (Fin.last r),((x.2 i).property (Fin.last r)).1⟩⟩)

def lineage {r K : ℕ} (x : M.Index (r+1) K) : M.Index r K×Child L K F α π :=
  (M.parent x,M.child x)

/-- Original requester/carry IDs, original endpoint IDs, map occurrences,
outputs and every ordered local partition can all be reconstructed. -/
theorem lineage_injective (r K : ℕ) : Function.Injective (M.lineage (r := r) (K := K)) := by
  intro x y h
  have hp := congrArg Prod.fst h
  have hc := congrArg Prod.snd h
  have hgp : (M.parentGroup x.1).val=(M.parentGroup y.1).val :=
    congrArg (fun z : M.Index r K => z.1.val) hp
  have hgl : x.1.val.2 (Fin.last r)=y.1.val.2 (Fin.last r) := by
    apply Prod.ext
    · simpa only [lineage,child] using congrArg (fun c : Child L K F α π => c.1) hc
    · exact congrArg (fun c : Child L K F α π => c.2.1) hc
  have hg : x.1=y.1 := by
    apply Subtype.ext
    apply Prod.ext
    · simpa only [parentGroup] using congrArg (fun z : O×(Fin r→Out L F π) => z.1) hgp
    · funext j
      refine Fin.lastCases hgl (fun i => ?_) j
      exact congrFun (congrArg Prod.snd hgp) i
  obtain ⟨g,e⟩ := x
  obtain ⟨g',f⟩ := y
  dsimp only at hg
  subst g'
  suffices hh : e=f by cases hh; rfl
  funext i
  apply Subtype.ext
  have hraw := congrArg (fun z : M.Index r K => fun i => (z.2 i).val) hp
  have hfirst : (e i).val.1=(f i).val.1 := congrArg (fun z => (z i).1) hraw
  apply Prod.ext hfirst
  funext j
  refine Fin.lastCases ?_ (fun t => ?_) j
  · exact congrArg (fun c : Child L K F α π => (c.2.2 i).val) hc
  · exact congrArg (fun z => (z i).2 t) hraw

def matrix {r K : ℕ} (x : M.Index r K) : Matrix (Fin (K+K)) (Fin Λ) ℤ :=
  fun i => Sum.elim (fun j => M.originalLeft (x.2 j).val.1.1)
    (fun j => M.originalRight (x.2 j).val.1.2) (finSumFinEquiv.symm i)

theorem matrix_parent {r K : ℕ} (x : M.Index (r+1) K) : M.matrix x=M.matrix (M.parent x) := rfl

theorem last_row_event {r K : ℕ} {E : Type*} [Field E] [Fintype E]
    [DecidableEq E] [Algebra (ZMod p) E]
    (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E) (hrow : M.row r=TernaryOriginalRowMenu.row Λ ℓ seed)
    (x : M.Index (r+1) K) :
    seed∈menuEvent ℓ (fun i j => (M.matrix (M.parent x) i j : ZMod p)) (childTarget M.maps (M.child x)) := by
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  intro i
  cases hs : finSumFinEquiv.symm i with
  | inl j =>
    simp only [matrix,parent,parentPair,childTarget,child,hs,Sum.elim_inl]
    have hh := ((x.2 j).property (Fin.last r)).2.1
    simpa only [Fin.val_last,hrow] using hh
  | inr j =>
    simp only [matrix,parent,parentPair,childTarget,child,hs,Sum.elim_inr]
    have hh := ((x.2 j).property (Fin.last r)).2.2.1
    simpa only [Fin.val_last,hrow] using hh

theorem retained_next_le {r K : ℕ} {E : Type*} [Field E] [Fintype E]
    [DecidableEq E] [Algebra (ZMod p) E]
    (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E) (hrow : M.row r=TernaryOriginalRowMenu.row Λ ℓ seed) :
    potential (M.matrix (r := r+1) (K := K))≤
      nextPotential (α := α) (π := π) ℓ (M.matrix (r := r) (K := K)) M.maps seed :=
  TernaryNativePairedLineage.retained_potential_le ℓ (M.matrix (r := r) (K := K))
    (M.matrix (r := r+1) (K := K)) M.maps seed M.lineage (M.lineage_injective r K)
    M.matrix_parent (M.last_row_event ℓ seed hrow)

end Model
end ThreeSum.TernaryNativePrefixLineage
