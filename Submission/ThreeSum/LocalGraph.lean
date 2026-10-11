import Submission.ThreeSum.LayerCounts
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Bool.Basic
import Lean.Elab.Tactic.Omega

/-!
# The concrete local subset graph and its binary words

A left vertex has ones exactly on its `h`-subset.  A right vertex has zeros
exactly on its `h`-subset.  The endpoint maps, their separation, and the
equality mask are proved directly from finite-set membership.
-/

namespace ThreeSum.LocalGraph

variable {α : Type*} [DecidableEq α]

def leftWord (s : Finset α) : α → Bool := fun i => decide (i ∈ s)

def rightWord (v : Finset α) : α → Bool := fun i => decide (i ∉ v)

theorem leftWord_injective : Function.Injective (@leftWord α _) := by
  intro s t he
  ext i
  simpa only [leftWord, decide_eq_decide] using congrFun he i

theorem rightWord_injective : Function.Injective (@rightWord α _) := by
  intro s t he
  ext i
  have hi := congrFun he i
  simpa only [rightWord, decide_eq_decide, not_iff_not] using hi

theorem leftWord_eq_rightWord_iff [Fintype α] (s v : Finset α) :
    leftWord s = rightWord v ↔ s = Finset.univ \ v := by
  constructor
  · intro he
    ext i
    have hi := congrFun he i
    simpa only [leftWord, rightWord, decide_eq_decide, Finset.mem_sdiff,
      Finset.mem_univ, true_and] using hi
  · intro he
    subst s
    funext i
    simp only [leftWord, rightWord, Finset.mem_sdiff, Finset.mem_univ, true_and]

/-- With `2*h<L`, no left vertex word can equal any right vertex word, even
when the two vertices do not form an edge. -/
theorem leftWord_ne_rightWord {L h : ℕ} {s v : Finset (Fin L)}
    (hs : s.card = h) (hv : v.card = h) (hsep : 2 * h < L) :
    leftWord s ≠ rightWord v := by
  intro he
  have hc := congrArg Finset.card ((leftWord_eq_rightWord_iff s v).mp he)
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ v)] at hc
  simp only [Finset.card_univ, Fintype.card_fin, hs, hv] at hc
  omega

/-- The equality mask is true exactly on the union of the disjoint endpoint
subsets. This identifies the exceptional four-word hash fibers. -/
theorem equalityMask_eq_union {s v : Finset α} (hd : Disjoint s v) :
    (fun i => leftWord s i == rightWord v i) = leftWord (s ∪ v) := by
  funext i
  have hnot := Finset.disjoint_left.mp hd
  by_cases hs : i ∈ s <;> by_cases hv : i ∈ v <;>
    simp_all [leftWord, rightWord]

theorem equalityMask_eq_iff_union_eq {s v s' v' : Finset α}
    (hd : Disjoint s v) (hd' : Disjoint s' v') :
    (fun i => leftWord s i == rightWord v i) =
        (fun i => leftWord s' i == rightWord v' i) ↔ s ∪ v = s' ∪ v' := by
  rw [equalityMask_eq_union hd, equalityMask_eq_union hd']
  exact leftWord_injective.eq_iff

section ConcreteGraph

open LayerCounts

/-- The enumerated ordered pairs of disjoint `h`-subsets are the edge type. -/
abbrev Edge (L h : ℕ) := {p // p ∈ edgeSet L h}

variable {L h : ℕ}

def left (e : Edge L h) : Fin L → Bool := leftWord e.val.1

def right (e : Edge L h) : Fin L → Bool := rightWord e.val.2

def output (e : Edge L h) : Finset (Fin L) := e.val.1 ∪ e.val.2

def equalityMask (e : Edge L h) : Fin L → Bool := fun i => left e i == right e i

theorem edge_data (e : Edge L h) :
    e.val.1.card = h ∧ e.val.2.card = h ∧ Disjoint e.val.1 e.val.2 :=
  mem_edgeSet.mp e.property

theorem output_card (e : Edge L h) : (output e).card = 2 * h := by
  rw [output, Finset.card_union_of_disjoint (edge_data e).2.2,
    (edge_data e).1, (edge_data e).2.1]
  omega

theorem endpoint_injective :
    Function.Injective (fun e : Edge L h => (left e, right e)) := by
  intro e f he
  apply Subtype.ext
  exact Prod.ext (leftWord_injective (congrArg Prod.fst he))
    (rightWord_injective (congrArg Prod.snd he))

theorem cross_separated (hsep : 2 * h < L) (e f : Edge L h) : left e ≠ right f :=
  leftWord_ne_rightWord (edge_data e).1 (edge_data f).2.1 hsep

theorem equalityMask_eq_output (e : Edge L h) :
    equalityMask e = leftWord (output e) :=
  equalityMask_eq_union (edge_data e).2.2

theorem equalityMask_eq_iff (e f : Edge L h) :
    equalityMask e = equalityMask f ↔ output e = output f := by
  rw [equalityMask_eq_output, equalityMask_eq_output]
  exact leftWord_injective.eq_iff

def leftVertices (L h : ℕ) : Finset (Fin L → Bool) :=
  (vertices L h).image leftWord

def rightVertices (L h : ℕ) : Finset (Fin L → Bool) :=
  (vertices L h).image rightWord

theorem leftVertices_card (L h : ℕ) : (leftVertices L h).card = L.choose h := by
  rw [leftVertices, Finset.card_image_of_injective _ leftWord_injective, vertices_card]

theorem rightVertices_card (L h : ℕ) : (rightVertices L h).card = L.choose h := by
  rw [rightVertices, Finset.card_image_of_injective _ rightWord_injective, vertices_card]

theorem left_mem_vertices (e : Edge L h) : left e ∈ leftVertices L h :=
  Finset.mem_image.mpr ⟨e.val.1, mem_vertices.mpr (edge_data e).1, rfl⟩

theorem right_mem_vertices (e : Edge L h) : right e ∈ rightVertices L h :=
  Finset.mem_image.mpr ⟨e.val.2, mem_vertices.mpr (edge_data e).2.1, rfl⟩

theorem vertex_sets_separated (hsep : 2 * h < L)
    (s : Fin L → Bool) (hs : s ∈ leftVertices L h)
    (t : Fin L → Bool) (ht : t ∈ rightVertices L h) : s ≠ t := by
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp ht
  exact leftWord_ne_rightWord (mem_vertices.mp hS) (mem_vertices.mp hV) hsep

/-- Transfer counts in a finite subtype to counts in its actual enumerated
domain. This lemma introduces no larger sample space. -/
theorem subtype_filter_card {β : Type*} [DecidableEq β] (s : Finset β)
    (p : β → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun e : s => p e.val)).card = (s.filter p).card := by
  apply Finset.card_bij (fun e _ => e.val)
  · intro e he
    exact Finset.mem_filter.mpr ⟨e.property, (Finset.mem_filter.mp he).2⟩
  · intro e _ f _ he
    exact Subtype.ext he
  · intro x hx
    refine ⟨⟨x, (Finset.mem_filter.mp hx).1⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩

theorem edge_card (L h : ℕ) :
    Fintype.card (Edge L h) = L.choose (2 * h) * (2 * h).choose h := by
  rw [Fintype.card_coe, edgeSet_card]

/-- Every endpoint has exactly the combinatorial degree, expressed on the
edge subtype used by the finite hash experiment. -/
theorem left_fiber_card (e : Edge L h) :
    (Finset.univ.filter (fun f : Edge L h => left f = left e)).card =
      (L - h).choose h := by
  simp only [left, leftWord_injective.eq_iff]
  exact (subtype_filter_card (edgeSet L h) (fun p => p.1 = e.val.1)).trans
    (leftFiber_card e.val.1 (edge_data e).1)

theorem right_fiber_card (e : Edge L h) :
    (Finset.univ.filter (fun f : Edge L h => right f = right e)).card =
      (L - h).choose h := by
  simp only [right, rightWord_injective.eq_iff]
  exact (subtype_filter_card (edgeSet L h) (fun p => p.2 = e.val.2)).trans
    (rightFiber_card e.val.2 (edge_data e).2.1)

/-- The exceptional equality-mask group has exactly one edge for each
`h`-subset of its `2*h` output coordinates. -/
theorem equalityMask_fiber_card (e : Edge L h) :
    (Finset.univ.filter (fun f : Edge L h => equalityMask f = equalityMask e)).card =
      (2 * h).choose h := by
  simp only [equalityMask_eq_iff, output]
  exact (subtype_filter_card (edgeSet L h) (fun p => p.1 ∪ p.2 = e.val.1 ∪ e.val.2)).trans
    (unionFiber_card (output e) (output_card e))

theorem endpoint_fiber_bounds (e : Edge L h) :
    (Finset.univ.filter (fun f : Edge L h => left f = left e)).card ≤
        (L - h).choose h ∧
      (Finset.univ.filter (fun f : Edge L h => right f = right e)).card ≤
        (L - h).choose h := by
  exact ⟨(left_fiber_card e).le, (right_fiber_card e).le⟩

theorem mask_fiber_bound (e : Edge L h) :
    (Finset.univ.filter (fun f : Edge L h =>
      (fun i => left f i == right f i) = (fun i => left e i == right e i))).card ≤
      (2 * h).choose h :=
  (equalityMask_fiber_card e).le

end ConcreteGraph

end ThreeSum.LocalGraph
