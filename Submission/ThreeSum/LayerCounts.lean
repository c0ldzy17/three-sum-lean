import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Lean.Elab.Tactic.Omega

/-!
# Exact counts for the local subset graph

These are counts of the executable finite sets used by the graph, rather
than abstract numerical cardinality hypotheses.  An edge is an ordered
pair of disjoint `h`-subsets of `Fin L`.
-/

namespace ThreeSum.LayerCounts

open Finset

def vertices (L h : ℕ) : Finset (Finset (Fin L)) :=
  Finset.univ.powersetCard h

def edgeSet (L h : ℕ) : Finset (Finset (Fin L) × Finset (Fin L)) :=
  (vertices L h ×ˢ vertices L h).filter (fun p => Disjoint p.1 p.2)

@[simp] theorem mem_vertices {L h : ℕ} {S : Finset (Fin L)} :
    S ∈ vertices L h ↔ S.card = h := by
  simp [vertices]

theorem vertices_card (L h : ℕ) : (vertices L h).card = L.choose h := by
  simp [vertices, card_powersetCard]

@[simp] theorem mem_edgeSet {L h : ℕ} {p : Finset (Fin L) × Finset (Fin L)} :
    p ∈ edgeSet L h ↔ p.1.card = h ∧ p.2.card = h ∧ Disjoint p.1 p.2 := by
  simp [edgeSet, and_assoc]

theorem leftFiber_card {L h : ℕ} (S : Finset (Fin L)) (hS : S.card = h) :
    ((edgeSet L h).filter (fun p => p.1 = S)).card = (L - h).choose h := by
  have hc : ((univ : Finset (Fin L)) \ S).card = L - h := by
    rw [card_sdiff_of_subset (subset_univ S)]
    simp [hS]
  rw [← hc, ← card_powersetCard]
  apply card_bij (fun p _ => p.2)
  · intro p hp
    rcases mem_filter.mp hp with ⟨hp, hpS⟩
    rcases mem_edgeSet.mp hp with ⟨_, hp2, hd⟩
    apply mem_powersetCard.mpr
    refine ⟨?_, hp2⟩
    intro i hi
    apply mem_sdiff.mpr
    refine ⟨mem_univ i, ?_⟩
    intro his
    exact disjoint_left.mp hd (hpS ▸ his) hi
  · intro p hp q hq he
    apply Prod.ext
    · exact (mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm
    · exact he
  · intro V hV
    rcases mem_powersetCard.mp hV with ⟨hsub, hcard⟩
    refine ⟨(S, V), ?_, rfl⟩
    apply mem_filter.mpr
    refine ⟨mem_edgeSet.mpr ⟨hS, hcard, ?_⟩, rfl⟩
    apply disjoint_left.mpr
    intro i his hiv
    exact (mem_sdiff.mp (hsub hiv)).2 his

theorem rightFiber_card {L h : ℕ} (V : Finset (Fin L)) (hV : V.card = h) :
    ((edgeSet L h).filter (fun p => p.2 = V)).card = (L - h).choose h := by
  rw [← leftFiber_card V hV]
  apply card_bij (fun p _ => p.swap)
  · intro p hp
    rcases mem_filter.mp hp with ⟨hp, hpV⟩
    rcases mem_edgeSet.mp hp with ⟨h1, h2, hd⟩
    exact mem_filter.mpr ⟨mem_edgeSet.mpr ⟨h2, h1, hd.symm⟩, hpV⟩
  · intro p hp q hq he
    exact Prod.swap_injective he
  · intro p hp
    rcases mem_filter.mp hp with ⟨hp, hpV⟩
    rcases mem_edgeSet.mp hp with ⟨h1, h2, hd⟩
    exact ⟨p.swap, mem_filter.mpr ⟨mem_edgeSet.mpr ⟨h2, h1, hd.symm⟩, hpV⟩,
      Prod.swap_swap p⟩

theorem unionFiber_card {L h : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = 2 * h) :
    ((edgeSet L h).filter (fun p => p.1 ∪ p.2 = Q)).card = (2 * h).choose h := by
  rw [← hQ, ← card_powersetCard]
  apply card_bij (fun p _ => p.1)
  · intro p hp
    rcases mem_filter.mp hp with ⟨hp, hpQ⟩
    exact mem_powersetCard.mpr ⟨hpQ ▸ subset_union_left, (mem_edgeSet.mp hp).1⟩
  · intro p hp q hq he
    rcases mem_filter.mp hp with ⟨hp, hpQ⟩
    rcases mem_filter.mp hq with ⟨hq, hqQ⟩
    have hpV : Q \ p.1 = p.2 := by
      rw [← hpQ]
      exact union_sdiff_cancel_left (mem_edgeSet.mp hp).2.2
    have hqV : Q \ q.1 = q.2 := by
      rw [← hqQ]
      exact union_sdiff_cancel_left (mem_edgeSet.mp hq).2.2
    exact Prod.ext he (by rw [← hpV, ← hqV, he])
  · intro S hS
    rcases mem_powersetCard.mp hS with ⟨hsub, hcard⟩
    refine ⟨(S, Q \ S), ?_, rfl⟩
    apply mem_filter.mpr
    refine ⟨mem_edgeSet.mpr ⟨hcard, ?_, ?_⟩, union_sdiff_of_subset hsub⟩
    · rw [card_sdiff_of_subset hsub, hQ, hcard]
      omega
    · exact disjoint_sdiff_self_right

theorem vertex_degree_identity (L h : ℕ) :
    L.choose h * (L - h).choose h = L.choose (2 * h) * (2 * h).choose h := by
  simpa [show 2 * h - h = h by omega] using
    (Nat.choose_mul (n := L) (k := 2 * h) (s := h) (by omega)).symm

theorem edgeSet_card (L h : ℕ) :
    (edgeSet L h).card = L.choose (2 * h) * (2 * h).choose h := by
  calc
    (edgeSet L h).card =
        ∑ S ∈ vertices L h, ((edgeSet L h).filter (fun p => p.1 = S)).card := by
      apply card_eq_sum_card_fiberwise
      intro p hp
      exact mem_vertices.mpr (mem_edgeSet.mp hp).1
    _ = ∑ S ∈ vertices L h, (L - h).choose h := by
      apply sum_congr rfl
      intro S hS
      exact leftFiber_card S (mem_vertices.mp hS)
    _ = L.choose h * (L - h).choose h := by
      simp [vertices_card]
    _ = _ := vertex_degree_identity L h

end ThreeSum.LayerCounts
