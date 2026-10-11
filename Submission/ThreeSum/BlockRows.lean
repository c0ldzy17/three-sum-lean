import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Ring.Nat
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Flattening a block family of subsets

The coordinates retain the block index explicitly. Joining and slicing are
mutually inverse, preserve Boolean set operations, and give exact cardinalities
for balanced full inputs and forced prefixes.
-/

namespace ThreeSum.BlockRows

open Finset
open scoped BigOperators

abbrev Coord (J L : ℕ) := Σ _i : Fin J, Fin L

def join {J L : ℕ} (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) :
    Finset (Coord J L) := I.sigma u

def flat {J L : ℕ} (u : Fin J → Finset (Fin L)) : Finset (Coord J L) := join univ u

def row {J L : ℕ} (S : Finset (Coord J L)) (i : Fin J) : Finset (Fin L) :=
  Finset.univ.filter fun x => Sigma.mk i x ∈ S

@[simp] theorem mem_join {J L : ℕ} {I : Finset (Fin J)}
    {u : Fin J → Finset (Fin L)} {i : Fin J} {x : Fin L} :
    Sigma.mk i x ∈ join I u ↔ i ∈ I ∧ x ∈ u i := Finset.mem_sigma

@[simp] theorem mem_flat {J L : ℕ} {u : Fin J → Finset (Fin L)}
    {i : Fin J} {x : Fin L} : Sigma.mk i x ∈ flat u ↔ x ∈ u i := by
  simp only [flat, mem_join, Finset.mem_univ, true_and]

@[simp] theorem mem_row {J L : ℕ} {S : Finset (Coord J L)} {i : Fin J} {x : Fin L} :
    x ∈ row S i ↔ Sigma.mk i x ∈ S := by
  simp only [row, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem row_flat {J L : ℕ} (u : Fin J → Finset (Fin L)) (i : Fin J) :
    row (flat u) i = u i := by ext x; simp

@[simp] theorem flat_row {J L : ℕ} (S : Finset (Coord J L)) : flat (row S) = S := by
  ext ⟨i, x⟩; simp

@[simp] theorem row_join {J L : ℕ} (I : Finset (Fin J))
    (u : Fin J → Finset (Fin L)) (i : Fin J) :
    row (join I u) i = if i ∈ I then u i else ∅ := by
  ext x
  by_cases hi : i ∈ I <;> simp [hi]

theorem row_subset {J L : ℕ} {S T : Finset (Coord J L)} (h : S ⊆ T) (i : Fin J) :
    row S i ⊆ row T i := by
  intro x hx
  exact mem_row.mpr (h (mem_row.mp hx))

theorem subset_iff_rows {J L : ℕ} {S T : Finset (Coord J L)} :
    S ⊆ T ↔ ∀ i, row S i ⊆ row T i := by
  constructor
  · exact row_subset
  · intro h ⟨i, x⟩ hx
    exact mem_row.mp (h i (mem_row.mpr hx))

@[simp] theorem row_union {J L : ℕ} (S T : Finset (Coord J L)) (i : Fin J) :
    row (S ∪ T) i = row S i ∪ row T i := by ext x; simp

@[simp] theorem row_sdiff {J L : ℕ} (S T : Finset (Coord J L)) (i : Fin J) :
    row (S \ T) i = row S i \ row T i := by ext x; simp

@[simp] theorem row_inter {J L : ℕ} (S T : Finset (Coord J L)) (i : Fin J) :
    row (S ∩ T) i = row S i ∩ row T i := by ext x; simp

theorem join_union_compl {J L : ℕ} (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) :
    join I u ∪ join Iᶜ u = flat u := by
  ext ⟨i, x⟩
  simp only [Finset.mem_union, mem_join, Finset.mem_compl, mem_flat]
  tauto

theorem join_disjoint_compl {J L : ℕ} (I : Finset (Fin J))
    (u v : Fin J → Finset (Fin L)) : Disjoint (join I u) (join Iᶜ v) := by
  apply Finset.disjoint_left.mpr
  intro ⟨i, x⟩ hx hy
  exact (Finset.mem_compl.mp (mem_join.mp hy).1) (mem_join.mp hx).1

theorem join_subset {J L : ℕ} (I : Finset (Fin J)) {u v : Fin J → Finset (Fin L)}
    (h : ∀ i ∈ I, u i ⊆ v i) : join I u ⊆ join I v := by
  intro ⟨i, x⟩ hx
  obtain ⟨hi, hx⟩ := mem_join.mp hx
  exact mem_join.mpr ⟨hi, h i hi hx⟩

theorem join_card {J L : ℕ} (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) :
    (join I u).card = ∑ i ∈ I, (u i).card := Finset.card_sigma _ _

theorem join_card_of_balance {J L h : ℕ} (I : Finset (Fin J))
    (u : Fin J → Finset (Fin L)) (hu : ∀ i ∈ I, (u i).card = h) :
    (join I u).card = I.card * h := by
  rw [join_card]
  simp only [Finset.sum_congr rfl hu, Finset.sum_const, Nat.nsmul_eq_mul]

theorem flat_card_of_balance {J L h : ℕ} (u : Fin J → Finset (Fin L))
    (hu : ∀ i, (u i).card = h) : (flat u).card = J * h := by
  simpa only [flat, Finset.card_univ, Fintype.card_fin] using
    join_card_of_balance (Finset.univ : Finset (Fin J)) u (fun i _ => hu i)

theorem card_of_balanced_rows {J L h : ℕ} (S : Finset (Coord J L))
    (hS : ∀ i, (row S i).card = h) : S.card = J * h := by
  rw [← flat_row S]
  exact flat_card_of_balance _ hS

def prefixIndices (J k : ℕ) : Finset (Fin J) := univ.filter fun i => i.val < k

@[simp] theorem mem_prefixIndices {J k : ℕ} {i : Fin J} :
    i ∈ prefixIndices J k ↔ i.val < k := by simp [prefixIndices]

/-- Size arithmetic for the actual remaining Q blocks. The parameter I is
any set of completed blocks, including the initial segment used in reporting. -/
theorem forced_sizes {J L h : ℕ} (I : Finset (Fin J))
    (Q u : Fin J → Finset (Fin L)) (hQ : ∀ i, (Q i).card = 2 * h)
    (hu : ∀ i ∈ I, u i ⊆ Q i ∧ (u i).card = h) :
    (join Iᶜ Q).card =
      (J * h - (join I u).card) +
      (J * h - (join I (fun i => Q i \ u i)).card) := by
  have hU := join_card_of_balance I u (fun i hi => (hu i hi).2)
  have hV := join_card_of_balance (h := h) I (fun i => Q i \ u i) (fun i hi => by
    rw [Finset.card_sdiff_of_subset (hu i hi).1, hQ i, (hu i hi).2]
    omega)
  have hR := join_card_of_balance Iᶜ Q (fun i _ => hQ i)
  have hcompl : Iᶜ.card = J - I.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  rw [hU, hV, hR, hcompl, ← Nat.sub_mul]
  ring

end ThreeSum.BlockRows
