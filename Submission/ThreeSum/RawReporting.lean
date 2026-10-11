import Submission.ThreeSum.RawIncidences
import Submission.ThreeSum.Reporting
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Finset.Sort

/-!
# Positive-prefix reporting for concrete guarded incidences

The band triple is fixed by the input index sets and offset passed to this
module. Its wanted queries retain the original A index, signed lift and
full output tuple, including every chosen-map occurrence. Children are
the balanced subsets of the next output block, in deterministic colex order.
-/

namespace ThreeSum.RawReporting

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences

private def colexEmbedding (L : ℕ) : Finset (Fin L) ↪ Colex (Finset (Fin L)) :=
  ⟨toColex, fun _ _ h => h⟩

/-- A deterministic ordering of exactly the balanced child subsets. -/
def childList {L : ℕ} (Q : Finset (Fin L)) (h : ℕ) : List (Finset (Fin L)) :=
  (((Q.powersetCard h).map (colexEmbedding L)).sort (· ≤ ·)).map ofColex

theorem mem_childList {L h : ℕ} {Q S : Finset (Fin L)} :
    S ∈ childList Q h ↔ S ∈ Q.powersetCard h := by
  constructor
  · intro hs
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
    obtain ⟨s, hsLayer, rfl⟩ := Finset.mem_map.mp ((Finset.mem_sort _).mp hc)
    exact hsLayer
  · intro hs
    apply List.mem_map.mpr
    refine ⟨toColex S, ?_, rfl⟩
    apply (Finset.mem_sort _).mpr
    exact Finset.mem_map.mpr ⟨S, hs, rfl⟩

theorem childList_nodup {L : ℕ} (Q : Finset (Fin L)) (h : ℕ) :
    (childList Q h).Nodup :=
  (Finset.sort_nodup _ _).map (fun _ _ h => h)

theorem childList_length {L : ℕ} (Q : Finset (Fin L)) (h : ℕ) :
    (childList Q h).length = Q.card.choose h := by
  simp only [childList, List.length_map, Finset.length_sort,
    Finset.card_map, Finset.card_powersetCard]

def children {h J : ℕ} (q : GlobalOutput h J) (k : ℕ) : List (Finset (Fin (512 * h))) :=
  if hk : k < J then childList (q ⟨k, hk⟩).2.val h else []

theorem children_nodup {h J : ℕ} (q : GlobalOutput h J) (k : ℕ) :
    (children q k).Nodup := by
  unfold children
  split
  · exact childList_nodup _ _
  · exact List.nodup_nil

theorem children_length {h J k : ℕ} (q : GlobalOutput h J) (hk : k < J) :
    (children q k).length = groupSize h := by
  rw [children, dif_pos hk, childList_length]
  have hc := LayerCounts.mem_vertices.mp (q ⟨k, hk⟩).2.property
  simp only [hc, groupSize]

def partitionWord {h J : ℕ} (t : ChoiceTuple h J) : List (Finset (Fin (512 * h))) :=
  List.ofFn fun i => (edge (t i)).val.1

theorem partitionWord_length {h J : ℕ} (t : ChoiceTuple h J) : (partitionWord t).length = J :=
  List.length_ofFn

instance outputBlockDecidableEq (h : ℕ) : DecidableEq (OutputBlock h) := inferInstance
instance globalOutputDecidableEq (h J : ℕ) : DecidableEq (GlobalOutput h J) :=
  Fintype.decidablePiFintype

abbrev Wanted (h J : ℕ) (α : Type*) := α × (Fin 3 × GlobalOutput h J)

instance wantedDecidableEq (h J : ℕ) (α : Type*) [DecidableEq α] :
    DecidableEq (Wanted h J α) := inferInstance

def wantedOf {h J : ℕ} {α β γ : Type*} (r : RawItem h J α β γ) : Wanted h J α :=
  (r.1.1, (r.2.2, tupleOutput r.2.1))

def word {h J : ℕ} {α β γ : Type*} (r : RawItem h J α β γ) := partitionWord r.2.1

section FixedBand

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def domain {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) :=
  I.filter fun r => wantedOf r = w

def prefixQuery {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (k : ℕ) (pre : List (Finset (Fin (512 * h)))) : ℕ :=
  Reporting.mass (domain I w) word (fun _ => 1) k pre

def frontier {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (k : ℕ) : List (List (Finset (Fin (512 * h)))) :=
  Reporting.frontier (children w.2.2) (prefixQuery I w) k

theorem word_children {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (r : RawItem h J α β γ) (hr : r ∈ domain I w) (j : ℕ) (hj : j < J) :
    (word r)[j]'(by rw [word, partitionWord_length]; exact hj) ∈ children w.2.2 j := by
  have hw := (Finset.mem_filter.mp hr).2
  have hq : tupleOutput r.2.1 = w.2.2 := congrArg (fun x => x.2.2) hw
  have hi := congrFun hq ⟨j, hj⟩
  have hQ : output (edge (r.2.1 ⟨j, hj⟩)) = (w.2.2 ⟨j, hj⟩).2.val :=
    congrArg (fun x => x.2.val) hi
  rw [children, dif_pos hj]
  apply mem_childList.mpr
  simp only [word, partitionWord, List.getElem_ofFn]
  apply Finset.mem_powersetCard.mpr
  refine ⟨?_, (edge_data _).1⟩
  rw [← hQ]
  exact Finset.subset_union_left

theorem mem_frontier_iff {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (hk : k ≤ J) (pre : List (Finset (Fin (512 * h)))) :
    pre ∈ frontier I w k ↔ ∃ r ∈ I, wantedOf r = w ∧ (word r).take k = pre := by
  rw [frontier, Reporting.mem_frontier_iff (domain I w) word (fun _ => 1)
    (children w.2.2) (prefixQuery I w) J k
    (fun r _ => partitionWord_length r.2.1) (word_children I w)
    (fun _ _ _ => rfl) hk]
  rw [Reporting.mass_pos_iff]
  simp only [domain, Finset.mem_filter, Nat.lt_one_iff, and_true]
  constructor
  · rintro ⟨r, ⟨hr, hw⟩, hp⟩
    exact ⟨r, hr, hw, hp⟩
  · rintro ⟨r, hr, hw, hp⟩
    exact ⟨r, ⟨hr, hw⟩, hp⟩

theorem frontier_length_le_domain {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (hk : k ≤ J) : (frontier I w k).length ≤ (domain I w).card := by
  have h := Reporting.frontier_length_le_mass (domain I w) word (fun _ => 1)
    (children w.2.2) (prefixQuery I w) J k
    (fun r _ => partitionWord_length r.2.1) (word_children I w)
    (fun _ _ _ => rfl) (children_nodup w.2.2) hk
  simpa only [frontier, Finset.sum_const, smul_eq_mul, mul_one] using h

/-- Summing all wanted-query frontiers still costs at most the original raw
mass at a fixed depth: wanted labels form disjoint raw fibers. -/
theorem total_frontier_length_le_raw_card {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (hk : k ≤ J) : (∑ w : Wanted h J α, (frontier I w k).length) ≤ I.card := by
  calc
    _ ≤ ∑ w : Wanted h J α, (domain I w).card := by
      apply Finset.sum_le_sum
      intro w _
      exact frontier_length_le_domain I w hk
    _ = _ := by
      symm
      exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)

theorem raw_word_reported {h J : ℕ} (I : Finset (RawItem h J α β γ))
    (r : RawItem h J α β γ) (hr : r ∈ I) :
    word r ∈ frontier I (wantedOf r) J := by
  apply (mem_frontier_iff I (wantedOf r) le_rfl (word r)).mpr
  refine ⟨r, hr, rfl, ?_⟩
  simpa only [word, partitionWord_length] using (List.take_length (l := word r))

theorem true_original_reported {h J : ℕ} {P d : ℤ}
    (T : Finset (Original α β γ)) (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ)
    (hh : 0 < h) (hP : 0 < P) (t : Original α β γ) (ht : t ∈ T)
    (he : difference a b c t = 0) :
    ∃ r ∈ rawOn h J P d T a b c, r.1 = t ∧
      word r ∈ frontier (rawOn h J P d T a b c) (wantedOf r) J := by
  obtain ⟨r, hr, hrt⟩ := raw_true_triple_complete hh hP ht he
  exact ⟨r, hr, hrt, raw_word_reported _ r hr⟩

theorem total_frontier_length_le_rawMass {h J k : ℕ} (P d : ℤ)
    (T : Finset (Original α β γ)) (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (hk : k ≤ J) :
    (∑ w : Wanted h J α, (frontier (rawOn h J P d T a b c) w k).length) ≤
      rawMass h J P d T a b c :=
  total_frontier_length_le_raw_card _ hk

end FixedBand

end ThreeSum.RawReporting
