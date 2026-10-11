import Submission.ThreeSum.Subset
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card

/-!
# Executable positive-prefix reporting

The routine enumerates children of the current positive frontier and discards
zero counts. Its correctness interface asks for exact natural prefix counts;
the subset-transform identities supply those counts in the application.
No bound on the cost of obtaining a count is assumed or proved here.
-/

namespace ThreeSum.Reporting

open Finset
open scoped BigOperators

variable {ι α : Type*} [DecidableEq α]

def mass (I : Finset ι) (word : ι → List α) (weight : ι → ℕ)
    (k : ℕ) (pre : List α) : ℕ :=
  Subset.fiberMass I (fun i => (word i).take k) weight pre

theorem mass_pos_iff (I : Finset ι) (word : ι → List α) (weight : ι → ℕ)
    (k : ℕ) (pre : List α) :
    0 < mass I word weight k pre ↔
      ∃ i ∈ I, (word i).take k = pre ∧ 0 < weight i := by
  unfold mass Subset.fiberMass
  rw [Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  simp only [mem_filter]
  constructor
  · rintro ⟨i, ⟨hi, hpre⟩, hw⟩
    exact ⟨i, hi, hpre, hw⟩
  · rintro ⟨i, hi, hpre, hw⟩
    exact ⟨i, ⟨hi, hpre⟩, hw⟩

/-- Children are supplied in an explicit order; no choice-based ordering or
advice is used. `query` is the exact-count procedure's value interface. -/
def frontier (children : ℕ → List α) (query : ℕ → List α → ℕ) : ℕ → List (List α)
  | 0 => if 0 < query 0 [] then [[]] else []
  | k + 1 =>
      ((frontier children query k).flatMap fun pre =>
        (children k).map fun x => pre ++ [x]).filter fun pre => 0 < query (k + 1) pre

theorem frontier_lengths (children : ℕ → List α) (query : ℕ → List α → ℕ)
    (k : ℕ) : ∀ pre ∈ frontier children query k, pre.length = k := by
  induction k with
  | zero =>
      intro pre hp
      simp only [frontier] at hp
      split at hp
      · simpa using congrArg List.length (List.mem_singleton.mp hp)
      · cases hp
  | succ k ih =>
      intro pre hp
      obtain ⟨parent, hparent, hpre⟩ := List.mem_flatMap.mp (List.mem_filter.mp hp).1
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hpre
      simp [ih parent hparent]

theorem mem_frontier_iff (I : Finset ι) (word : ι → List α) (weight : ι → ℕ)
    (children : ℕ → List α) (query : ℕ → List α → ℕ) (J k : ℕ)
    (hlen : ∀ i ∈ I, (word i).length = J)
    (hchildren : ∀ i (hi : i ∈ I), ∀ j (hj : j < J),
      (word i)[j]'(by rw [hlen i hi]; exact hj) ∈ children j)
    (hquery : ∀ j ≤ J, ∀ pre, query j pre = mass I word weight j pre)
    (hk : k ≤ J) (pre : List α) :
    pre ∈ frontier children query k ↔ 0 < mass I word weight k pre := by
  induction k generalizing pre with
  | zero =>
      constructor
      · intro hp
        simp only [frontier] at hp
        split at hp
        · have heq := List.mem_singleton.mp hp
          subst pre
          simpa only [hquery 0 (by omega) []] using ‹0 < query 0 []›
        · cases hp
      · intro hm
        obtain ⟨i, hi, hpre, hw⟩ := (mass_pos_iff I word weight 0 pre).mp hm
        have heq : pre = [] := by simpa using hpre.symm
        rw [heq] at hm ⊢
        simp [frontier, hquery 0 (by omega) [], hm]
  | succ k ih =>
      constructor
      · intro hp
        have hpos := (List.mem_filter.mp hp).2
        simpa only [decide_eq_true_eq, hquery (k + 1) hk pre] using hpos
      · intro hm
        obtain ⟨i, hi, hpre, hw⟩ := (mass_pos_iff I word weight (k + 1) pre).mp hm
        have hj : k < J := by omega
        have hlenk : k < (word i).length := by rw [hlen i hi]; exact hj
        have hparentMass : 0 < mass I word weight k ((word i).take k) :=
          (mass_pos_iff I word weight k _).mpr ⟨i, hi, rfl, hw⟩
        have hparent := (ih (by omega) ((word i).take k)).mpr hparentMass
        apply List.mem_filter.mpr
        constructor
        · apply List.mem_flatMap.mpr
          refine ⟨(word i).take k, hparent, ?_⟩
          apply List.mem_map.mpr
          exact ⟨(word i)[k], hchildren i hi k hj,
            (List.take_append_getElem hlenk).trans hpre⟩
        · simpa only [decide_eq_true_eq, hquery (k + 1) hk pre] using hm

theorem frontier_nodup (children : ℕ → List α) (query : ℕ → List α → ℕ)
    (hc : ∀ k, (children k).Nodup) (k : ℕ) : (frontier children query k).Nodup := by
  induction k with
  | zero => unfold frontier; split <;> simp
  | succ k ih =>
      apply List.Nodup.filter
      apply List.nodup_flatMap.mpr
      constructor
      · intro pre hpre
        apply (hc k).map
        intro x y hxy
        exact List.singleton_injective (List.append_cancel_left hxy)
      · apply ih.imp
        intro p q hpq
        apply List.disjoint_left.mpr
        intro t ht hq
        obtain ⟨x, hx, hxt⟩ := List.mem_map.mp ht
        obtain ⟨y, hy, hyt⟩ := List.mem_map.mp hq
        have heq : p ++ [x] = q ++ [y] := hxt.trans hyt.symm
        exact hpq (List.append_inj_left' heq (by rfl))

/-- The list is precisely the positive fibers, so its size is bounded by
the root mass, even if different raw incidences have the same value. -/
theorem frontier_length_le_mass (I : Finset ι) (word : ι → List α) (weight : ι → ℕ)
    (children : ℕ → List α) (query : ℕ → List α → ℕ) (J k : ℕ)
    (hlen : ∀ i ∈ I, (word i).length = J)
    (hchildren : ∀ i (hi : i ∈ I), ∀ j (hj : j < J),
      (word i)[j]'(by rw [hlen i hi]; exact hj) ∈ children j)
    (hquery : ∀ j ≤ J, ∀ pre, query j pre = mass I word weight j pre)
    (hc : ∀ k, (children k).Nodup) (hk : k ≤ J) :
    (frontier children query k).length ≤ ∑ i ∈ I, weight i := by
  classical
  let labels := I.image fun i => (word i).take k
  have heq : (frontier children query k).toFinset =
      labels.filter (fun pre => 0 < mass I word weight k pre) := by
    ext pre
    rw [List.mem_toFinset, mem_frontier_iff I word weight children query J k
      hlen hchildren hquery hk, mem_filter]
    constructor
    · intro h
      obtain ⟨i, hi, hpre, hw⟩ := (mass_pos_iff I word weight k pre).mp h
      exact ⟨mem_image.mpr ⟨i, hi, hpre⟩, h⟩
    · exact And.right
  have hcount := Subset.positive_fibers_le_mass I labels
    (fun i => (word i).take k) weight (fun i hi => mem_image.mpr ⟨i, hi, rfl⟩)
  change (labels.filter (fun pre => 0 < mass I word weight k pre)).card ≤ _ at hcount
  rw [← heq, List.toFinset_card_of_nodup (frontier_nodup children query hc k)] at hcount
  exact hcount

/-- The actual candidate list formed at one level contains exactly one
entry per parent/child pair, before zero-count pruning. -/
theorem generated_candidates_length (parents : List (List α)) (children : List α) :
    (parents.flatMap fun pre => children.map fun x => pre ++ [x]).length =
      parents.length * children.length := by
  induction parents with
  | nil => simp
  | cons pre parents ih => simp [ih, Nat.add_mul, Nat.add_comm]

end ThreeSum.Reporting
