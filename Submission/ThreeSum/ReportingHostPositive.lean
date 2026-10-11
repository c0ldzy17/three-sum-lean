import Submission.ThreeSum.LightReportingCatalogExpand
import Submission.ThreeSum.ReportingHostFrontier

/-!
# Exact next-frontier order and raw-mass charges for the actual expansion

Gathering the stably selected child positions produces exactly the recursive
reporting frontier, including its original order and retained multiplicity.
-/

namespace ThreeSum.ReportingHostPositive

open Light Finset ThreeSum.SubsetAddress
open BlockForced StoredReporting GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open LightBlockChildrenIndexed ReportingHostFrontier
open scoped BigOperators

set_option linter.unusedSectionVars false

theorem map_range_getD {α : Type*} (xs : List α) (fallback : α) :
    (List.range xs.length).map (fun i => xs[i]?.getD fallback) = xs := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp only [List.getElem_map,List.getElem_range,List.getElem?_eq_getElem hi',Option.getD_some]

theorem selected_map {α : Type*} (xs : List α) (fallback : α) (q : α → ℕ) :
    (LightReportingFilter.selected (fun i => q (xs[i]?.getD fallback)) xs.length).map
        (fun i => xs[i]?.getD fallback) = xs.filter (fun x => 0 < q x) := by
  change ((List.range xs.length).filter
    ((fun x : α => decide (0 < q x)) ∘ (fun i => xs[i]?.getD fallback))).map
      (fun i => xs[i]?.getD fallback) = _
  rw [← List.filter_map,map_range_getD]

theorem frontier_positive {α : Type*} (children : ℕ → List α) (query : ℕ → List α → ℕ)
    {k : ℕ} {pre : List α} (hp : pre ∈ Reporting.frontier children query k) :
    0 < query k pre := by
  cases k with
  | zero =>
      simp only [Reporting.frontier] at hp
      split at hp
      · have he : pre = [] := List.mem_singleton.mp hp
        simpa only [he] using ‹0 < query 0 []›
      · cases hp
  | succ k =>
      exact of_decide_eq_true (List.mem_filter.mp hp).2

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def positiveChildren {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k < J) :
    List (List (Finset (Fin (512*h)))) :=
  (LightReportingFilter.selected (fun i => prefixQuery I w (k+1) (childAt w.2.2 pre hk i))
    (groupSize h)).map (childAt w.2.2 pre hk)

theorem positiveChildren_eq_filter {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k < J) :
    positiveChildren I w pre hk =
      (childPrefixes w.2.2 pre hk).filter (fun next => 0 < prefixQuery I w (k+1) next) := by
  unfold positiveChildren
  change (LightReportingFilter.selected
    (fun i => prefixQuery I w (k+1) ((childPrefixes w.2.2 pre hk)[i]?.getD [])) (groupSize h)).map
      (fun i => (childPrefixes w.2.2 pre hk)[i]?.getD []) = _
  rw [← childPrefixes_length w.2.2 pre hk]
  exact selected_map (childPrefixes w.2.2 pre hk) [] (prefixQuery I w (k+1))

theorem positiveChildren_length_le {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k < J) :
    (positiveChildren I w pre hk).length ≤ groupSize h := by
  simpa only [positiveChildren,List.length_map] using
    LightReportingFilter.selected_length_le (fun i => prefixQuery I w (k+1) (childAt w.2.2 pre hk i)) (groupSize h)

theorem frontier_valid {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (hk : k ≤ J) {pre : List (Finset (Fin (512*h)))}
    (hp : pre ∈ ReportingHostFrontier.frontier I w k) : ValidPrefix w.2.2 k pre :=
  positivePrefix_valid I w pre hk (frontier_positive _ _ hp)

theorem frontier_step {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (hk : k < J) :
    ReportingHostFrontier.frontier I w (k+1) =
      (ReportingHostFrontier.frontier I w k).flatMap (fun pre => positiveChildren I w pre hk) := by
  simp only [ReportingHostFrontier.frontier,Reporting.frontier,List.filter_flatMap,
    positiveChildren_eq_filter,ReportingHostFrontier.children,dif_pos hk,childPrefixes]

def parentWork {h J : ℕ} (I : Finset (RawItem h J α β γ)) (k t : ℕ) : ℕ :=
  ∑ w : Wanted h J α, (ReportingHostFrontier.frontier I w k).length*
    LightReportingCatalogExpand.time h J k t

theorem parentWork_le {h J k t : ℕ} (I : Finset (RawItem h J α β γ)) (hk : k < J)
    (ht : t ≤ LightBlockQuery.residualSize h J (k+1)+1) :
    parentWork I k t ≤ I.card*
      (25000*(LightBlockQuery.width h J+1)^3*
        (LightSparseQuery.queryItems (LightBlockQuery.residualSize h J (k+1)) t+1)*(groupSize h+1)) := by
  rw [parentWork,← Finset.sum_mul]
  exact Nat.mul_le_mul (total_frontier_length_le_raw_card I (Nat.le_of_lt hk))
    (LightReportingCatalogExpand.time_bound hk ht)

end ThreeSum.ReportingHostPositive
