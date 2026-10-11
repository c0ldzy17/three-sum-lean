import Submission.ThreeSum.ReportingHostPositive

/-! # Exact ordered accumulation for the actual multi-parent reporting loop -/

namespace ThreeSum.ReportingHostPositiveBatch

open Finset BlockForced StoredReporting GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostPositive

set_option linter.unusedSectionVars false

theorem flatMap_length_le {α β : Type*} (xs : List α) (f : α → List β) (G : ℕ)
    (hf : ∀ x ∈ xs, (f x).length ≤ G) : (xs.flatMap f).length ≤ xs.length*G := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := hf x (by simp)
      have ht := ih (fun y hy => hf y (by simp [hy]))
      simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def parentAt {h : ℕ} (pres : List (List (Finset (Fin (512*h))))) (i : ℕ) := pres[i]?.getD []

theorem parentAt_eq_get {h i : ℕ} (pres : List (List (Finset (Fin (512*h))))) (hi : i < pres.length) :
    parentAt pres i = pres[i] := by simp only [parentAt,List.getElem?_eq_getElem hi,Option.getD_some]

def through {h J k : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (pres : List (List (Finset (Fin (512*h))))) (hk : k < J) (j : ℕ) :
    List (List (Finset (Fin (512*h)))) :=
  (pres.take j).flatMap (fun pre => positiveChildren I w pre hk)

theorem through_zero {h J k : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (pres : List (List (Finset (Fin (512*h))))) (hk : k < J) : through I w pres hk 0 = [] := by
  simp [through]

theorem through_succ {h J k j : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (pres : List (List (Finset (Fin (512*h))))) (hk : k < J) (hj : j < pres.length) :
    through I w pres hk (j+1) = through I w pres hk j ++ positiveChildren I w (parentAt pres j) hk := by
  rw [through,← List.take_append_getElem hj,List.flatMap_append,List.flatMap_singleton,parentAt_eq_get pres hj]
  rfl

theorem through_length_le {h J k j : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (pres : List (List (Finset (Fin (512*h))))) (hk : k < J) :
    (through I w pres hk j).length ≤ j*groupSize h := by
  exact (flatMap_length_le (pres.take j) (fun pre => positiveChildren I w pre hk) _
    (fun pre _ => positiveChildren_length_le I w pre hk)).trans
      (Nat.mul_le_mul_right _ (by simp only [List.length_take]; exact Nat.min_le_left _ _))

theorem through_all {h J k : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (pres : List (List (Finset (Fin (512*h))))) (hk : k < J) :
    through I w pres hk pres.length = pres.flatMap (fun pre => positiveChildren I w pre hk) := by
  simp only [through,List.take_length]

theorem parentAt_valid {h J k i : ℕ} (q : GlobalOutput h J)
    (pres : List (List (Finset (Fin (512*h))))) (hp : ∀ pre ∈ pres, ValidPrefix q k pre)
    (hi : i < pres.length) : ValidPrefix q k (parentAt pres i) := by
  rw [parentAt_eq_get pres hi]
  exact hp _ (List.getElem_mem hi)

end ThreeSum.ReportingHostPositiveBatch
