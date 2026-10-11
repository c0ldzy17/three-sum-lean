import Submission.ThreeSum.IndexedGreedy
import Submission.ThreeSum.LightCoverScores
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! # Boolean-array semantics of the already specified finite greedy schedule -/

namespace ThreeSum.BooleanGreedy

open Finset
open scoped BigOperators

def covers (matrix : ℕ → ℕ → ℕ) (row col : ℕ) : Prop := matrix row col = 1

instance (matrix : ℕ → ℕ → ℕ) : DecidableRel (covers matrix) :=
  fun _ _ => inferInstanceAs (Decidable (_ = _))

def state (matrix : ℕ → ℕ → ℕ) (rows cols t : ℕ) : Finset ℕ :=
  Cover.greedyState (List.range rows) (covers matrix) (range cols) t

def active (matrix : ℕ → ℕ → ℕ) (rows cols t j : ℕ) : ℕ :=
  if j ∈ state matrix rows cols t then 1 else 0

def choice (matrix : ℕ → ℕ → ℕ) (rows cols t : ℕ) : ℕ :=
  Cover.selectMap (List.range rows) (covers matrix) (state matrix rows cols t)

def choices (matrix : ℕ → ℕ → ℕ) (rows cols t : ℕ) : List ℕ :=
  Cover.greedyChoices (List.range rows) (covers matrix) (range cols) t

theorem state_subset (matrix : ℕ → ℕ → ℕ) (rows cols t : ℕ) :
    state matrix rows cols t ⊆ range cols := Cover.greedyState_subset ..

theorem active_le (matrix : ℕ → ℕ → ℕ) (rows cols t j : ℕ) :
    active matrix rows cols t j ≤ 1 := by unfold active; split <;> omega

theorem active_zero {matrix : ℕ → ℕ → ℕ} {rows cols j : ℕ} (hj : j < cols) :
    active matrix rows cols 0 j = 1 := by simp [active,state,Cover.greedyState,hj]

theorem score_eq_card {matrix : ℕ → ℕ → ℕ} {rows cols row : ℕ}
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1)
    (hrow : row < rows) (t : ℕ) :
    LightCoverScores.score matrix (active matrix rows cols t) cols row =
      ((state matrix rows cols t).filter (covers matrix row)).card := by
  have hset : ((range cols).filter fun j => j ∈ state matrix rows cols t ∧ covers matrix row j) =
      (state matrix rows cols t).filter (covers matrix row) := by
    ext j
    simp only [mem_filter]
    constructor
    · rintro ⟨_,hmem,hcover⟩
      exact ⟨hmem,hcover⟩
    · rintro ⟨hmem,hcover⟩
      exact ⟨state_subset matrix rows cols t hmem,hmem,hcover⟩
  rw [← hset,Finset.card_filter]
  unfold LightCoverScores.score LightBooleanDot.dot
  apply sum_congr rfl
  intro j hj
  have hm := hmatrix row hrow j (mem_range.mp hj)
  by_cases ha : j ∈ state matrix rows cols t <;> by_cases hc : matrix row j = 1
  · simp [active,ha,covers,hc]
  · have hz : matrix row j = 0 := by omega
    simp [active,ha,covers,hc,hz]
  · simp [active,ha,covers,hc]
  · simp [active,ha,covers,hc]

theorem choice_lt {matrix : ℕ → ℕ → ℕ} {rows cols : ℕ} (hrows : 0 < rows) (t : ℕ) :
    choice matrix rows cols t < rows := by
  apply List.mem_range.mp
  exact Cover.selectMap_mem _ (by simpa using hrows.ne') _ _

theorem choice_eq_least {matrix : ℕ → ℕ → ℕ} {rows cols : ℕ}
    (hrows : 0 < rows)
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1) (t : ℕ) :
    choice matrix rows cols t =
      LightMinimum.least (fun i => -(LightCoverScores.score matrix (active matrix rows cols t) cols i : ℤ)) rows := by
  have hf : ∀ i < rows,
      -(((state matrix rows cols t).filter (covers matrix i)).card : ℤ) =
      -(LightCoverScores.score matrix (active matrix rows cols t) cols i : ℤ) := by
    intro i hi
    rw [score_eq_card hmatrix hi t]
  rw [choice,IndexedGreedy.selectMap_indices _ _ hrows]
  have hcongr (f g : ℕ → ℤ) : ∀ n, (∀ i < n, f i = g i) →
      LightMinimum.least f n = LightMinimum.least g n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro he
      cases n with
      | zero => simp [LightMinimum.least]
      | succ n =>
        have hb := LightMinimum.least_lt g (by omega : 0 < n+1)
        have hi := ih (fun i hi => he i (by omega))
        change (if f (n+1) < f (LightMinimum.least f (n+1)) then n+1 else _) = _
        rw [hi,he (n+1) (by omega),he _ (by omega)]
        rfl
  exact hcongr _ _ rows hf

theorem active_succ {matrix : ℕ → ℕ → ℕ} {rows cols : ℕ}
    (hrows : 0 < rows)
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1) (t j : ℕ) (hj : j < cols) :
    active matrix rows cols (t+1) j =
      active matrix rows cols t j * (1-matrix (choice matrix rows cols t) j) := by
  have hm := hmatrix _ (choice_lt (matrix := matrix) (cols := cols) hrows t) j hj
  have hmem : j ∈ state matrix rows cols (t+1) ↔
      j ∈ state matrix rows cols t ∧ ¬covers matrix (choice matrix rows cols t) j :=
    Finset.mem_filter
  by_cases ha : j ∈ state matrix rows cols t <;>
    by_cases hc : matrix (choice matrix rows cols t) j = 1
  · have hn : j ∉ state matrix rows cols (t+1) := fun h => (hmem.mp h).2 hc
    simp only [active,if_neg hn,if_pos ha,hc,Nat.sub_self,Nat.mul_zero]
  · have hz : matrix (choice matrix rows cols t) j = 0 := by omega
    have hn : j ∈ state matrix rows cols (t+1) := hmem.mpr ⟨ha,hc⟩
    simp only [active,if_pos hn,if_pos ha,hz,Nat.sub_zero,Nat.mul_one]
  · have hn : j ∉ state matrix rows cols (t+1) := fun h => ha (hmem.mp h).1
    simp only [active,if_neg hn,if_neg ha,Nat.zero_mul]
  · have hn : j ∉ state matrix rows cols (t+1) := fun h => ha (hmem.mp h).1
    simp only [active,if_neg hn,if_neg ha,Nat.zero_mul]

theorem choices_length (matrix : ℕ → ℕ → ℕ) (rows cols t : ℕ) :
    (choices matrix rows cols t).length = t := Cover.greedyChoices_length ..

theorem choices_succ (matrix : ℕ → ℕ → ℕ) (rows cols t : ℕ) :
    choices matrix rows cols (t+1) = choices matrix rows cols t ++ [choice matrix rows cols t] := rfl

end ThreeSum.BooleanGreedy
