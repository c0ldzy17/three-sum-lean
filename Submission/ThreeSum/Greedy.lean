import Submission.ThreeSum.Cover
import Mathlib.Data.List.MinMax
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Ring
import Aesop

/-! # An executable finite greedy cover and its logarithmic length bound -/

namespace ThreeSum.Cover

open Finset
open scoped BigOperators

variable {Ω U : Type*} [Inhabited Ω] [DecidableEq U]

/-- Exhaustive finite search, breaking ties by the order of the input list. -/
def selectMap (maps : List Ω) (covers : Ω → U → Prop) [DecidableRel covers]
    (targets : Finset U) : Ω :=
  (maps.argmax fun ω => (targets.filter (covers ω)).card).getD default

theorem selectMap_mem (maps : List Ω) (hne : maps ≠ [])
    (covers : Ω → U → Prop) [DecidableRel covers] (targets : Finset U) :
    selectMap maps covers targets ∈ maps := by
  unfold selectMap
  cases h : maps.argmax (fun ω => (targets.filter (covers ω)).card) with
  | none => exact False.elim (hne (List.argmax_eq_none.mp h))
  | some ω =>
    simp only [Option.getD_some]
    exact List.argmax_mem (f := fun ω => (targets.filter (covers ω)).card)
      (by simpa only [Option.mem_def] using h)

theorem selectMap_max (maps : List Ω) (covers : Ω → U → Prop)
    [DecidableRel covers] (targets : Finset U) {ω : Ω} (hω : ω ∈ maps) :
    (targets.filter (covers ω)).card ≤
      (targets.filter (covers (selectMap maps covers targets))).card := by
  unfold selectMap
  cases h : maps.argmax (fun ω => (targets.filter (covers ω)).card) with
  | none => have := List.argmax_eq_none.mp h; simp_all
  | some v =>
    simp only [Option.getD_some]
    exact List.le_of_mem_argmax (f := fun ω => (targets.filter (covers ω)).card)
      hω (by simpa only [Option.mem_def] using h)

def greedyState (maps : List Ω) (covers : Ω → U → Prop) [DecidableRel covers]
    (targets : Finset U) : ℕ → Finset U
  | 0 => targets
  | t + 1 =>
    let old := greedyState maps covers targets t
    old.filter fun u => ¬ covers (selectMap maps covers old) u

def greedyChoices (maps : List Ω) (covers : Ω → U → Prop) [DecidableRel covers]
    (targets : Finset U) : ℕ → List Ω
  | 0 => []
  | t + 1 => greedyChoices maps covers targets t ++
      [selectMap maps covers (greedyState maps covers targets t)]

theorem greedyChoices_length (maps : List Ω) (covers : Ω → U → Prop)
    [DecidableRel covers] (targets : Finset U) (t : ℕ) :
    (greedyChoices maps covers targets t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [greedyChoices, ih]

theorem greedyState_spec (maps : List Ω) (covers : Ω → U → Prop)
    [DecidableRel covers] (targets : Finset U) (t : ℕ) (u : U) :
    u ∈ greedyState maps covers targets t ↔
      u ∈ targets ∧ ∀ ω ∈ greedyChoices maps covers targets t, ¬ covers ω u := by
  induction t with
  | zero => simp [greedyState, greedyChoices]
  | succ t ih =>
    simp only [greedyState, mem_filter, greedyChoices, List.mem_append, List.mem_singleton, ih]
    aesop

theorem greedyState_subset (maps : List Ω) (covers : Ω → U → Prop)
    [DecidableRel covers] (targets : Finset U) (t : ℕ) :
    greedyState maps covers targets t ⊆ targets := by
  intro u hu
  exact ((greedyState_spec maps covers targets t u).mp hu).1

theorem greedyState_contract [Fintype Ω] (maps : List Ω)
    (hall : ∀ ω, ω ∈ maps) (covers : Ω → U → Prop) [DecidableRel covers]
    (targets : Finset U) (a : ℕ) (ha : 0 < a)
    (hfrequency : ∀ u ∈ targets,
      Fintype.card Ω ≤ a * (univ.filter fun ω => covers ω u).card) (t : ℕ) :
    a * (greedyState maps covers targets (t + 1)).card ≤
      (a - 1) * (greedyState maps covers targets t).card := by
  let old := greedyState maps covers targets t
  have hfreq : ∀ u ∈ old,
      Fintype.card Ω ≤ a * (univ.filter fun ω => covers ω u).card := by
    intro u hu
    exact hfrequency u (greedyState_subset maps covers targets t hu)
  obtain ⟨ω, hω⟩ := exists_good_cover old covers a hfreq
  have hbest := selectMap_max maps covers old (hall ω)
  exact survivor_step old (covers (selectMap maps covers old)) a ha
    (hω.trans (Nat.mul_le_mul_left a hbest))

/-- The exact geometric recurrence, with all denominators cleared. -/
theorem greedyState_geometric [Fintype Ω] (maps : List Ω)
    (hall : ∀ ω, ω ∈ maps) (covers : Ω → U → Prop) [DecidableRel covers]
    (targets : Finset U) (a : ℕ) (ha : 0 < a)
    (hfrequency : ∀ u ∈ targets,
      Fintype.card Ω ≤ a * (univ.filter fun ω => covers ω u).card) (t : ℕ) :
    a ^ t * (greedyState maps covers targets t).card ≤ (a - 1) ^ t * targets.card := by
  induction t with
  | zero => simp [greedyState]
  | succ t ih =>
    have hs := greedyState_contract maps hall covers targets a ha hfrequency t
    calc
      a ^ (t + 1) * (greedyState maps covers targets (t + 1)).card =
          a ^ t * (a * (greedyState maps covers targets (t + 1)).card) := by ring
      _ ≤ a ^ t * ((a - 1) * (greedyState maps covers targets t).card) :=
        Nat.mul_le_mul_left _ hs
      _ = (a - 1) * (a ^ t * (greedyState maps covers targets t).card) := by ring
      _ ≤ (a - 1) * ((a - 1) ^ t * targets.card) := Nat.mul_le_mul_left _ ih
      _ = (a - 1) ^ (t + 1) * targets.card := by ring

/-- Each block of a iterations shrinks the geometric upper bound by 1/2. -/
theorem half_power_bound (a : ℕ) (ha : 0 < a) : 2 * (a - 1) ^ a ≤ a ^ a := by
  have hae : a - 1 + 1 = a := by omega
  have h := pow_add_mul_le_add_pow (a := a - 1) (b := 1)
    (Nat.zero_le _) (Nat.zero_le _) a
  simp only [hae, mul_one] at h
  have hpow : (a - 1) ^ a = (a - 1) ^ (a - 1) * (a - 1) := by
    calc
      (a - 1) ^ a = (a - 1) ^ ((a - 1) + 1) := congrArg ((a - 1) ^ ·) hae.symm
      _ = (a - 1) ^ (a - 1) * (a - 1) := pow_succ _ _
  have hm := Nat.mul_le_mul_left ((a - 1) ^ (a - 1)) (Nat.sub_le a 1)
  nlinarith

theorem greedyState_blocks [Fintype Ω] (maps : List Ω)
    (hall : ∀ ω, ω ∈ maps) (covers : Ω → U → Prop) [DecidableRel covers]
    (targets : Finset U) (a : ℕ) (ha : 1 < a)
    (hfrequency : ∀ u ∈ targets,
      Fintype.card Ω ≤ a * (univ.filter fun ω => covers ω u).card) (k : ℕ) :
    2 ^ k * (greedyState maps covers targets (a * k)).card ≤ targets.card := by
  have ha0 : 0 < a := by omega
  have hgeom := greedyState_geometric maps hall covers targets a ha0 hfrequency (a * k)
  have hhalf := Nat.pow_le_pow_left (half_power_bound a ha0) k
  simp only [mul_pow, ← pow_mul] at hhalf
  have hpos : 0 < (a - 1) ^ (a * k) := Nat.pow_pos (by omega)
  have hm := Nat.mul_le_mul_right (greedyState maps covers targets (a * k)).card hhalf
  nlinarith

/-- The implemented greedy list covers every target within
a*(floor(log2(number of targets))+1) maps. -/
theorem greedy_cover [Fintype Ω] (maps : List Ω)
    (hall : ∀ ω, ω ∈ maps) (covers : Ω → U → Prop) [DecidableRel covers]
    (targets : Finset U) (a : ℕ) (ha : 1 < a)
    (hfrequency : ∀ u ∈ targets,
      Fintype.card Ω ≤ a * (univ.filter fun ω => covers ω u).card) :
    ∀ u ∈ targets,
      ∃ ω ∈ greedyChoices maps covers targets (a * (Nat.log2 targets.card + 1)),
        covers ω u := by
  have hblocks := greedyState_blocks maps hall covers targets a ha hfrequency
    (Nat.log2 targets.card + 1)
  have hlog := Nat.lt_log2_self (n := targets.card)
  have hzero : (greedyState maps covers targets (a * (Nat.log2 targets.card + 1))).card = 0 := by
    by_contra hn
    have hp : 1 ≤ (greedyState maps covers targets (a * (Nat.log2 targets.card + 1))).card := by omega
    have hm := Nat.mul_le_mul_left (2 ^ (Nat.log2 targets.card + 1)) hp
    nlinarith
  intro u hu
  by_contra! hnone
  have hmem := (greedyState_spec maps covers targets _ u).mpr ⟨hu, hnone⟩
  simpa [card_eq_zero.mp hzero] using hmem

end ThreeSum.Cover
