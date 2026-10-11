import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Image
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# A finite, deterministic three-color reduction

The family below enumerates two positions of the binary representation of an
array index and all 81 maps from their four patterns to three colors.  Its
parameter count is exactly `81 * d^2`.  In particular it never enumerates all
three-colorings of the input.  The final equivalence allows repeated input
values and deduplicates each color class into a finite set.
-/

namespace ThreeSum.Coloring

variable {α : Type*}

private theorem exists_coordinate_ne {s t : α → Bool} (h : s ≠ t) :
    ∃ i, s i ≠ t i := by
  classical
  by_contra hn
  push Not at hn
  exact h (funext hn)

/-- Two coordinates suffice to distinguish any three different binary words. -/
theorem two_coordinates_separate {s t u : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    ∃ i j, (s i, s j) ≠ (t i, t j) ∧
      (s i, s j) ≠ (u i, u j) ∧ (t i, t j) ≠ (u i, u j) := by
  obtain ⟨i, hi⟩ := exists_coordinate_ne hst
  have hui : u i = s i ∨ u i = t i := by
    cases hs : s i <;> cases ht : t i <;> cases hu : u i <;> simp_all
  rcases hui with hui | hui
  · obtain ⟨j, hj⟩ := exists_coordinate_ne hsu
    refine ⟨i, j, ?_, ?_, ?_⟩
    · exact fun he => hi (congrArg Prod.fst he)
    · exact fun he => hj (congrArg Prod.snd he)
    · intro he
      exact hi ((congrArg Prod.fst he).trans hui).symm
  · obtain ⟨j, hj⟩ := exists_coordinate_ne htu
    refine ⟨i, j, ?_, ?_, ?_⟩
    · exact fun he => hi (congrArg Prod.fst he)
    · intro he
      exact hi ((congrArg Prod.fst he).trans hui)
    · exact fun he => hj (congrArg Prod.snd he)

/-- An explicitly enumerable parameter space: two coordinates and an 81-entry
choice of a color map. -/
abbrev Parameter (d : ℕ) := (Fin d × Fin d) × ((Bool × Bool) → Fin 3)

def applyColor {d : ℕ} (p : Parameter d) (word : Fin d → Bool) : Fin 3 :=
  p.2 (word p.1.1, word p.1.2)

theorem parameter_card (d : ℕ) : Fintype.card (Parameter d) = 81 * d ^ 2 := by
  simp [Parameter, Fintype.card_fun, pow_two, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc]

/-- Enumeration of the small parameter space separates the words in the
specified order, so no permutation of the three-set equation is needed. -/
theorem exists_separating_parameter {d : ℕ} {s t u : Fin d → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    ∃ p : Parameter d, applyColor p s = 0 ∧ applyColor p t = 1 ∧
      applyColor p u = 2 := by
  obtain ⟨i, j, hst', hsu', htu'⟩ := two_coordinates_separate hst hsu htu
  let f : (Bool × Bool) → Fin 3 := fun x =>
    if x = (s i, s j) then 0 else if x = (t i, t j) then 1 else 2
  refine ⟨((i, j), f), ?_, ?_, ?_⟩
  · simp [applyColor, f]
  · simp [applyColor, f, Ne.symm hst']
  · simp [applyColor, f, Ne.symm hsu', Ne.symm htu']

/-- The minimum binary width needed for indices from zero through `n-1`. -/
def indexWidth (n : ℕ) : ℕ := Nat.size (n - 1)

def indexWord {n : ℕ} (i : Fin n) : Fin (indexWidth n) → Bool :=
  fun j => i.val.testBit j.val

theorem index_lt_pow_width {n : ℕ} (i : Fin n) : i.val < 2 ^ indexWidth n := by
  exact (show i.val ≤ n - 1 by omega).trans_lt (Nat.lt_size_self (n - 1))

theorem indexWord_injective (n : ℕ) : Function.Injective (@indexWord n) := by
  intro i j hij
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < indexWidth n
  · exact congrFun hij ⟨k, hk⟩
  · have hp : 2 ^ indexWidth n ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt ((index_lt_pow_width i).trans_le hp),
      Nat.testBit_eq_false_of_lt ((index_lt_pow_width j).trans_le hp)]

/-- The width is bounded by any binary length that can hold all `n` indices. -/
theorem indexWidth_le {n d : ℕ} (hn : n ≤ 2 ^ d) : indexWidth n ≤ d := by
  by_cases hzero : n = 0
  · simp [indexWidth, hzero]
  · exact Nat.size_le.mpr (by omega)

theorem indexWidth_le_log2 (n : ℕ) : indexWidth n ≤ n.log2 + 1 :=
  indexWidth_le Nat.lt_log2_self.le

def colorIndex {n : ℕ} (p : Parameter (indexWidth n)) (i : Fin n) : Fin 3 :=
  applyColor p (indexWord i)

/-- The actual family is an image of the small, explicitly enumerable
parameter domain. Duplicate colorings can be discarded. -/
def family (n : ℕ) : Finset (Fin n → Fin 3) :=
  Finset.univ.image (fun p : Parameter (indexWidth n) => colorIndex p)

theorem family_card_bound (n : ℕ) :
    (family n).card ≤ 81 * (indexWidth n) ^ 2 := by
  calc
    (family n).card ≤ Fintype.card (Parameter (indexWidth n)) :=
      Finset.card_image_le
    _ = _ := parameter_card _

/-- An exact logarithmic bound, valid also for input sizes zero and one. -/
theorem parameter_card_log_bound (n : ℕ) :
    Fintype.card (Parameter (indexWidth n)) ≤ 81 * (n.log2 + 1) ^ 2 := by
  rw [parameter_card]
  exact Nat.mul_le_mul_left 81 (Nat.pow_le_pow_left (indexWidth_le_log2 n) 2)

theorem family_card_log_bound (n : ℕ) :
    (family n).card ≤ 81 * (n.log2 + 1) ^ 2 := by
  exact (family_card_bound n).trans
    (Nat.mul_le_mul_left 81 (Nat.pow_le_pow_left (indexWidth_le_log2 n) 2))

theorem family_separates {n : ℕ} {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ c ∈ family n, c i = 0 ∧ c j = 1 ∧ c k = 2 := by
  obtain ⟨p, hp⟩ := exists_separating_parameter
    (fun h => hij (indexWord_injective n h)) (fun h => hik (indexWord_injective n h))
    (fun h => hjk (indexWord_injective n h))
  exact ⟨colorIndex p, Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩, hp⟩

/-- Values are deduplicated inside each class, retaining original index
witnesses through image membership. -/
def values {n : ℕ} (x : Fin n → ℤ) (c : Fin n → Fin 3) (color : Fin 3) :
    Finset ℤ :=
  (Finset.univ.filter (fun i => c i = color)).image x

def negValues {n : ℕ} (x : Fin n → ℤ) (c : Fin n → Fin 3) : Finset ℤ :=
  (values x c 2).image (fun z => -z)

theorem mem_values {n : ℕ} (x : Fin n → ℤ) (c : Fin n → Fin 3)
    (color : Fin 3) (v : ℤ) :
    v ∈ values x c color ↔ ∃ i, c i = color ∧ x i = v := by
  simp [values]

theorem mem_negValues {n : ℕ} (x : Fin n → ℤ) (c : Fin n → Fin 3) (v : ℤ) :
    v ∈ negValues x c ↔ ∃ i, c i = 2 ∧ -x i = v := by
  simp [negValues, mem_values]

def DistinctZeroSum {n : ℕ} (x : Fin n → ℤ) : Prop :=
  ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ x i + x j + x k = 0

def ThreeSetWitness (a b c : Finset ℤ) : Prop :=
  ∃ u ∈ a, ∃ v ∈ b, ∃ w ∈ c, u + v = w

/-- Exact equivalence between an array 3SUM witness at distinct positions and
one of the enumerated, deduplicated three-set instances. -/
theorem reduction_correct {n : ℕ} (x : Fin n → ℤ) :
    DistinctZeroSum x ↔ ∃ c ∈ family n,
      ThreeSetWitness (values x c 0) (values x c 1) (negValues x c) := by
  constructor
  · rintro ⟨i, j, k, hij, hik, hjk, hsum⟩
    obtain ⟨c, hc, hi, hj, hk⟩ := family_separates hij hik hjk
    refine ⟨c, hc, x i, (mem_values x c 0 _).mpr ⟨i, hi, rfl⟩,
      x j, (mem_values x c 1 _).mpr ⟨j, hj, rfl⟩,
      -x k, (mem_negValues x c _).mpr ⟨k, hk, rfl⟩, ?_⟩
    omega
  · rintro ⟨c, _, a, ha, b, hb, z, hz, he⟩
    obtain ⟨i, hi, rfl⟩ := (mem_values x c 0 a).mp ha
    obtain ⟨j, hj, rfl⟩ := (mem_values x c 1 b).mp hb
    obtain ⟨k, hk, rfl⟩ := (mem_negValues x c z).mp hz
    refine ⟨i, j, k, ?_, ?_, ?_, by omega⟩
    · intro heq
      subst j
      simp_all
    · intro heq
      subst k
      simp_all
    · intro heq
      subst k
      simp_all

/-- The executable reduction calls its supplied three-set solver over the
small parameter domain directly. It does not materialize all colorings. -/
def runReduction {n : ℕ} (x : Fin n → ℤ)
    (solve : Finset ℤ → Finset ℤ → Finset ℤ → Bool) : Bool :=
  decide (∃ p : Parameter (indexWidth n),
    solve (values x (colorIndex p) 0) (values x (colorIndex p) 1)
      (negValues x (colorIndex p)) = true)

/-- Correctness composes with a supplied exact three-set solver. The solver's
running time is deliberately not claimed by this reduction theorem. -/
theorem runReduction_correct {n : ℕ} (x : Fin n → ℤ)
    (solve : Finset ℤ → Finset ℤ → Finset ℤ → Bool)
    (hsolve : ∀ a b c, solve a b c = true ↔ ThreeSetWitness a b c) :
    runReduction x solve = true ↔ DistinctZeroSum x := by
  rw [reduction_correct]
  simp only [runReduction, decide_eq_true_eq, hsolve]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨colorIndex p, Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩, hp⟩
  · rintro ⟨c, hc, hp⟩
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hc
    exact ⟨p, hp⟩

end ThreeSum.Coloring
