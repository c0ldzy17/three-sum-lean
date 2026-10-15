import Submission.ThreeSum.HashFamily
import Mathlib.Tactic.LinearCombination

/-!
# Tagged linear hashes for the trinary cover

The two source tags are separate coordinates.  They make every ordered
endpoint pair independent, including equal untagged words.  Distinct words
on one side together with any word on the other side give rank three.
This module proves these actual vector relations; it does not replace the
higher paired-rank entropy estimate by an assumption.
-/

namespace ThreeSum.TernaryCoverHashes

open scoped BigOperators

variable {ι K : Type*} [Fintype ι] [Field K]

abbrev Coordinate (ι : Type*) := Sum ι Bool

def leftVector (x : ι → K) : Coordinate ι → K :=
  Sum.elim x (fun b => if b then 0 else 1)

def rightVector (x : ι → K) : Coordinate ι → K :=
  Sum.elim x (fun b => if b then 1 else 0)

def outputVector (x : ι → K) : Coordinate ι → K :=
  Sum.elim x (fun _ => 1)

theorem vector_sum {x y q : ι → K} (hsum : ∀ i, x i + y i = q i) :
    leftVector x + rightVector y = outputVector q := by
  funext i
  cases i with
  | inl i => exact hsum i
  | inr b => cases b <;> simp [leftVector, rightVector, outputVector]

theorem pair_relation (x y : ι → K) {a b : K}
    (h : ∀ i, a * leftVector x i + b * rightVector y i = 0) :
    a = 0 ∧ b = 0 := by
  exact ⟨by simpa [leftVector, rightVector] using h (.inr false),
    by simpa [leftVector, rightVector] using h (.inr true)⟩

theorem same_side_relation {x y : ι → K} (hxy : x ≠ y) (z : ι → K)
    {a b c : K}
    (h : ∀ i, a * leftVector x i + b * leftVector y i +
      c * rightVector z i = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  classical
  have hab : a + b = 0 := by
    simpa [leftVector, rightVector] using h (.inr false)
  have hc : c = 0 := by
    simpa [leftVector, rightVector] using h (.inr true)
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra! hsame
    exact hxy (funext hsame)
  have he : a * (x i - y i) = 0 := by
    have hr : a * x i + b * y i + c * z i = 0 := h (.inl i)
    linear_combination hr - y i * hab - z i * hc
  have ha : a = 0 := (mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr hi)
  exact ⟨ha, by simpa [ha] using hab, hc⟩

theorem pair_independent (x y : ι → K) :
    LinearIndependent K ![leftVector x, rightVector y] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hr := pair_relation x y (a := g 0) (b := g 1) (fun p => by
    have hp := congrFun hg p
    simpa [Fin.sum_univ_succ] using hp)
  fin_cases i <;> simp_all

theorem same_side_independent {x y : ι → K} (hxy : x ≠ y) (z : ι → K) :
    LinearIndependent K ![leftVector x, leftVector y, rightVector z] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hr := same_side_relation hxy z (a := g 0) (b := g 1) (c := g 2)
    (fun p => by
      have hp := congrFun hg p
      simpa [Fin.sum_univ_succ, add_assoc] using hp)
  fin_cases i <;> simp_all

theorem right_same_side_relation {x y : ι → K} (hxy : x ≠ y) (z : ι → K)
    {a b c : K}
    (h : ∀ i, a * rightVector x i + b * rightVector y i +
      c * leftVector z i = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  classical
  have hab : a + b = 0 := by
    simpa [leftVector, rightVector] using h (.inr true)
  have hc : c = 0 := by
    simpa [leftVector, rightVector] using h (.inr false)
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra! hsame
    exact hxy (funext hsame)
  have he : a * (x i - y i) = 0 := by
    have hr : a * x i + b * y i + c * z i = 0 := h (.inl i)
    linear_combination hr - y i * hab - z i * hc
  have ha : a = 0 := (mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr hi)
  exact ⟨ha, by simpa [ha] using hab, hc⟩

theorem right_same_side_independent {x y : ι → K} (hxy : x ≠ y) (z : ι → K) :
    LinearIndependent K ![rightVector x, rightVector y, leftVector z] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hr := right_same_side_relation hxy z (a := g 0) (b := g 1) (c := g 2)
    (fun p => by
      have hp := congrFun hg p
      simpa [Fin.sum_univ_succ, add_assoc] using hp)
  fin_cases i <;> simp_all

section Finite

variable [Fintype K] [DecidableEq K] [DecidableEq ι]

def linearHash (v : Coordinate ι → K) (w : Coordinate ι → K) : K :=
  ∑ i, v i * w i

def pairEvent (x y : ι → K) (a b : K) : Finset (Coordinate ι → K) :=
  Finset.univ.filter fun w => linearHash (leftVector x) w = a ∧
    linearHash (rightVector y) w = b

/-- Exactly uniform counts for the actual tagged pair, with no inequality
between requested residues or untagged endpoint words. -/
theorem pairEvent_card (x y : ι → K) (a b : K) :
    Fintype.card K ^ 2 * (pairEvent x y a b).card =
      Fintype.card (Coordinate ι → K) := by
  classical
  have heq : pairEvent x y a b = Finset.univ.filter (fun w =>
      HashFamily.hashMap ![leftVector x, rightVector y] w = ![a, b]) := by
    ext w
    simp only [pairEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [funext_iff]
    simp [linearHash, HashFamily.hashMap_apply, Fin.forall_fin_succ]
  rw [heq]
  simpa using HashFamily.hash_fiber_card (pair_independent x y) ![a, b]

/-- An additional distinct source on the left contributes one independent
hash equation, even when any requested residues coincide. -/
theorem left_triple_card {x u : ι → K} (hxu : x ≠ u) (y : ι → K) (a b c : K) :
    Fintype.card K ^ 3 *
      ((pairEvent x y a b).filter fun w => linearHash (leftVector u) w = c).card =
        Fintype.card (Coordinate ι → K) := by
  classical
  have heq : ((pairEvent x y a b).filter fun w => linearHash (leftVector u) w = c) =
      Finset.univ.filter (fun w =>
        HashFamily.hashMap ![leftVector x, leftVector u, rightVector y] w = ![a, c, b]) := by
    ext w
    simp only [pairEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [funext_iff]
    simp [linearHash, HashFamily.hashMap_apply, Fin.forall_fin_succ, and_assoc, and_left_comm,
      and_comm]
  rw [heq]
  simpa using HashFamily.hash_fiber_card (same_side_independent hxu y) ![a, c, b]

theorem right_triple_card (x : ι → K) {y v : ι → K} (hyv : y ≠ v) (a b c : K) :
    Fintype.card K ^ 3 *
      ((pairEvent x y a b).filter fun w => linearHash (rightVector v) w = c).card =
        Fintype.card (Coordinate ι → K) := by
  classical
  have heq : ((pairEvent x y a b).filter fun w => linearHash (rightVector v) w = c) =
      Finset.univ.filter (fun w =>
        HashFamily.hashMap ![rightVector y, rightVector v, leftVector x] w = ![b, c, a]) := by
    ext w
    simp only [pairEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [funext_iff]
    simp [linearHash, HashFamily.hashMap_apply, Fin.forall_fin_succ, and_assoc, and_left_comm,
      and_comm]
  rw [heq]
  simpa using HashFamily.hash_fiber_card (right_same_side_independent hyv x) ![b, c, a]

end Finite

/-- Unequal nonzero projection coefficients are injective inside every
fixed sum level.  This is the algebraic input to the projection majorization
argument; it is valid for all field characteristics. -/
theorem projection_injective_on_sum {a b x y x' y' : K} (hab : a ≠ b)
    (hsum : x + y = x' + y')
    (hprojection : a * x + b * y = a * x' + b * y') :
    x = x' ∧ y = y' := by
  have he : (a - b) * (x - x') = 0 := by
    linear_combination hprojection - b * hsum
  have hx : x = x' := sub_eq_zero.mp
    ((mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hab))
  exact ⟨hx, by simpa [hx] using hsum⟩

end ThreeSum.TernaryCoverHashes
