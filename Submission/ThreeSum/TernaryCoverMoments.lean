import Submission.ThreeSum.HashFamily
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Exact high-moment and bad-map arithmetic

The moment expansion retains every ordered edge tuple, including repetitions.
The class-count lemma explicitly records its two mathematical obligations:
the number of tuples of each fixed relation class, and the uniform hash
fiber bound.  They are not asserted for the trinary graph in this module.
-/

namespace ThreeSum.TernaryCoverMoments

open Finset
open scoped BigOperators

variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq Ω]

def jointEvent (events : E → Finset Ω) {k : ℕ} (es : Fin k → E) : Finset Ω :=
  univ.filter fun w => ∀ i, w ∈ events (es i)

theorem sum_incidenceCount_pow (events : E → Finset Ω) (k : ℕ) :
    (∑ w, HashFamily.incidenceCount events w ^ k) =
      ∑ es : Fin k → E, (jointEvent events es).card := by
  classical
  simp_rw [HashFamily.incidenceCount_eq_sum, Fintype.sum_pow, Fintype.prod_boole]
  rw [sum_comm]
  apply sum_congr rfl
  intro es _
  unfold jointEvent
  rw [card_eq_sum_ones, sum_filter]
  apply sum_congr rfl
  intro w _
  by_cases h : ∀ i, w ∈ events (es i) <;> simp [h]

/-- Exact cancellation of one fixed relation class's rank exponent.
The class-count and hash-fiber hypotheses are exposed, rather than hidden
inside an assumed moment estimate. -/
theorem moment_bound_of_classes {C : Type*} [Fintype C] [DecidableEq C]
    (events : E → Finset Ω) (k p : ℕ) (hp : 0 < p)
    (classify : (Fin k → E) → C) (rank : C → ℕ)
    (hcount : ∀ c : C, (univ.filter fun es => classify es = c).card ≤ p ^ rank c)
    (hhash : ∀ es : Fin k → E,
      p ^ rank (classify es) * (jointEvent events es).card ≤ Fintype.card Ω) :
    (∑ w, HashFamily.incidenceCount events w ^ k) ≤ Fintype.card C * Fintype.card Ω := by
  classical
  rw [sum_incidenceCount_pow]
  have hclass (c : C) :
      (∑ es ∈ (univ.filter fun es => classify es = c), (jointEvent events es).card) ≤
        Fintype.card Ω := by
    apply Nat.le_of_mul_le_mul_left (c := p ^ rank c) ?_ (Nat.pow_pos hp)
    rw [mul_sum]
    calc
      _ ≤ ∑ _es ∈ (univ.filter fun es => classify es = c), Fintype.card Ω := by
        apply sum_le_sum
        intro es hes
        have hc := (mem_filter.mp hes).2
        simpa [hc] using hhash es
      _ = (univ.filter fun es : Fin k → E => classify es = c).card * Fintype.card Ω := by simp
      _ ≤ p ^ rank c * Fintype.card Ω := Nat.mul_le_mul_right _ (hcount c)
  have hsplit : (∑ es : Fin k → E, (jointEvent events es).card) =
      ∑ c : C, ∑ es ∈ (univ.filter fun es => classify es = c), (jointEvent events es).card := by
    simp_rw [sum_filter]
    rw [sum_comm]
    simp
  rw [hsplit]
  calc
    _ ≤ ∑ _c : C, Fintype.card Ω := sum_le_sum (fun c _ => hclass c)
    _ = Fintype.card C * Fintype.card Ω := by simp

section Caps

variable {T : Type*} [Fintype T] [DecidableEq T]

def badMaps (X : Ω → T → ℕ) (τ : ℕ) : Finset Ω :=
  univ.filter fun w => ∃ t, τ < X w t

theorem target_bad_count_bound (X : Ω → T → ℕ) (k τ : ℕ) (t : T) :
    τ ^ k * (univ.filter fun w => τ < X w t).card ≤ ∑ w, X w t ^ k := by
  classical
  calc
    _ = ∑ _w ∈ (univ.filter fun w => τ < X w t), τ ^ k := by simp [Nat.mul_comm]
    _ ≤ ∑ w ∈ (univ.filter fun w => τ < X w t), X w t ^ k := by
      apply sum_le_sum
      intro w hw
      exact Nat.pow_le_pow_left (mem_filter.mp hw).2.le k
    _ ≤ ∑ w, X w t ^ k :=
      sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => Nat.zero_le _)

/-- All literal target pairs are included in the union bound. -/
theorem badMaps_count_bound (X : Ω → T → ℕ) (k τ C : ℕ)
    (hmoment : ∀ t : T, (∑ w, X w t ^ k) ≤ C * Fintype.card Ω) :
    τ ^ k * (badMaps X τ).card ≤ Fintype.card T * C * Fintype.card Ω := by
  classical
  have hcard : (badMaps X τ).card ≤
      ∑ t : T, (univ.filter fun w => τ < X w t).card := by
    have heq : badMaps X τ =
        (univ : Finset T).biUnion (fun t => univ.filter fun w => τ < X w t) := by
      ext w
      simp [badMaps]
    rw [heq]
    exact card_biUnion_le
  calc
    _ ≤ τ ^ k * ∑ t : T, (univ.filter fun w => τ < X w t).card :=
      Nat.mul_le_mul_left _ hcard
    _ = ∑ t : T, τ ^ k * (univ.filter fun w => τ < X w t).card := mul_sum ..
    _ ≤ ∑ t : T, C * Fintype.card Ω :=
      sum_le_sum (fun t _ => (target_bad_count_bound X k τ t).trans (hmoment t))
    _ = _ := by simp; ring

/-- Retained target mass removed by a global raw-cap test is bounded by the
actual retained fiber cap.  The cap factor must be charged before choosing
the high moment order. -/
theorem removed_mass_bound (f : Ω → ℕ) (bad : Finset Ω) (B : ℕ)
    (hcap : ∀ w, f w ≤ B ^ 2) :
    (∑ w ∈ bad, f w) ≤ B ^ 2 * bad.card := by
  calc
    _ ≤ ∑ _w ∈ bad, B ^ 2 := sum_le_sum (fun w _ => hcap w)
    _ = _ := by simp [Nat.mul_comm]

end Caps

end ThreeSum.TernaryCoverMoments
