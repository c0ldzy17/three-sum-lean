import Mathlib.Data.Int.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

/-!
# Exact arithmetic interface for the deterministic histogram construction

These are finite arithmetic and counting theorems.  They do not assert a
running-time bound or the existence of a word-RAM implementation.
-/

namespace ThreeSum.Arithmetic

open Finset
open scoped BigOperators

/-! ## Guarded arithmetic-to-radix lifts -/

/-- A multiple of a positive modulus strictly between its two nearest
nonzero multiples must vanish. -/
theorem eq_zero_of_dvd_of_bounds {R x : ℤ} (hR : 0 < R)
    (hlo : -R < x) (hhi : x < R) (hdiv : R ∣ x) : x = 0 := by
  obtain ⟨q, rfl⟩ := hdiv
  by_cases hq : q = 0
  · simp [hq]
  have hcases : q ≤ -1 ∨ 1 ≤ q := by omega
  rcases hcases with hq | hq
  · have hm := mul_le_mul_of_nonneg_left hq hR.le
    nlinarith
  · have hm := mul_le_mul_of_nonneg_left hq hR.le
    nlinarith

/-- The only three signed lifts queried by the algorithm. -/
def SmallLift (j : ℤ) : Prop := j = -1 ∨ j = 0 ∨ j = 1

/-- With the range guard, a radix congruence for a normalized input triple
is an integer equality with one of the three arithmetic lifts. -/
theorem guarded_lift_eq {P R a b c d j : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ R)
    (ha0 : 0 ≤ a) (haP : a < P)
    (hb0 : 0 ≤ b) (hbP : b < P)
    (hc0 : 0 ≤ c) (hcP : c < P)
    (hj : SmallLift j)
    (hcong : R ∣ (c + d - b) - (a + j * P + d)) :
    c - b = a + j * P := by
  have hR : 0 < R := by omega
  have hdiv : R ∣ c - b - a - j * P := by
    convert hcong using 1 <;> ring
  have hbds : -R < c - b - a - j * P ∧ c - b - a - j * P < R := by
    rcases hj with rfl | rfl | rfl <;> constructor <;> nlinarith
  have hz := eq_zero_of_dvd_of_bounds hR hbds.1 hbds.2 hdiv
  linarith

/-- A queried representation cannot introduce an alias that fails the
arithmetic congruence. -/
theorem arithmetic_dvd_of_guarded_lift {P R a b c d j : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ R)
    (ha0 : 0 ≤ a) (haP : a < P)
    (hb0 : 0 ≤ b) (hbP : b < P)
    (hc0 : 0 ≤ c) (hcP : c < P)
    (hj : SmallLift j)
    (hcong : R ∣ (c + d - b) - (a + j * P + d)) :
    P ∣ c - b - a := by
  have heq := guarded_lift_eq hP hguard ha0 haP hb0 hbP hc0 hcP hj hcong
  refine ⟨j, ?_⟩
  nlinarith

/-- Distinct signed lifts of a fixed A residue never give the same radix
query key under the range guard. -/
theorem guarded_lift_unique {P R a d j k : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ R)
    (hj : SmallLift j) (hk : SmallLift k)
    (hcong : R ∣ (a + j * P + d) - (a + k * P + d)) : j = k := by
  have hR : 0 < R := by omega
  have hdiv : R ∣ (j - k) * P := by
    convert hcong using 1 <;> ring
  have hbds : -R < (j - k) * P ∧ (j - k) * P < R := by
    rcases hj with rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl <;> constructor <;> nlinarith
  have hz := eq_zero_of_dvd_of_bounds hR hbds.1 hbds.2 hdiv
  rcases mul_eq_zero.mp hz with h | h
  · omega
  · omega

/-- The actual modulo-key interface, before lifting back to original values. -/
theorem guarded_lift_eq_of_modEq {P R a b c d j : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ R)
    (ha0 : 0 ≤ a) (haP : a < P)
    (hb0 : 0 ≤ b) (hbP : b < P)
    (hc0 : 0 ≤ c) (hcP : c < P)
    (hj : SmallLift j)
    (hkey : Int.ModEq R (a + j * P + d) (c + d - b)) :
    c - b = a + j * P :=
  guarded_lift_eq hP hguard ha0 haP hb0 hbP hc0 hcP hj hkey.dvd

/-- Guarded radix-key equality implies the arithmetic divisibility test on
the original signed integer values, not only on their canonical residues. -/
theorem guarded_remainder_lift_sound {P R a b c d j : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ R) (hj : SmallLift j)
    (hkey : Int.ModEq R (a % P + j * P + d) (c % P + d - b % P)) :
    P ∣ c - b - a := by
  have hp0 : P ≠ 0 := ne_of_gt hP
  have hnorm : P ∣ c % P - b % P - a % P :=
    arithmetic_dvd_of_guarded_lift hP hguard
      (Int.emod_nonneg _ hp0) (Int.emod_lt_of_pos _ hP)
      (Int.emod_nonneg _ hp0) (Int.emod_lt_of_pos _ hP)
      (Int.emod_nonneg _ hp0) (Int.emod_lt_of_pos _ hP) hj hkey.dvd
  have heq : Int.ModEq P (c % P - b % P - a % P) (c - b - a) :=
    ((Int.mod_modEq c P).sub (Int.mod_modEq b P)).sub (Int.mod_modEq a P)
  exact Int.modEq_zero_iff_dvd.mp (heq.symm.trans hnorm.modEq_zero_int)

/-- Completeness of the signed-lift list for any modular candidate.
In fact, canonical residues only need the lifts -1 and 0. -/
theorem small_lift_exists {P a b c : ℤ} (hP : 0 < P)
    (ha0 : 0 ≤ a) (haP : a < P)
    (hb0 : 0 ≤ b) (hbP : b < P)
    (hc0 : 0 ≤ c) (hcP : c < P)
    (hdiv : P ∣ c - b - a) :
    ∃ j : ℤ, SmallLift j ∧ c - b = a + j * P := by
  obtain ⟨j, hj⟩ := hdiv
  have hjlo : -1 ≤ j := by
    by_contra h
    have hj' : j ≤ -2 := by omega
    have hm := mul_le_mul_of_nonneg_left hj' hP.le
    nlinarith
  have hjhi : j ≤ 0 := by
    by_contra h
    have hj' : 1 ≤ j := by omega
    have hm := mul_le_mul_of_nonneg_left hj' hP.le
    nlinarith
  refine ⟨j, ?_, ?_⟩
  · unfold SmallLift
    omega
  · nlinarith

/-! ## The weighted false-count identity -/

/-- A concrete Bezout witness is enough for the product-divisibility
identity.  The statement does not assume primality or that the arithmetic
modulus is prime. -/
theorem mul_dvd_iff_of_bezout {m l x : ℤ}
    (hbez : ∃ u v : ℤ, u * m + v * l = 1) :
    m * l ∣ x ↔ m ∣ x ∧ l ∣ x := by
  constructor
  · rintro ⟨z, hz⟩
    constructor
    · refine ⟨l * z, ?_⟩
      rw [hz]
      ring
    · refine ⟨m * z, ?_⟩
      rw [hz]
      ring
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    obtain ⟨u, v, huv⟩ := hbez
    refine ⟨u * b + v * a, ?_⟩
    calc
      x = (u * m + v * l) * x := by rw [huv]; ring
      _ = u * m * x + v * l * x := by ring
      _ = u * m * (l * b) + v * l * (m * a) := by rw [← hb, ← ha]
      _ = m * l * (u * b + v * a) := by ring

/-- Integer-valued divisibility is converted to a natural indicator. -/
def dividesIndicator (m x : ℤ) : ℕ := if m ∣ x then 1 else 0

/-- Number of auxiliary divisibility tests failed by an integer difference. -/
def missWeight (L : Finset ℤ) (x : ℤ) : ℕ :=
  ∑ l ∈ L, if l ∣ x then 0 else 1

/-- Every auxiliary test either succeeds or fails, exactly once. -/
theorem missWeight_add_hits (L : Finset ℤ) (x : ℤ) :
    missWeight L x + (∑ l ∈ L, dividesIndicator l x) = L.card := by
  unfold missWeight
  rw [← Finset.sum_add_distrib]
  calc
    (∑ l ∈ L, ((if l ∣ x then 0 else 1) + dividesIndicator l x)) =
        ∑ _l ∈ L, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro l hl
      by_cases h : l ∣ x <;> simp [dividesIndicator, h]
    _ = L.card := by simp

theorem weighted_indicator_identity (L : Finset ℤ) (m x : ℤ)
    (hcop : ∀ l ∈ L, ∃ u v : ℤ, u * m + v * l = 1) :
    (if m ∣ x then missWeight L x else 0) +
        (∑ l ∈ L, dividesIndicator (m * l) x) =
      L.card * dividesIndicator m x := by
  by_cases hm : m ∣ x
  · have hsum : (∑ l ∈ L, dividesIndicator (m * l) x) =
        ∑ l ∈ L, dividesIndicator l x := by
      apply Finset.sum_congr rfl
      intro l hl
      simp [dividesIndicator, mul_dvd_iff_of_bezout (hcop l hl), hm]
    rw [if_pos hm, hsum]
    simpa [dividesIndicator, hm] using missWeight_add_hits L x
  · have hsum : (∑ l ∈ L, dividesIndicator (m * l) x) = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      have hnot : ¬ m * l ∣ x := fun h => hm ((mul_dvd_iff_of_bezout (hcop l hl)).mp h).1
      simp [dividesIndicator, hnot]
    rw [if_neg hm, hsum]
    simp [hm, dividesIndicator]

def modCount {ι : Type*} (T : Finset ι) (difference : ι → ℤ) (m : ℤ) : ℕ :=
  ∑ i ∈ T, dividesIndicator m (difference i)

def weightedFalseCount {ι : Type*} (T : Finset ι) (difference : ι → ℤ)
    (L : Finset ℤ) (m : ℤ) : ℕ :=
  ∑ i ∈ T, if m ∣ difference i then missWeight L (difference i) else 0

/-- The exact non-subtractive identity; it also proves the subtracted
quantity is no larger than `L.card * modCount`. -/
theorem weightedFalseCount_add {ι : Type*} (T : Finset ι) (difference : ι → ℤ)
    (L : Finset ℤ) (m : ℤ)
    (hcop : ∀ l ∈ L, ∃ u v : ℤ, u * m + v * l = 1) :
    weightedFalseCount T difference L m +
        (∑ l ∈ L, modCount T difference (m * l)) =
      L.card * modCount T difference m := by
  unfold weightedFalseCount modCount
  calc
    (∑ i ∈ T, if m ∣ difference i then missWeight L (difference i) else 0) +
        (∑ l ∈ L, ∑ i ∈ T, dividesIndicator (m * l) (difference i)) =
      ∑ i ∈ T, ((if m ∣ difference i then missWeight L (difference i) else 0) +
        ∑ l ∈ L, dividesIndicator (m * l) (difference i)) := by
          rw [Finset.sum_add_distrib, Finset.sum_comm]
    _ = ∑ i ∈ T, L.card * dividesIndicator m (difference i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact weighted_indicator_identity L m (difference i) hcop
    _ = L.card * (∑ i ∈ T, dividesIndicator m (difference i)) := by
      rw [Finset.mul_sum]

/-- The actual `H_m = s N_m - sum N_(m*l)` formula, over natural counts. -/
theorem weightedFalseCount_eq {ι : Type*} (T : Finset ι) (difference : ι → ℤ)
    (L : Finset ℤ) (m : ℤ)
    (hcop : ∀ l ∈ L, ∃ u v : ℤ, u * m + v * l = 1) :
    weightedFalseCount T difference L m =
      L.card * modCount T difference m - (∑ l ∈ L, modCount T difference (m * l)) := by
  have h := weightedFalseCount_add T difference L m hcop
  omega

theorem missWeight_pos_of_witness {L : Finset ℤ} {x l : ℤ}
    (hl : l ∈ L) (hnot : ¬ l ∣ x) : 1 ≤ missWeight L x := by
  have h := Finset.single_le_sum (s := L)
    (f := fun z : ℤ => if z ∣ x then (0 : ℕ) else 1)
    (fun z hz => Nat.zero_le _) hl
  simpa [missWeight, hnot] using h

@[simp] theorem missWeight_zero (L : Finset ℤ) : missWeight L 0 = 0 := by
  simp [missWeight]

/-- Pairwise coprime auxiliary moduli whose product exceeds the absolute
difference separate every nonzero difference.  No primality is necessary. -/
theorem exists_aux_not_dvd_of_prod_bound (L : Finset ℤ) (x : ℤ)
    (hcop : (L : Set ℤ).Pairwise (fun a b => IsCoprime a b))
    (hx : x ≠ 0) (hbound : x.natAbs < (∏ l ∈ L, l).natAbs) :
    ∃ l ∈ L, ¬ l ∣ x := by
  classical
  by_contra hnone
  push_neg at hnone
  have hdiv : (∏ l ∈ L, l) ∣ x := Finset.prod_dvd_of_coprime hcop hnone
  have hle := Int.natAbs_le_of_dvd_ne_zero hdiv hx
  omega

/-- Auxiliary tests separating every nonzero input difference make the
weighted score an upper bound on the number of false modular triples. -/
theorem falseCount_le_weightedFalseCount {ι : Type*} (T : Finset ι)
    (difference : ι → ℤ) (L : Finset ℤ) (m : ℤ)
    (hsep : ∀ i ∈ T, difference i ≠ 0 → ∃ l ∈ L, ¬ l ∣ difference i) :
    (∑ i ∈ T, if m ∣ difference i ∧ difference i ≠ 0 then (1 : ℕ) else 0) ≤
      weightedFalseCount T difference L m := by
  unfold weightedFalseCount
  apply Finset.sum_le_sum
  intro i hi
  by_cases h : m ∣ difference i ∧ difference i ≠ 0
  · obtain ⟨l, hl, hnot⟩ := hsep i hi h.2
    simpa [h, h.1] using missWeight_pos_of_witness hl hnot
  · simp only [if_neg h]
    exact Nat.zero_le _

/-! ## Exact early YES from per-original-triple representation caps -/

def fiberWeight {ι τ : Type*} [DecidableEq τ] (I : Finset ι)
    (owner : ι → τ) (weight : ι → ℕ) (t : τ) : ℕ :=
  ∑ i ∈ I, if owner i = t then weight i else 0

theorem sum_fiberWeight {ι τ : Type*} [Fintype τ] [DecidableEq τ]
    (I : Finset ι) (owner : ι → τ) (weight : ι → ℕ) :
    (∑ t : τ, fiberWeight I owner weight t) = ∑ i ∈ I, weight i := by
  classical
  unfold fiberWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp

/-- If total represented mass exceeds `Rmax * H`, some positive incidence
belongs to a true original triple.  The hypotheses bound individual false
fibers and the number of false originals, rather than postulating the
desired conclusion or a full running-time theorem. -/
theorem early_yes {ι τ : Type*} [Fintype τ] [DecidableEq τ]
    (I : Finset ι) (owner : ι → τ) (weight : ι → ℕ)
    (good : τ → Prop) [DecidablePred good] (Rmax H : ℕ)
    (hcap : ∀ t : τ, ¬ good t → fiberWeight I owner weight t ≤ Rmax)
    (hcount : (Finset.univ.filter (fun t : τ => ¬ good t)).card ≤ H)
    (hlarge : Rmax * H < ∑ i ∈ I, weight i) :
    ∃ i ∈ I, 0 < weight i ∧ good (owner i) := by
  classical
  by_contra hnone
  have hzero : ∀ i ∈ I, good (owner i) → weight i = 0 := by
    intro i hi hg
    by_contra hw
    exact hnone ⟨i, hi, Nat.pos_of_ne_zero hw, hg⟩
  have hbound : ∀ t : τ, fiberWeight I owner weight t ≤
      if good t then 0 else Rmax := by
    intro t
    by_cases ht : good t
    · simp only [if_pos ht]
      have hz : fiberWeight I owner weight t = 0 := by
        unfold fiberWeight
        apply Finset.sum_eq_zero
        intro i hi
        by_cases he : owner i = t
        · simp [he, hzero i hi (he.symm ▸ ht)]
        · simp [he]
      omega
    · simpa [ht] using hcap t ht
  have hsum : (∑ t : τ, if good t then (0 : ℕ) else Rmax) =
      (Finset.univ.filter (fun t : τ => ¬ good t)).card * Rmax := by
    calc
      (∑ t : τ, if good t then (0 : ℕ) else Rmax) =
          ∑ t ∈ Finset.univ.filter (fun t : τ => ¬ good t), Rmax := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro t ht
        by_cases hg : good t <;> simp [hg]
      _ = _ := by simp
  have htotal : (∑ i ∈ I, weight i) ≤ Rmax * H := by
    calc
      (∑ i ∈ I, weight i) = ∑ t : τ, fiberWeight I owner weight t :=
        (sum_fiberWeight I owner weight).symm
      _ ≤ ∑ t : τ, if good t then 0 else Rmax :=
        Finset.sum_le_sum (fun t ht => hbound t)
      _ = (Finset.univ.filter (fun t : τ => ¬ good t)).card * Rmax := hsum
      _ ≤ H * Rmax := Nat.mul_le_mul_right Rmax hcount
      _ = Rmax * H := Nat.mul_comm _ _
  omega

end ThreeSum.Arithmetic
