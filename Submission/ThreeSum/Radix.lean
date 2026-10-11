import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Aesop

/-!
# Exact radix composition of finite local covers

The recursion enumerates only representations of one supplied target pair.
The coverage and multiplicity proofs quantify over arbitrary integer targets;
no enumeration of the square of the global modulus is used in the definition.
-/

namespace ThreeSum.Radix

open Finset
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def localFiber (p : ℤ) (left right : Ω → ℤ) (a b : ℤ) : Finset Ω :=
  univ.filter fun ω => p ∣ a - left ω ∧ p ∣ b - right ω

/-- The value of a positional hash, starting with its low digit. -/
def positionalHash (p : ℤ) (raw : Ω → ℤ) : List Ω → ℤ
  | [] => 0
  | ω :: rest => raw ω + p * positionalHash p raw rest

/-- Exact candidate recursion.  Each local choice determines the next pair
of quotient targets, so carries do not create an independent branching factor. -/
def representations (p : ℤ) (left right : Ω → ℤ) : ℕ → ℤ → ℤ → Finset (List Ω)
  | 0, _, _ => {[]}
  | j + 1, a, b =>
    (localFiber p left right a b).biUnion fun ω =>
      (representations p left right j ((a - left ω) / p) ((b - right ω) / p)).image
        (List.cons ω)

/-- Divisibility through one radix digit. -/
theorem radix_divisibility (p a h t : ℤ) (hp : p ≠ 0) (j : ℕ) :
    p ^ (j + 1) ∣ a - (h + p * t) ↔
      p ∣ a - h ∧ p ^ j ∣ (a - h) / p - t := by
  constructor
  · intro hd
    have hd₁ : p ∣ a - h := by
      have hpow : p ∣ p ^ (j + 1) := dvd_pow_self _ (by omega)
      have hm : p ∣ p * t := dvd_mul_right _ _
      have hs := Int.dvd_add (dvd_trans hpow hd) hm
      convert hs using 1 <;> ring
    refine ⟨hd₁, ?_⟩
    have heq := Int.mul_ediv_cancel' hd₁
    have hrew : a - (h + p * t) = p * ((a - h) / p - t) := by
      nlinarith
    rw [hrew, pow_succ', mul_dvd_mul_iff_left hp] at hd
    exact hd
  · rintro ⟨hd₁, hd₂⟩
    have heq := Int.mul_ediv_cancel' hd₁
    have hrew : a - (h + p * t) = p * ((a - h) / p - t) := by
      nlinarith
    rw [hrew, pow_succ', mul_dvd_mul_iff_left hp]
    exact hd₂

/-- The recursive family contains exactly all positional representations,
including their distinct schedules and local edge choices. -/
theorem mem_representations (p : ℤ) (hp : p ≠ 0) (left right : Ω → ℤ)
    (j : ℕ) (a b : ℤ) (xs : List Ω) :
    xs ∈ representations p left right j a b ↔
      xs.length = j ∧ p ^ j ∣ a - positionalHash p left xs ∧
        p ^ j ∣ b - positionalHash p right xs := by
  induction j generalizing a b xs with
  | zero =>
    cases xs <;> simp [representations, positionalHash]
  | succ j ih =>
    cases xs with
    | nil => simp [representations, positionalHash]
    | cons ω xs =>
      have hm : ω :: xs ∈ representations p left right (j + 1) a b ↔
          ω ∈ localFiber p left right a b ∧
            xs ∈ representations p left right j ((a - left ω) / p) ((b - right ω) / p) := by
        simp [representations]
      rw [hm, ih]
      simp only [localFiber, mem_filter, mem_univ, true_and, List.length_cons,
        Nat.add_right_cancel_iff, positionalHash, radix_divisibility p _ _ _ hp]
      tauto

/-- Every pair is globally covered if every local pair has a choice. -/
theorem representations_nonempty (p : ℤ) (left right : Ω → ℤ)
    (hcover : ∀ a b, (localFiber p left right a b).Nonempty)
    (j : ℕ) (a b : ℤ) : (representations p left right j a b).Nonempty := by
  induction j generalizing a b with
  | zero => exact singleton_nonempty _
  | succ j ih =>
    obtain ⟨ω, hω⟩ := hcover a b
    obtain ⟨xs, hxs⟩ := ih ((a - left ω) / p) ((b - right ω) / p)
    refine ⟨ω :: xs, ?_⟩
    exact mem_biUnion.mpr ⟨ω, hω, mem_image.mpr ⟨xs, hxs, rfl⟩⟩

/-- Multiplicity compounds once per local choice; there is no extra carry
factor in the global bound. -/
theorem representations_card_le (p : ℤ) (left right : Ω → ℤ) (B : ℕ)
    (hcap : ∀ a b, (localFiber p left right a b).card ≤ B)
    (j : ℕ) (a b : ℤ) : (representations p left right j a b).card ≤ B ^ j := by
  induction j generalizing a b with
  | zero => simp [representations]
  | succ j ih =>
    calc
      (representations p left right (j + 1) a b).card ≤
          ∑ ω ∈ localFiber p left right a b,
            ((representations p left right j ((a - left ω) / p)
              ((b - right ω) / p)).image (List.cons ω)).card := card_biUnion_le
      _ ≤ ∑ _ω ∈ localFiber p left right a b, B ^ j := by
        apply sum_le_sum
        intro ω _
        exact card_image_le.trans (ih _ _)
      _ = (localFiber p left right a b).card * B ^ j := by simp
      _ ≤ B * B ^ j := Nat.mul_le_mul_right _ (hcap a b)
      _ = B ^ (j + 1) := by ring

/-- A single combined finite theorem exposes both parts needed by the caller. -/
theorem radix_cover_and_cap (p : ℤ) (hp : p ≠ 0) (left right : Ω → ℤ) (B : ℕ)
    (hcover : ∀ a b, (localFiber p left right a b).Nonempty)
    (hcap : ∀ a b, (localFiber p left right a b).card ≤ B)
    (j : ℕ) (a b : ℤ) :
    (∃ xs, xs.length = j ∧ p ^ j ∣ a - positionalHash p left xs ∧
      p ^ j ∣ b - positionalHash p right xs) ∧
    (representations p left right j a b).card ≤ B ^ j := by
  obtain ⟨xs, hxs⟩ := representations_nonempty p left right hcover j a b
  exact ⟨⟨xs, (mem_representations p hp left right j a b xs).mp hxs⟩,
    representations_card_le p left right B hcap j a b⟩

end ThreeSum.Radix
