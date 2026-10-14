import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-! # Exact endpoint trimming and occurrence multiplicity

Retained graph edges inject into their two actual source buckets.  The
schedule occurrence is retained as part of every representation, so repeated
maps contribute separately.  These bounds do not assert a moment estimate.
-/

namespace ThreeSum.TernaryCoverRetained

open Finset
open scoped BigOperators

variable {E A B K : Type*} [Fintype E]
variable [DecidableEq A] [DecidableEq B] [DecidableEq K]

def bucket (vertices : Finset A) (hash : A → K) (a : K) : Finset A :=
  vertices.filter fun v => hash v = a

def hits (left : E → A) (right : E → B) (hashL : A → K) (hashR : B → K)
    (a b : K) : Finset E :=
  univ.filter fun e => hashL (left e) = a ∧ hashR (right e) = b

/-- Inject actual edges into the product of the two actual endpoint buckets. -/
theorem hits_card_le (left : E → A) (right : E → B)
    (hashL : A → K) (hashR : B → K) (VL : Finset A) (VR : Finset B)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hleft : ∀ e, left e ∈ VL) (hright : ∀ e, right e ∈ VR) (a b : K) :
    (hits left right hashL hashR a b).card ≤
      (bucket VL hashL a).card * (bucket VR hashR b).card := by
  classical
  have hcount : (hits left right hashL hashR a b).card ≤
      (bucket VL hashL a ×ˢ bucket VR hashR b).card := by
    apply card_le_card_of_injOn (fun e => (left e, right e))
    · intro e he
      obtain ⟨hl, hr⟩ := (mem_filter.mp he).2
      exact mem_product.mpr
        ⟨mem_filter.mpr ⟨hleft e, hl⟩, mem_filter.mpr ⟨hright e, hr⟩⟩
    · intro e _ f _ h
      exact hinj h
  simpa only [card_product] using hcount

theorem hits_card_le_sq (left : E → A) (right : E → B)
    (hashL : A → K) (hashR : B → K) (VL : Finset A) (VR : Finset B)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hleft : ∀ e, left e ∈ VL) (hright : ∀ e, right e ∈ VR)
    (a b : K) (cap : ℕ)
    (hl : (bucket VL hashL a).card ≤ cap)
    (hr : (bucket VR hashR b).card ≤ cap) :
    (hits left right hashL hashR a b).card ≤ cap ^ 2 := by
  calc
    _ ≤ (bucket VL hashL a).card * (bucket VR hashR b).card :=
      hits_card_le left right hashL hashR VL VR hinj hleft hright a b
    _ ≤ cap * cap := Nat.mul_le_mul hl hr
    _ = cap ^ 2 := by rw [pow_two]

/-- A finite schedule sums occurrence fibers, including repeated maps. -/
theorem occurrence_card_le {C I : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq C] (s : Finset C) (occurrence : C → I) (cap : ℕ)
    (hcap : ∀ i : I, (s.filter fun c => occurrence c = i).card ≤ cap) :
    s.card ≤ Fintype.card I * cap := by
  classical
  calc
    s.card = ∑ i : I, (s.filter fun c => occurrence c = i).card :=
      card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
    _ ≤ ∑ _i : I, cap := sum_le_sum (fun i _ => hcap i)
    _ = Fintype.card I * cap := by simp

end ThreeSum.TernaryCoverRetained
