import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sets
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-!
# The quadratic cardinal bound for relevant sorted-band triples

The proof is an explicit injection.  A relevant A interval either contains
the lower endpoint of a B/C difference interval, or its own lower endpoint
cuts that rectangle.  For a fixed cut, interval intersections inject into
the endpoints of the two families.

This file proves the combinatorial output bound and solution coverage.
It does not assign that bound to a cubic filtering implementation.
-/

namespace ThreeSum.Bands

variable {I J K : Type*}

def Separated (lo hi : I → ℤ) : Prop :=
  ∀ i j, i ≠ j → hi i < lo j ∨ hi j < lo i

theorem interval_unique {lo hi : I → ℤ} (hs : Separated lo hi)
    {i j : I} {x : ℤ} (hi0 : lo i ≤ x) (hi1 : x ≤ hi i)
    (hj0 : lo j ≤ x) (hj1 : x ≤ hi j) : i = j := by
  by_contra hne
  rcases hs i j hne with h | h <;> omega

theorem separated_shift {lo hi : I → ℤ} (hs : Separated lo hi) (t : ℤ) :
    Separated (fun i => t + lo i) (fun i => t + hi i) := by
  intro i j hne
  change t + hi i < t + lo j ∨ t + hi j < t + lo i
  rcases hs i j hne with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

def Overlap (alo ahi : I → ℤ) (blo bhi : J → ℤ) (p : I × J) : Prop :=
  alo p.1 ≤ bhi p.2 ∧ blo p.2 ≤ ahi p.1

instance (alo ahi : I → ℤ) (blo bhi : J → ℤ) (p : I × J) :
    Decidable (Overlap alo ahi blo bhi p) :=
  inferInstanceAs (Decidable (alo p.1 ≤ bhi p.2 ∧ blo p.2 ≤ ahi p.1))

def overlapOwner (alo : I → ℤ) (blo : J → ℤ) (p : I × J) : I ⊕ J :=
  if alo p.1 ≤ blo p.2 then Sum.inr p.2 else Sum.inl p.1

theorem overlapOwner_injective {alo ahi : I → ℤ} {blo bhi : J → ℤ}
    (hA : Separated alo ahi) (hB : Separated blo bhi)
    {p q : I × J} (hp : Overlap alo ahi blo bhi p) (hq : Overlap alo ahi blo bhi q)
    (heq : overlapOwner alo blo p = overlapOwner alo blo q) : p = q := by
  rcases p with ⟨i, j⟩
  rcases q with ⟨k, l⟩
  unfold overlapOwner at heq
  dsimp only at heq
  change alo i ≤ bhi j ∧ blo j ≤ ahi i at hp
  change alo k ≤ bhi l ∧ blo l ≤ ahi k at hq
  by_cases h : alo i ≤ blo j
  · by_cases h' : alo k ≤ blo l
    · simp only [if_pos h, if_pos h'] at heq
      have hj : j = l := Sum.inr.inj heq
      subst l
      have hi : i = k := interval_unique hA h hp.2 h' hq.2
      subst k
      rfl
    · simp [h, h'] at heq
  · by_cases h' : alo k ≤ blo l
    · simp [h, h'] at heq
    · simp only [if_neg h, if_neg h'] at heq
      have hi : i = k := Sum.inl.inj heq
      subst k
      have hj : j = l := interval_unique hB (by omega) hp.1 (by omega) hq.1
      subst l
      rfl

theorem overlap_card_le [Fintype I] [Fintype J]
    {alo ahi : I → ℤ} {blo bhi : J → ℤ}
    (hA : Separated alo ahi) (hB : Separated blo bhi) :
    Fintype.card {p : I × J // Overlap alo ahi blo bhi p} ≤
      Fintype.card I + Fintype.card J := by
  let f : {p : I × J // Overlap alo ahi blo bhi p} → I ⊕ J :=
    fun p => overlapOwner alo blo p.val
  have hinj : Function.Injective f := by
    intro p q h
    exact Subtype.ext (overlapOwner_injective hA hB p.property q.property h)
  simpa only [Fintype.card_sum] using Fintype.card_le_of_injective f hinj

def Relevant (alo ahi : I → ℤ) (blo bhi : J → ℤ) (clo chi : K → ℤ)
    (p : I × (J × K)) : Prop :=
  alo p.1 ≤ chi p.2.2 - blo p.2.1 ∧ clo p.2.2 - bhi p.2.1 ≤ ahi p.1

instance (alo ahi : I → ℤ) (blo bhi : J → ℤ) (clo chi : K → ℤ)
    (p : I × (J × K)) : Decidable (Relevant alo ahi blo bhi clo chi p) :=
  inferInstanceAs (Decidable
    (alo p.1 ≤ chi p.2.2 - blo p.2.1 ∧ clo p.2.2 - bhi p.2.1 ≤ ahi p.1))

def tripleOwner (alo : I → ℤ) (blo bhi : J → ℤ) (clo : K → ℤ)
    (p : I × (J × K)) : (J × K) ⊕ (I × (J ⊕ K)) :=
  if alo p.1 < clo p.2.2 - bhi p.2.1 then Sum.inl p.2
  else Sum.inr (p.1, overlapOwner (fun j => alo p.1 + blo j) clo p.2)

theorem tripleOwner_injective
    {alo ahi : I → ℤ} {blo bhi : J → ℤ} {clo chi : K → ℤ}
    (hA : Separated alo ahi) (hB : Separated blo bhi) (hC : Separated clo chi)
    {p q : I × (J × K)} (hp : Relevant alo ahi blo bhi clo chi p)
    (hq : Relevant alo ahi blo bhi clo chi q)
    (heq : tripleOwner alo blo bhi clo p = tripleOwner alo blo bhi clo q) : p = q := by
  rcases p with ⟨i, j, k⟩
  rcases q with ⟨i', j', k'⟩
  change alo i ≤ chi k - blo j ∧ clo k - bhi j ≤ ahi i at hp
  change alo i' ≤ chi k' - blo j' ∧ clo k' - bhi j' ≤ ahi i' at hq
  unfold tripleOwner at heq
  dsimp only at heq
  by_cases h : alo i < clo k - bhi j
  · by_cases h' : alo i' < clo k' - bhi j'
    · simp only [if_pos h, if_pos h'] at heq
      have hjk : (j, k) = (j', k') := Sum.inl.inj heq
      have hj := congrArg Prod.fst hjk
      have hk := congrArg Prod.snd hjk
      dsimp only at hj hk
      subst j'
      subst k'
      have hi : i = i' := interval_unique hA (by omega) hp.2 (by omega) hq.2
      subst i'
      rfl
    · simp [h, h'] at heq
  · by_cases h' : alo i' < clo k' - bhi j'
    · simp [h, h'] at heq
    · simp only [if_neg h, if_neg h'] at heq
      have he := Sum.inr.inj heq
      have hi := congrArg Prod.fst he
      dsimp only at hi
      subst i'
      have ho := congrArg Prod.snd he
      dsimp only at ho
      have hOverlap : Overlap (fun j => alo i + blo j) (fun j => alo i + bhi j) clo chi (j, k) := by
        constructor <;> dsimp only <;> omega
      have hOverlap' : Overlap (fun j => alo i + blo j) (fun j => alo i + bhi j) clo chi (j', k') := by
        constructor <;> dsimp only <;> omega
      have hjk := overlapOwner_injective (separated_shift hB (alo i)) hC hOverlap hOverlap' ho
      cases hjk
      rfl

/-- Exact O(m²) bound, allowing different numbers of bands on each side. -/
theorem relevant_card_le [Fintype I] [Fintype J] [Fintype K]
    {alo ahi : I → ℤ} {blo bhi : J → ℤ} {clo chi : K → ℤ}
    (hA : Separated alo ahi) (hB : Separated blo bhi) (hC : Separated clo chi) :
    Fintype.card {p : I × (J × K) // Relevant alo ahi blo bhi clo chi p} ≤
      Fintype.card J * Fintype.card K +
        Fintype.card I * (Fintype.card J + Fintype.card K) := by
  let f : {p : I × (J × K) // Relevant alo ahi blo bhi clo chi p} →
      (J × K) ⊕ (I × (J ⊕ K)) := fun p => tripleOwner alo blo bhi clo p.val
  have hinj : Function.Injective f := by
    intro p q h
    exact Subtype.ext (tripleOwner_injective hA hB hC p.property q.property h)
  simpa only [Fintype.card_sum, Fintype.card_prod] using Fintype.card_le_of_injective f hinj

/-- Every exact equation in the input interval hulls survives band filtering. -/
theorem exact_equation_relevant
    {alo ahi : I → ℤ} {blo bhi : J → ℤ} {clo chi : K → ℤ}
    {i : I} {j : J} {k : K} {a b c : ℤ}
    (ha : alo i ≤ a ∧ a ≤ ahi i) (hb : blo j ≤ b ∧ b ≤ bhi j)
    (hc : clo k ≤ c ∧ c ≤ chi k) (heq : a + b = c) :
    Relevant alo ahi blo bhi clo chi (i, j, k) := by
  constructor <;> dsimp only <;> omega

end ThreeSum.Bands
