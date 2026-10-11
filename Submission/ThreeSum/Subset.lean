import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Lean.Elab.Tactic.Omega
import Aesop

/-!
# Exact subset identities used by the proposed 3SUM algorithm

This module proves the algebraic identities, rather than taking the claimed
algorithm or its running time as an assumption.  `zeta` is the ordinary finite
subset sum; `mobius` is its signed inverse.  The fixed-cardinality specialization
is the identity used by the repeated histogram construction.
-/

namespace ThreeSum.Subset

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

/-- Ordinary zeta transform on the finite-subset lattice. -/
def zeta (f : Finset α → ℤ) (q : Finset α) : ℤ :=
  ∑ s ∈ q.powerset, f s

/-- Signed Möbius transform on the finite-subset lattice. -/
def mobius (f : Finset α → ℤ) (q : Finset α) : ℤ :=
  ∑ s ∈ q.powerset, (-1 : ℤ) ^ (q.card - s.card) * f s

theorem zeta_insert (f : Finset α → ℤ) {q : Finset α} {a : α}
    (ha : a ∉ q) :
    zeta f (insert a q) = zeta f q + zeta (fun s => f (insert a s)) q := by
  exact Finset.sum_powerset_insert ha f

theorem mobius_congr (q : Finset α) {f g : Finset α → ℤ}
    (h : ∀ s ⊆ q, f s = g s) : mobius f q = mobius g q := by
  apply Finset.sum_congr rfl
  intro s hs
  rw [h s (Finset.mem_powerset.mp hs)]

theorem mobius_add (f g : Finset α → ℤ) (q : Finset α) :
    mobius (fun s => f s + g s) q = mobius f q + mobius g q := by
  simp only [mobius, mul_add, Finset.sum_add_distrib]

theorem mobius_insert (f : Finset α → ℤ) {q : Finset α} {a : α}
    (ha : a ∉ q) :
    mobius f (insert a q) =
      mobius (fun s => f (insert a s)) q - mobius f q := by
  unfold mobius
  rw [Finset.sum_powerset_insert ha]
  have hleft :
      (∑ s ∈ q.powerset, (-1 : ℤ) ^ ((insert a q).card - s.card) * f s) =
      -(∑ s ∈ q.powerset, (-1 : ℤ) ^ (q.card - s.card) * f s) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    have hcard := Finset.card_le_card (Finset.mem_powerset.mp hs)
    have hexp : (insert a q).card - s.card = (q.card - s.card) + 1 := by
      rw [Finset.card_insert_of_notMem ha]
      omega
    rw [hexp, pow_succ]
    ring
  have hright :
      (∑ s ∈ q.powerset,
        (-1 : ℤ) ^ ((insert a q).card - (insert a s).card) * f (insert a s)) =
      ∑ s ∈ q.powerset, (-1 : ℤ) ^ (q.card - s.card) * f (insert a s) := by
    apply Finset.sum_congr rfl
    intro s hs
    have has : a ∉ s := fun h => ha ((Finset.mem_powerset.mp hs) h)
    rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem has,
      Nat.add_sub_add_right]
  rw [hleft, hright]
  ring

/-- Exact Möbius inversion. The proof is induction on the finite output set. -/
theorem mobius_zeta (f : Finset α → ℤ) (q : Finset α) :
    mobius (zeta f) q = f q := by
  induction q using Finset.induction_on generalizing f with
  | empty => simp [mobius, zeta]
  | @insert a q ha ih =>
      rw [mobius_insert (zeta f) ha]
      have hchange :
          mobius (fun s => zeta f (insert a s)) q =
          mobius (fun s => zeta f s + zeta (fun t => f (insert a t)) s) q := by
        apply mobius_congr
        intro s hs
        exact zeta_insert f (fun h => ha (hs h))
      rw [hchange, mobius_add, ih f, ih (fun s => f (insert a s))]
      ring

/-- Union convolution, before the fixed-cardinality disjointness reduction. -/
def unionConvolution (f g : Finset α → ℤ) (q : Finset α) : ℤ :=
  ∑ s ∈ q.powerset, ∑ v ∈ q.powerset,
    if s ∪ v = q then f s * g v else 0

private theorem powerset_subset_of_subset {u q : Finset α} (h : u ⊆ q) :
    u.powerset ⊆ q.powerset := by
  intro s hs
  exact Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hs).trans h)

private theorem unionConvolution_extend (f g : Finset α → ℤ)
    {u q : Finset α} (hu : u ⊆ q) :
    unionConvolution f g u =
      ∑ s ∈ q.powerset, ∑ v ∈ q.powerset,
        if s ∪ v = u then f s * g v else 0 := by
  have hp := powerset_subset_of_subset hu
  unfold unionConvolution
  calc
    _ = ∑ s ∈ u.powerset, ∑ v ∈ q.powerset,
          if s ∪ v = u then f s * g v else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_subset hp
      intro v hv hvu
      have hne : s ∪ v ≠ u := by
        intro he
        apply hvu
        apply Finset.mem_powerset.mpr
        rw [← he]
        exact Finset.subset_union_right
      simp only [hne, ite_false]
    _ = _ := by
      apply Finset.sum_subset hp
      intro s hs hsu
      apply Finset.sum_eq_zero
      intro v hv
      have hne : s ∪ v ≠ u := by
        intro he
        apply hsu
        apply Finset.mem_powerset.mpr
        rw [← he]
        exact Finset.subset_union_left
      simp only [hne, ite_false]

theorem zeta_unionConvolution (f g : Finset α → ℤ) (q : Finset α) :
    zeta (unionConvolution f g) q = zeta f q * zeta g q := by
  unfold zeta
  calc
    _ = ∑ u ∈ q.powerset, ∑ s ∈ q.powerset, ∑ v ∈ q.powerset,
          if s ∪ v = u then f s * g v else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      exact unionConvolution_extend f g (Finset.mem_powerset.mp hu)
    _ = ∑ s ∈ q.powerset, ∑ v ∈ q.powerset, ∑ u ∈ q.powerset,
          if s ∪ v = u then f s * g v else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.sum_comm]
    _ = ∑ s ∈ q.powerset, ∑ v ∈ q.powerset, f s * g v := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro v hv
      have huv : s ∪ v ∈ q.powerset :=
        Finset.mem_powerset.mpr
          (Finset.union_subset (Finset.mem_powerset.mp hs) (Finset.mem_powerset.mp hv))
      rw [Finset.sum_eq_single (s ∪ v)]
      · simp
      · intro u hu hne
        simp only [Ne.symm hne, ite_false]
      · intro h
        exact False.elim (h huv)
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm

/-- The signed product of two ordinary zeta transforms counts exact unions. -/
theorem mobius_zeta_product (f g : Finset α → ℤ) (q : Finset α) :
    mobius (fun t => zeta f t * zeta g t) q = unionConvolution f g q := by
  have heq : (fun t => zeta f t * zeta g t) = zeta (unionConvolution f g) := by
    funext t
    exact (zeta_unionConvolution f g t).symm
  rw [heq, mobius_zeta]

/-- If the input sizes add to the output size, an exact union is disjoint. -/
theorem disjoint_of_union_card {s v q : Finset α}
    (hu : s ∪ v = q) (hc : q.card = s.card + v.card) : Disjoint s v := by
  apply Finset.card_union_eq_card_add_card.mp
  simpa only [hu] using hc

/-- The single-sum disjoint subset convolution used by the algorithm. -/
def disjointConvolution (f g : Finset α → ℤ) (q : Finset α) : ℤ :=
  ∑ s ∈ q.powerset, f s * g (q \ s)

theorem unionConvolution_eq_disjointConvolution
    (f g : Finset α → ℤ) (q : Finset α) (a b : ℕ)
    (hf : ∀ s, f s ≠ 0 → s.card = a)
    (hg : ∀ v, g v ≠ 0 → v.card = b)
    (hq : q.card = a + b) :
    unionConvolution f g q = disjointConvolution f g q := by
  unfold unionConvolution disjointConvolution
  apply Finset.sum_congr rfl
  intro s hs
  have hsq := Finset.mem_powerset.mp hs
  by_cases hfs : f s = 0
  · simp [hfs]
  have hcompl : q \ s ∈ q.powerset :=
    Finset.mem_powerset.mpr Finset.sdiff_subset
  rw [Finset.sum_eq_single (q \ s)]
  · have hU : s ∪ (q \ s) = q := by
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (hx | ⟨hx, _⟩)
        · exact hsq hx
        · exact hx
      · intro hx
        by_cases hxs : x ∈ s
        · exact Or.inl hxs
        · exact Or.inr ⟨hx, hxs⟩
    simp only [hU, ite_true]
  · intro v hv hne
    by_cases hu : s ∪ v = q
    · by_cases hgv : g v = 0
      · simp [hgv]
      have hd : Disjoint s v := disjoint_of_union_card hu (by rw [hf s hfs, hg v hgv]; exact hq)
      have he : v = q \ s := by
        ext x
        simp only [Finset.mem_sdiff]
        constructor
        · intro hx
          refine ⟨?_, ?_⟩
          · rw [← hu]
            exact Finset.mem_union_right s hx
          · intro hxs
            exact Finset.disjoint_left.mp hd hxs hx
        · rintro ⟨hxq, hxs⟩
          rw [← hu] at hxq
          exact (Finset.mem_union.mp hxq).resolve_left hxs
      exact False.elim (hne he)
    · simp only [hu, ite_false]
  · intro h
    exact False.elim (h hcompl)

/-- The complete fixed-cardinality Möbius/subset-convolution identity. -/
theorem fixed_cardinality_identity
    (f g : Finset α → ℤ) (q : Finset α) (a b : ℕ)
    (hf : ∀ s, f s ≠ 0 → s.card = a)
    (hg : ∀ v, g v ≠ 0 → v.card = b)
    (hq : q.card = a + b) :
    (∑ t ∈ q.powerset, (-1 : ℤ) ^ (q.card - t.card) *
      (∑ s ∈ t.powerset, f s) * (∑ v ∈ t.powerset, g v)) =
    ∑ s ∈ q.powerset, f s * g (q \ s) := by
  have h := mobius_zeta_product f g q
  rw [unionConvolution_eq_disjointConvolution f g q a b hf hg hq] at h
  simpa only [mobius, zeta, disjointConvolution, mul_assoc] using h

/-- For histogram populations the signed expression is exactly a natural-number
count, embedded into the integers; no positivity of an intermediate box sum is
assumed. -/
theorem fixed_cardinality_identity_nat
    (f g : Finset α → ℕ) (q : Finset α) (a b : ℕ)
    (hf : ∀ s, f s ≠ 0 → s.card = a)
    (hg : ∀ v, g v ≠ 0 → v.card = b)
    (hq : q.card = a + b) :
    (∑ t ∈ q.powerset, (-1 : ℤ) ^ (q.card - t.card) *
      (∑ s ∈ t.powerset, (f s : ℤ)) * (∑ v ∈ t.powerset, (g v : ℤ))) =
    (∑ s ∈ q.powerset, f s * g (q \ s) : ℕ) := by
  have hf' : ∀ s, (f s : ℤ) ≠ 0 → s.card = a := by
    intro s hs
    apply hf s
    intro hz
    apply hs
    simp only [hz, Nat.cast_zero]
  have hg' : ∀ v, (g v : ℤ) ≠ 0 → v.card = b := by
    intro v hv
    apply hg v
    intro hz
    apply hv
    simp only [hz, Nat.cast_zero]
  have hid := fixed_cardinality_identity
    (fun s => (f s : ℤ)) (fun v => (g v : ℤ)) q a b hf' hg' hq
  simpa only [Nat.cast_sum, Nat.cast_mul] using hid

/-! ## Stored partial zeta stages -/

/-- Value after exactly the coordinates in `processed` have been zeta-transformed.
All other coordinates of `u` are still forced to be present. -/
def partialZeta (processed : Finset α) (f : Finset α → ℤ) (u : Finset α) : ℤ :=
  ∑ x ∈ (u ∩ processed).powerset, f ((u \ processed) ∪ x)

/-- One ordinary zeta addition, with the old stage read at both inputs. -/
def zetaStep (a : α) (F : Finset α → ℤ) (u : Finset α) : ℤ :=
  if a ∈ u then F u + F (u.erase a) else F u

theorem partialZeta_empty (f : Finset α → ℤ) (u : Finset α) :
    partialZeta ∅ f u = f u := by
  simp [partialZeta]

theorem partialZeta_all (f : Finset α → ℤ) (u : Finset α) :
    partialZeta u f u = zeta f u := by
  simp [partialZeta, zeta]

/-- The exact update invariant for the ordinary coordinatewise zeta DP. -/
theorem partialZeta_insert (f : Finset α → ℤ) (u processed : Finset α)
    (a : α) (ha : a ∉ processed) :
    partialZeta (insert a processed) f u =
      zetaStep a (partialZeta processed f) u := by
  by_cases hau : a ∈ u
  · have hi : u ∩ insert a processed = insert a (u ∩ processed) := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert]
      aesop
    have he : u.erase a ∩ processed = u ∩ processed := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_erase]
      aesop
    have hd : u.erase a \ processed = u \ insert a processed := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
      aesop
    have hterm (x : Finset α) :
        (u \ insert a processed) ∪ insert a x = (u \ processed) ∪ x := by
      ext b
      by_cases hba : b = a
      · subst b
        simp [hau, ha]
      · simp [hba]
    have hai : a ∉ u ∩ processed := by simp [ha]
    rw [partialZeta, hi, Finset.sum_powerset_insert hai]
    simp only [zetaStep, hau, ite_true]
    have hfirst :
        (∑ x ∈ (u ∩ processed).powerset, f ((u \ insert a processed) ∪ x)) =
        partialZeta processed f (u.erase a) := by
      simp only [partialZeta, he, hd]
    have hsecond :
        (∑ x ∈ (u ∩ processed).powerset,
          f ((u \ insert a processed) ∪ insert a x)) =
        partialZeta processed f u := by
      simp only [partialZeta, hterm]
    rw [hfirst, hsecond, add_comm]
  · have hi : u ∩ insert a processed = u ∩ processed := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert]
      aesop
    have hd : u \ insert a processed = u \ processed := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      aesop
    simp only [partialZeta, hi, hd, zetaStep, hau, ite_false]

/-- Functional specification of successive zeta table updates. This definition
states the values of the stages; it makes no claim about their RAM cost. -/
def runZeta : List α → (Finset α → ℤ) → Finset α → ℤ
  | [], f => f
  | a :: coords, f => zetaStep a (runZeta coords f)

theorem runZeta_eq_partialZeta (coords : List α) (hn : coords.Nodup)
    (f : Finset α → ℤ) (u : Finset α) :
    runZeta coords f u = partialZeta coords.toFinset f u := by
  induction coords generalizing u with
  | nil => simp [runZeta, partialZeta]
  | cons a coords ih =>
      have hparts := List.nodup_cons.mp hn
      have hnot : a ∉ coords.toFinset := by simpa using hparts.1
      have heq : runZeta coords f = partialZeta coords.toFinset f := by
        funext v
        exact ih hparts.2 v
      simp only [runZeta, List.toFinset_cons, heq]
      exact (partialZeta_insert f u coords.toFinset a hnot).symm

/-- A forced pre is read from one entry of a stored suffix-zeta stage. -/
theorem partialZeta_forced_prefix
    (f : Finset α → ℤ) (processed s₀ t : Finset α)
    (hs : Disjoint s₀ processed) (ht : t ⊆ processed) :
    partialZeta processed f (s₀ ∪ t) =
      ∑ x ∈ t.powerset, f (s₀ ∪ x) := by
  have hnot : ∀ x ∈ s₀, x ∉ processed := fun x hx hy =>
    Finset.disjoint_left.mp hs hx hy
  have hi : (s₀ ∪ t) ∩ processed = t := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    aesop
  have hd : (s₀ ∪ t) \ processed = s₀ := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hx, hp⟩
      rcases hx with hxs | hxt
      · exact hxs
      · exact False.elim (hp (ht hxt))
    · intro hx
      exact ⟨Or.inl hx, hnot x hx⟩
  simp only [partialZeta, hi, hd]

/-- Every lookup of the forced-pre formula lies in the stored downset
whenever the total pre-plus-suffix size is at most `mu`. -/
theorem forced_prefix_stays_in_downset
    (s₀ t : Finset α) (mu : ℕ) (h : s₀.card + t.card ≤ mu) :
    (s₀ ∪ t).card ≤ mu := by
  exact (Finset.card_union_le s₀ t).trans h

/-- The ordinary zeta update also reads only from that same downset. -/
theorem zetaStep_stays_in_downset
    (u : Finset α) (a : α) (mu : ℕ) (h : u.card ≤ mu) :
    (u.erase a).card ≤ mu := by
  exact (Finset.card_le_card (Finset.erase_subset a u)).trans h

/-- The original histogram with a fixed pre and a suffix-domain guard. -/
def forcedInput (f : Finset α → ℤ) (pre suffix x : Finset α) : ℤ :=
  if x ⊆ suffix then f (pre ∪ x) else 0

theorem forcedInput_cardinality
    (f : Finset α → ℤ) (pre suffix : Finset α) (a : ℕ)
    (hf : ∀ s, f s ≠ 0 → s.card = a)
    (hd : Disjoint pre suffix) :
    ∀ x, forcedInput f pre suffix x ≠ 0 → x.card = a - pre.card := by
  intro x hx
  have hxs : x ⊆ suffix := by
    by_contra h
    apply hx
    simp only [forcedInput, h, ite_false]
  have hfx : f (pre ∪ x) ≠ 0 := by
    simpa only [forcedInput, hxs, ite_true] using hx
  have hdx : Disjoint pre x := by
    apply Finset.disjoint_left.mpr
    intro b hbp hbx
    exact Finset.disjoint_left.mp hd hbp (hxs hbx)
  have hc := hf (pre ∪ x) hfx
  rw [Finset.card_union_of_disjoint hdx] at hc
  omega

theorem zeta_forcedInput
    (f : Finset α → ℤ) (pre suffix t : Finset α)
    (hd : Disjoint pre suffix) (ht : t ⊆ suffix) :
    zeta (forcedInput f pre suffix) t =
      partialZeta suffix f (pre ∪ t) := by
  rw [partialZeta_forced_prefix f suffix pre t hd ht]
  apply Finset.sum_congr rfl
  intro x hx
  have hxs := (Finset.mem_powerset.mp hx).trans ht
  simp only [forcedInput, hxs, ite_true]

/-- The restricted count used by a reporting query is obtained from the already
stored partial-zeta stages.  No extra restricted transform is postulated. -/
theorem forced_prefix_identity
    (f g : Finset α → ℤ) (prefix₁ prefix₂ suffix q : Finset α) (a b : ℕ)
    (hf : ∀ s, f s ≠ 0 → s.card = a)
    (hg : ∀ v, g v ≠ 0 → v.card = b)
    (hd₁ : Disjoint prefix₁ suffix) (hd₂ : Disjoint prefix₂ suffix)
    (hqs : q ⊆ suffix)
    (hq : q.card = (a - prefix₁.card) + (b - prefix₂.card)) :
    mobius (fun t => partialZeta suffix f (prefix₁ ∪ t) *
      partialZeta suffix g (prefix₂ ∪ t)) q =
    ∑ x ∈ q.powerset, f (prefix₁ ∪ x) * g (prefix₂ ∪ (q \ x)) := by
  let f' := forcedInput f prefix₁ suffix
  let g' := forcedInput g prefix₂ suffix
  have hprod := mobius_zeta_product f' g' q
  rw [unionConvolution_eq_disjointConvolution f' g' q
    (a - prefix₁.card) (b - prefix₂.card)
    (forcedInput_cardinality f prefix₁ suffix a hf hd₁)
    (forcedInput_cardinality g prefix₂ suffix b hg hd₂) hq] at hprod
  calc
    _ = mobius (fun t => zeta f' t * zeta g' t) q := by
      apply mobius_congr
      intro t ht
      rw [zeta_forcedInput f prefix₁ suffix t hd₁ (ht.trans hqs),
        zeta_forcedInput g prefix₂ suffix t hd₂ (ht.trans hqs)]
    _ = disjointConvolution f' g' q := hprod
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      have hxs := (Finset.mem_powerset.mp hx).trans hqs
      have hds : q \ x ⊆ suffix := Finset.sdiff_subset.trans hqs
      simp only [f', g', forcedInput, hxs, hds, ite_true]

/-! ## Prefix reporting mass -/

/-- Weighted mass of one refinement fiber. -/
def fiberMass {β γ : Type*} [DecidableEq γ]
    (domain : Finset β) (label : β → γ) (weight : β → ℕ) (value : γ) : ℕ :=
  ∑ p ∈ domain with label p = value, weight p

/-- Refinement into all allowed next labels preserves the original weighted
mass, including multiplicity. This is a finite-sum identity, not a bound assumed
from the proposed 3SUM algorithm. -/
theorem fiberMass_conservation {β γ : Type*} [DecidableEq γ]
    (domain : Finset β) (labels : Finset γ) (label : β → γ) (weight : β → ℕ)
    (hlabels : ∀ p ∈ domain, label p ∈ labels) :
    (∑ value ∈ labels, fiberMass domain label weight value) =
      ∑ p ∈ domain, weight p := by
  exact Finset.sum_fiberwise_of_maps_to hlabels weight

/-- A positive child has integer mass at least one, so the number of positive
children cannot exceed the parent's mass. -/
theorem positive_fibers_le_mass {β γ : Type*} [DecidableEq γ]
    (domain : Finset β) (labels : Finset γ) (label : β → γ) (weight : β → ℕ)
    (hlabels : ∀ p ∈ domain, label p ∈ labels) :
    (labels.filter (fun value => 0 < fiberMass domain label weight value)).card ≤
      ∑ p ∈ domain, weight p := by
  rw [← fiberMass_conservation domain labels label weight hlabels]
  calc
    _ = ∑ value ∈ labels, if 0 < fiberMass domain label weight value then 1 else 0 := by
      simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro value hvalue
      split_ifs with h
      · omega
      · exact Nat.zero_le _

/-- Revealing a block means classifying a completion by its intersection with
that block. Summing all resulting subset fibers preserves mass. -/
theorem block_refinement_conservation
    (completions : Finset (Finset α)) (block : Finset α)
    (weight : Finset α → ℕ) :
    (∑ child ∈ block.powerset,
      fiberMass completions (fun s => s ∩ block) weight child) =
      ∑ s ∈ completions, weight s := by
  apply fiberMass_conservation
  intro s hs
  exact Finset.mem_powerset.mpr Finset.inter_subset_right

/-- The algorithm visits only balanced assignments. If every completion has
exactly `h` positions in the next block, the balanced children still partition
all of the weighted mass. -/
theorem balanced_block_refinement_conservation
    (completions : Finset (Finset α)) (block : Finset α) (h : ℕ)
    (weight : Finset α → ℕ)
    (hbalanced : ∀ s ∈ completions, (s ∩ block).card = h) :
    (∑ child ∈ block.powersetCard h,
      fiberMass completions (fun s => s ∩ block) weight child) =
      ∑ s ∈ completions, weight s := by
  apply fiberMass_conservation
  intro s hs
  exact Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hbalanced s hs⟩

end ThreeSum.Subset
