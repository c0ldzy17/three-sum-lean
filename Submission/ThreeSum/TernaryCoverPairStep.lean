import Submission.ThreeSum.TernaryCoverRankFibers
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # One exact paired rank step

The vertical kernel of a fixed subspace of `X × (K × K)` is a subspace of
`K × K`.  Its dimension is exactly the rank increment after the preceding
coordinates are fixed.  All completion coefficients are chosen from this
fixed kernel, independently of the particular preceding words.
-/

noncomputable section
namespace ThreeSum.TernaryCoverPairStep

open Finset TernaryCoverRankFibers

variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]

def vertical (S : Submodule K (X × (K × K))) : Submodule K (K × K) :=
  S.comap (LinearMap.inr K X (K × K))

def prefixSpace (S : Submodule K (X × (K × K))) : Submodule K X :=
  S.map (LinearMap.fst K X (K × K))

def prefixMap (S : Submodule K (X × (K × K))) : S →ₗ[K] X :=
  (LinearMap.fst K X (K × K)).comp S.subtype

def verticalMap (S : Submodule K (X × (K × K))) : vertical S →ₗ[K] S where
  toFun v := ⟨(0, v.val), v.property⟩
  map_add' a b := by apply Subtype.ext; ext <;> simp
  map_smul' a b := by apply Subtype.ext; simp

theorem verticalMap_injective (S : Submodule K (X × (K × K))) :
    Function.Injective (verticalMap S) := by
  intro a b h
  apply Subtype.ext
  exact congrArg (fun v : S => v.val.2) h

theorem verticalMap_range (S : Submodule K (X × (K × K))) :
    LinearMap.range (verticalMap S) = LinearMap.ker (prefixMap S) := by
  ext s
  constructor
  · rintro ⟨v, rfl⟩
    rfl
  · intro hs
    have hx : s.val.1 = 0 := hs
    let v : vertical S := ⟨s.val.2, by
      change (0, s.val.2) ∈ S
      have he : (0, s.val.2) = s.val := Prod.ext hx.symm rfl
      rw [he]
      exact s.property⟩
    refine ⟨v, ?_⟩
    apply Subtype.ext
    exact Prod.ext hx.symm rfl

theorem prefixMap_range (S : Submodule K (X × (K × K))) :
    LinearMap.range (prefixMap S) = prefixSpace S := by
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s.val, s.property, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, rfl⟩

theorem rank_increment [Module.Finite K X] (S : Submodule K (X × (K × K))) :
    Module.finrank K (prefixSpace S) + Module.finrank K (vertical S) = Module.finrank K S := by
  have h := LinearMap.finrank_range_add_finrank_ker (prefixMap S)
  have hv := LinearMap.finrank_range_of_inj (verticalMap_injective S)
  rw [verticalMap_range] at hv
  rw [prefixMap_range, hv] at h
  exact h

variable {E Z ι : Type*} [Fintype E] [Fintype Z] [Fintype ι] [DecidableEq K]

def pairedSet (left right : E → ι → K) (prior : Z → ι → X)
    (S : Submodule K (X × (K × K))) : Finset (Z × E) := by
  classical
  exact univ.filter fun ze => ∀ i, (prior ze.1 i, (left ze.2 i, right ze.2 i)) ∈ S

def priorSet (prior : Z → ι → X) (S : Submodule K (X × (K × K))) : Finset Z := by
  classical
  exact univ.filter fun z => ∀ i, prior z i ∈ prefixSpace S

theorem pairedSet_prior (left right : E → ι → K) (prior : Z → ι → X)
    (S : Submodule K (X × (K × K))) {ze : Z × E}
    (h : ze ∈ pairedSet left right prior S) : ze.1 ∈ priorSet prior S := by
  classical
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  intro i
  exact ⟨(prior ze.1 i, (left ze.2 i, right ze.2 i)), (mem_filter.mp h).2 i, rfl⟩

theorem pair_step_count (left right : E → ι → K) (prior : Z → ι → X) (P : ℕ)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hE : Fintype.card E ≤ P ^ 2)
    (hprojection : ∀ β γ : K, (β ≠ 0 ∨ γ ≠ 0) → ∀ q : ι → K,
      (projectionFiber left right β γ q).card ≤ P)
    (S : Submodule K (X × (K × K))) :
    (pairedSet left right prior S).card ≤
      (priorSet prior S).card * P ^ Module.finrank K (vertical S) := by
  classical
  have hfiber (z : Z) :
      ((pairedSet left right prior S).filter fun ze => ze.1 = z).card ≤
        P ^ Module.finrank K (vertical S) := by
    let F := (pairedSet left right prior S).filter fun ze => ze.1 = z
    change F.card ≤ _
    by_cases hz : F.card = 0
    · rw [hz]
      exact Nat.zero_le _
    obtain ⟨ze0, hze0⟩ := card_pos.mp (Nat.pos_of_ne_zero hz)
    let offset : ι → K × K := fun i => (left ze0.2 i, right ze0.2 i)
    have hin : ∀ ze ∈ F, ze.2 ∈ affineFiber left right (vertical S) offset := by
      intro ze hze
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      intro i
      have hz0 := (mem_filter.mp hze0).2
      have hzz := (mem_filter.mp hze).2
      have ha := (mem_filter.mp (mem_filter.mp hze).1).2 i
      have hb := (mem_filter.mp (mem_filter.mp hze0).1).2 i
      have hh := S.sub_mem ha hb
      change (0, (left ze.2 i, right ze.2 i) - offset i) ∈ S
      change (prior ze.1 i - prior ze0.1 i,
        (left ze.2 i, right ze.2 i) - (left ze0.2 i, right ze0.2 i)) ∈ S at hh
      rw [hzz, hz0, sub_self] at hh
      exact hh
    have hi : F.card ≤ (affineFiber left right (vertical S) offset).card := by
      apply card_le_card_of_injOn Prod.snd hin
      intro a ha b hb heq
      exact Prod.ext ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm) heq
    exact hi.trans (affineFiber_card_le_pow_finrank left right P hinj hE hprojection _ _)
  calc
    _ = ∑ z ∈ priorSet prior S,
        ((pairedSet left right prior S).filter fun ze => ze.1 = z).card :=
      card_eq_sum_card_fiberwise (fun ze hze => pairedSet_prior left right prior S hze)
    _ ≤ ∑ _z ∈ priorSet prior S, P ^ Module.finrank K (vertical S) :=
      sum_le_sum (fun z _ => hfiber z)
    _ = _ := by simp

end ThreeSum.TernaryCoverPairStep
