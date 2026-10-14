import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Conditional paired completions in an affine subspace

For a fixed proper subspace of `K × K`, one nonzero annihilating scalar
projection is chosen once for that subspace.  The same coefficients constrain
every word coordinate.  Thus a conditional rank-one completion bound does
not enumerate arbitrary field coefficients and incurs no extra field-size
factor.  This lemma is separate from the full tuple recursion.
-/

noncomputable section
namespace ThreeSum.TernaryCoverRankFibers

open Finset

variable {K : Type*} [Field K]

theorem exists_annihilating_projection (V : Submodule K (K × K)) (hV : V ≠ ⊤) :
    ∃ β γ : K, (β ≠ 0 ∨ γ ≠ 0) ∧ ∀ v ∈ V, β * v.1 + γ * v.2 = 0 := by
  have hAnn : V.dualAnnihilator ≠ ⊥ := by
    intro h
    exact hV (Submodule.dualAnnihilator_eq_bot_iff.mp h)
  obtain ⟨φ, hφ, hφne⟩ := V.dualAnnihilator.ne_bot_iff.mp hAnn
  have heval (v : K × K) : φ v = v.1 * φ (1,0) + v.2 * φ (0,1) := by
    have heq : v = v.1 • (1,0) + v.2 • (0,1) := by ext <;> simp
    rw [heq, map_add, map_smul, map_smul]
    simp
  refine ⟨φ (1,0), φ (0,1), ?_, ?_⟩
  · by_contra! hz
    apply hφne
    apply LinearMap.ext
    intro v
    change φ v = 0
    rw [heval v, hz.1, hz.2]
    simp
  · intro v hv
    have hz := (Submodule.mem_dualAnnihilator φ).mp hφ v hv
    rw [heval] at hz
    simpa [mul_comm] using hz

variable {E ι : Type*} [Fintype E] [Fintype ι] [DecidableEq K]

def projectionFiber (left right : E → ι → K) (β γ : K) (q : ι → K) : Finset E :=
  univ.filter fun e => ∀ i, β * left e i + γ * right e i = q i

def affineFiber (left right : E → ι → K) (V : Submodule K (K × K))
    (offset : ι → K × K) : Finset E := by
  classical
  exact univ.filter fun e => ∀ i, (left e i, right e i) - offset i ∈ V

/-- The annihilator is selected using only the fixed conditional subspace.
The provided projection-fiber cap is applied once, with that same functional
on every coordinate. -/
theorem affineFiber_card_le_of_proper (left right : E → ι → K) (P : ℕ)
    (hprojection : ∀ β γ : K, (β ≠ 0 ∨ γ ≠ 0) → ∀ q : ι → K,
      (projectionFiber left right β γ q).card ≤ P)
    (V : Submodule K (K × K)) (hV : V ≠ ⊤) (offset : ι → K × K) :
    (affineFiber left right V offset).card ≤ P := by
  classical
  obtain ⟨β, γ, hnonzero, hann⟩ := exists_annihilating_projection V hV
  let q : ι → K := fun i => β * (offset i).1 + γ * (offset i).2
  have hsub : affineFiber left right V offset ⊆ projectionFiber left right β γ q := by
    intro e he
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    intro i
    have h := hann ((left e i, right e i) - offset i) ((mem_filter.mp he).2 i)
    change β * (left e i - (offset i).1) + γ * (right e i - (offset i).2) = 0 at h
    dsimp [q]
    linear_combination h
  exact (card_le_card hsub).trans (hprojection β γ hnonzero q)

/-- A rank-zero conditional subspace fixes both endpoint words. -/
theorem affineFiber_card_le_one (left right : E → ι → K)
    (hinj : Function.Injective (fun e => (left e, right e))) (offset : ι → K × K) :
    (affineFiber left right (⊥ : Submodule K (K × K)) offset).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro e he f hf
  apply hinj
  have hpair (i : ι) : (left e i, right e i) = (left f i, right f i) := by
    have ha := (mem_filter.mp he).2 i
    have hb := (mem_filter.mp hf).2 i
    have ha' : (left e i, right e i) = offset i := sub_eq_zero.mp ha
    have hb' : (left f i, right f i) = offset i := sub_eq_zero.mp hb
    exact ha'.trans hb'.symm
  exact Prod.ext (funext fun i => congrArg Prod.fst (hpair i))
    (funext fun i => congrArg Prod.snd (hpair i))

/-- Conditional rank increments zero, one, and two cost respectively one,
`P`, and `P²` completions.  This includes the full two-dimensional fiber. -/
theorem affineFiber_card_le_pow_finrank (left right : E → ι → K) (P : ℕ)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hE : Fintype.card E ≤ P ^ 2)
    (hprojection : ∀ β γ : K, (β ≠ 0 ∨ γ ≠ 0) → ∀ q : ι → K,
      (projectionFiber left right β γ q).card ≤ P)
    (V : Submodule K (K × K)) (offset : ι → K × K) :
    (affineFiber left right V offset).card ≤ P ^ Module.finrank K V := by
  classical
  have hdim : Module.finrank K V ≤ 2 := by
    simpa using Submodule.finrank_le V
  have hcases : Module.finrank K V = 0 ∨ Module.finrank K V = 1 ∨ Module.finrank K V = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · have hV : V = ⊥ := Submodule.finrank_eq_zero.mp h0
    rw [h0, hV, pow_zero]
    exact affineFiber_card_le_one left right hinj offset
  · have hV : V ≠ ⊤ := by
      intro heq
      have h := h1
      rw [heq] at h
      norm_num at h
    rw [h1, pow_one]
    exact affineFiber_card_le_of_proper left right P hprojection V hV offset
  · rw [h2]
    exact (card_le_card (filter_subset ..)).trans (by simpa using hE)

end ThreeSum.TernaryCoverRankFibers
