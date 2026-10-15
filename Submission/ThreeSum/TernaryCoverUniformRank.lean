import Submission.ThreeSum.HashFamily
import Submission.ThreeSum.TernaryCoverRelations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Uniform prescribed hashes at the actual feature rank

An independent basis is selected from the actual hash rows.  The full event
is contained in the prescribed event for that basis.  Row rank equals the
dimension of the actual column span through the exact annihilator identity.
-/

noncomputable section
namespace ThreeSum.TernaryCoverUniformRank

open Finset TernaryCoverRelations
open scoped BigOperators

variable {K σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]

def columnSpan {d : ℕ} (v : Fin d → σ → K) : Submodule K (Fin d → K) :=
  Submodule.span K (Set.range fun i => fun j => v j i)

theorem mem_relationSpace_columnSpan {d : ℕ} (v : Fin d → σ → K) (a : Fin d → K) :
    a ∈ relationSpace (columnSpan v) ↔ ∀ i, ∑ j, a j * v j i = 0 := by
  change dotProductEquiv K (Fin d) a ∈ (columnSpan v).dualAnnihilator ↔ _
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro h i
    exact h _ (Submodule.subset_span (Set.mem_range_self i))
  · intro h x hx
    have hs : columnSpan v ≤ LinearMap.ker (dotProductEquiv K (Fin d) a) := by
      apply Submodule.span_le.mpr
      rintro w ⟨i, rfl⟩
      exact h i
    exact hs hx

theorem relationSpace_finrank_add {d : ℕ} (S : Submodule K (Fin d → K)) :
    Module.finrank K S + Module.finrank K (relationSpace S) = d := by
  let e := dotProductEquiv K (Fin d)
  have hdim := LinearEquiv.finrank_eq (e.symm.submoduleMap S.dualAnnihilator)
  have heq : S.dualAnnihilator.map e.symm.toLinearMap = relationSpace S := by
    simpa [relationSpace, e] using S.dualAnnihilator.map_equiv_eq_comap_symm e.symm
  rw [heq] at hdim
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq S
  rw [hdim] at h
  simpa using h

theorem row_rank_eq_column_rank {d : ℕ} (v : Fin d → σ → K) :
    Module.finrank K (Submodule.span K (Set.range v)) = Module.finrank K (columnSpan v) := by
  have hker : LinearMap.ker (Fintype.linearCombination K v) = relationSpace (columnSpan v) := by
    ext a
    rw [LinearMap.mem_ker, mem_relationSpace_columnSpan]
    rw [funext_iff]
    simp [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hr := LinearMap.finrank_range_add_finrank_ker (Fintype.linearCombination K v)
  rw [Fintype.range_linearCombination, hker] at hr
  have hc := relationSpace_finrank_add (columnSpan v)
  have hd : Module.finrank K (Fin d → K) = d := by simp
  rw [hd] at hr
  omega

variable [Fintype K] [DecidableEq K]

def prescribedEvent {d : ℕ} (v : Fin d → σ → K) (target : Fin d → K) : Finset (σ → K) :=
  univ.filter fun w => ∀ j, HashFamily.hashMap v w j = target j

theorem prescribedEvent_rank_bound {d : ℕ} (v : Fin d → σ → K) (target : Fin d → K) :
    Fintype.card K ^ Module.finrank K (columnSpan v) * (prescribedEvent v target).card ≤
      Fintype.card (σ → K) := by
  classical
  let S := Submodule.span K (Set.range v)
  let r := Module.finrank K S
  obtain ⟨f, hf, _, hind⟩ := Submodule.exists_fun_fin_finrank_span_eq K (Set.range v)
  let pick : Fin r → Fin d := fun i => Classical.choose (hf i)
  have hpick (i : Fin r) : v (pick i) = f i := Classical.choose_spec (hf i)
  let target' : Fin r → K := fun i => target (pick i)
  let basisEvent : Finset (σ → K) := univ.filter fun w => HashFamily.hashMap f w = target'
  have hsub : prescribedEvent v target ⊆ basisEvent := by
    intro w hw
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    funext i
    have hi := (mem_filter.mp hw).2 (pick i)
    change (∑ j, f i j * w j) = target (pick i)
    rw [← hpick]
    exact hi
  have hb : Fintype.card K ^ r * basisEvent.card = Fintype.card (σ → K) := by
    simpa [basisEvent, r, S] using HashFamily.hash_fiber_card hind target'
  have hr : r = Module.finrank K (columnSpan v) := row_rank_eq_column_rank v
  rw [← hr]
  exact (Nat.mul_le_mul_left _ (card_le_card hsub)).trans_eq hb

end ThreeSum.TernaryCoverUniformRank
