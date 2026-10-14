import Submission.ThreeSum.TernaryCoverTupleCount
import Submission.ThreeSum.TernaryCoverUniformRank
import Submission.ThreeSum.TernaryCoverMoments
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Finite-alphabet paired high moments

Both moment obligations are discharged: a fixed column-span class contains
at most `P^rank` tuples, and its joint prescribed hash event has at most
`|weights|/P^rank` assignments.  The number of actual column-span classes is
bounded by the trit-matrix basis count, independently of the field size.
-/

noncomputable section
namespace ThreeSum.TernaryCoverHighMoment

open Finset TernaryCoverRankFibers TernaryCoverTupleCount
open TernaryCoverRelations TernaryCoverUniformRank TernaryCoverMoments
open scoped BigOperators

variable {K E σ : Type*} [Field K] [Fintype E] [Fintype σ] [DecidableEq σ]

def flattenPairs (k : ℕ) : (Fin k → K × K) ≃ₗ[K] (Fin (k*2) → K) where
  toFun v j := if (finProdFinEquiv.symm j).2 = 0 then
    (v (finProdFinEquiv.symm j).1).1 else (v (finProdFinEquiv.symm j).1).2
  invFun w j := (w (finProdFinEquiv (j,0)), w (finProdFinEquiv (j,1)))
  left_inv v := by
    funext j
    apply Prod.ext <;> simp
  right_inv w := by
    funext j
    obtain ⟨ab, rfl⟩ := finProdFinEquiv.surjective j
    obtain ⟨a,b⟩ := ab
    fin_cases b <;> simp
  map_add' v w := by funext j; dsimp only [Pi.add_apply]; split_ifs <;> rfl
  map_smul' a v := by funext j; dsimp only [Pi.smul_apply]; split_ifs <;> rfl

@[simp] theorem flattenPairs_apply (k : ℕ) (v : Fin k → K × K) (j : Fin (k*2)) :
    flattenPairs k v j = if (finProdFinEquiv.symm j).2 = 0 then
      (v (finProdFinEquiv.symm j).1).1 else (v (finProdFinEquiv.symm j).1).2 := rfl

@[simp] theorem flattenPairs_prod_zero (k : ℕ) (v : Fin k → K × K) (j : Fin k) :
    flattenPairs k v (finProdFinEquiv (j,0)) = (v j).1 := by
  rw [flattenPairs_apply, Equiv.symm_apply_apply]
  rfl

@[simp] theorem flattenPairs_prod_one (k : ℕ) (v : Fin k → K × K) (j : Fin k) :
    flattenPairs k v (finProdFinEquiv (j,1)) = (v j).2 := by
  rw [flattenPairs_apply, Equiv.symm_apply_apply]
  simp

def castWord (v : σ → Fin 3) : σ → K := fun i => ((v i).val : K)

def rows (left right : E → σ → Fin 3) {k : ℕ} (es : Fin k → E) : Fin (k*2) → σ → K :=
  fun j i => flattenPairs k (tupleColumn (fun e => castWord (left e)) (fun e => castWord (right e)) es i) j

def digitColumns (left right : E → σ → Fin 3) {k : ℕ} (es : Fin k → E) :
    σ → Fin (k*2) → Fin 3 :=
  fun i j => if (finProdFinEquiv.symm j).2 = 0 then
    left (es (finProdFinEquiv.symm j).1) i else right (es (finProdFinEquiv.symm j).1) i

theorem columnSpan_rows (left right : E → σ → Fin 3) {k : ℕ} (es : Fin k → E) :
    columnSpan (rows (K := K) left right es) =
      Submodule.span K (Set.range fun i => digitVector (K := K) (digitColumns left right es i)) := by
  congr 2
  funext i j
  unfold rows
  rw [flattenPairs_apply]
  unfold tupleColumn castWord digitColumns digitVector
  dsimp only
  split_ifs <;> rfl

def classify (left right : E → σ → Fin 3) {k : ℕ} (es : Fin k → E) :
    (possibleSpans K (k*2)) :=
  ⟨columnSpan (rows left right es), by
    rw [columnSpan_rows]
    exact span_mem_possibleSpans (digitColumns left right es)⟩

variable [Fintype K] [DecidableEq K]

def rawEvents (left right : E → σ → Fin 3) (a b : K) (e : E) : Finset (σ → K) :=
  univ.filter fun w => (∑ i, castWord (left e) i * w i) = a ∧
    (∑ i, castWord (right e) i * w i) = b

theorem jointEvent_rows (left right : E → σ → Fin 3) (a b : K) {k : ℕ} (es : Fin k → E) :
    jointEvent (rawEvents (K := K) left right a b) es =
      prescribedEvent (rows left right es) (flattenPairs k (fun _ => (a,b))) := by
  classical
  ext w
  simp only [jointEvent, rawEvents, prescribedEvent, mem_filter, mem_univ, true_and]
  constructor
  · intro h j
    obtain ⟨ab, rfl⟩ := finProdFinEquiv.surjective j
    obtain ⟨e,t⟩ := ab
    have ht : t = 0 ∨ t = 1 := by omega
    rcases ht with ht | ht
    · subst t
      simpa only [HashFamily.hashMap_apply, rows, flattenPairs_prod_zero, tupleColumn] using (h e).1
    · subst t
      simpa only [HashFamily.hashMap_apply, rows, flattenPairs_prod_one, tupleColumn] using (h e).2
  · intro h e
    constructor
    · simpa only [HashFamily.hashMap_apply, rows, flattenPairs_prod_zero, tupleColumn] using h (finProdFinEquiv (e,0))
    · simpa only [HashFamily.hashMap_apply, rows, flattenPairs_prod_one, tupleColumn] using h (finProdFinEquiv (e,1))

theorem raw_high_moment (left right : E → σ → Fin 3)
    (hinj : Function.Injective (fun e => (castWord (K := K) (left e), castWord (K := K) (right e))))
    (hE : Fintype.card E ≤ Fintype.card K ^ 2)
    (hprojection : ∀ β γ : K, (β ≠ 0 ∨ γ ≠ 0) → ∀ q : σ → K,
      (projectionFiber (fun e => castWord (K := K) (left e))
        (fun e => castWord (K := K) (right e)) β γ q).card ≤ Fintype.card K)
    (k : ℕ) (a b : K) :
    (∑ w, HashFamily.incidenceCount (rawEvents left right a b) w ^ k) ≤
      3 ^ (4*k^2) * Fintype.card (σ → K) := by
  classical
  let C := possibleSpans K (k*2)
  let rank : C → ℕ := fun c => Module.finrank K c.val
  have hcount (c : C) :
      (univ.filter fun es : Fin k → E => classify left right es = c).card ≤ Fintype.card K ^ rank c := by
    let S := c.val.comap (flattenPairs (K := K) k).toLinearMap
    have hsub : (univ.filter fun es : Fin k → E => classify left right es = c) ⊆
        tupleSet (fun e => castWord (K := K) (left e)) (fun e => castWord (K := K) (right e)) k S := by
      intro es hes
      have hc := congrArg Subtype.val (mem_filter.mp hes).2
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      intro i
      change flattenPairs k (tupleColumn (fun e => castWord (K := K) (left e))
        (fun e => castWord (K := K) (right e)) es i) ∈ c.val
      rw [← hc]
      exact Submodule.subset_span (Set.mem_range_self i)
    have hr : Module.finrank K c.val = Module.finrank K S := by
      have h := LinearEquiv.finrank_eq ((flattenPairs (K := K) k).symm.submoduleMap c.val)
      have heq : c.val.map (flattenPairs (K := K) k).symm.toLinearMap = S :=
        c.val.map_equiv_eq_comap_symm (flattenPairs (K := K) k).symm
      rwa [heq] at h
    exact (card_le_card hsub).trans (by
      simpa [rank, ← hr] using tupleSet_card_le
        (fun e => castWord (K := K) (left e)) (fun e => castWord (K := K) (right e))
        (Fintype.card K) hinj hE hprojection k S)
  have hhash (es : Fin k → E) :
      Fintype.card K ^ rank (classify left right es) * (jointEvent (rawEvents left right a b) es).card ≤
        Fintype.card (σ → K) := by
    rw [jointEvent_rows]
    exact prescribedEvent_rank_bound (rows left right es) _
  have h := moment_bound_of_classes (rawEvents left right a b) k (Fintype.card K)
    Fintype.card_pos (classify left right) rank hcount hhash
  have hC : Fintype.card C ≤ 3 ^ (4*k^2) := by
    dsimp [C]
    rw [Fintype.card_coe]
    convert possibleSpans_card (K := K) (k*2) using 1 <;> congr 1 <;> ring
  exact h.trans (Nat.mul_le_mul_right _ hC)

end ThreeSum.TernaryCoverHighMoment
