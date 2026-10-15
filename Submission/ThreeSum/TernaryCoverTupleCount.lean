import Submission.ThreeSum.TernaryCoverPairStep
import Mathlib.Data.Fin.Tuple.Basic

/-! # Exact fixed-subspace paired-tuple count

The induction fixes the relation subspace first.  At each paired step its
vertical kernel determines the single common projection imposed on all word
coordinates.  Consequently no arbitrary field coefficient is enumerated.
-/

noncomputable section
namespace ThreeSum.TernaryCoverTupleCount

open Finset TernaryCoverRankFibers TernaryCoverPairStep

variable {K E ι : Type*} [Field K] [Fintype E] [Fintype ι] [DecidableEq K]

def tupleColumn (left right : E → ι → K) {n : ℕ} (es : Fin n → E) (i : ι) : Fin n → K × K :=
  fun j => (left (es j) i, right (es j) i)

def tupleSet (left right : E → ι → K) (n : ℕ) (S : Submodule K (Fin n → K × K)) :
    Finset (Fin n → E) := by
  classical
  exact univ.filter fun es => ∀ i, tupleColumn left right es i ∈ S

def splitRows (n : ℕ) : (Fin (n+1) → K × K) ≃ₗ[K] ((Fin n → K × K) × (K × K)) where
  toFun f := (Fin.tail f, f 0)
  invFun p := Fin.cons p.2 p.1
  left_inv f := Fin.cons_self_tail f
  right_inv p := by simp
  map_add' f g := rfl
  map_smul' a f := rfl

theorem tuple_split_card (left right : E → ι → K) (n : ℕ)
    (S : Submodule K (Fin (n+1) → K × K)) :
    (tupleSet left right (n+1) S).card =
      (pairedSet left right (tupleColumn left right)
        (S.map (splitRows (K := K) n).toLinearMap)).card := by
  classical
  apply card_bij (fun es _ => (Fin.tail es, es 0))
  · intro es hes
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    intro i
    exact ⟨tupleColumn left right es i, (mem_filter.mp hes).2 i, rfl⟩
  · intro es _ fs _ he
    have ht := congrArg Prod.fst he
    have hh := congrArg Prod.snd he
    change Fin.tail es = Fin.tail fs at ht
    change es 0 = fs 0 at hh
    rw [← Fin.cons_self_tail es, ← Fin.cons_self_tail fs, ht, hh]
  · intro ze hze
    refine ⟨Fin.cons ze.2 ze.1, ?_, ?_⟩
    · apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      intro i
      obtain ⟨v, hv, he⟩ := (mem_filter.mp hze).2 i
      have heq : v = tupleColumn left right (Fin.cons ze.2 ze.1) i := by
        apply (splitRows (K := K) n).injective
        change (Fin.tail v, v 0) = (tupleColumn left right ze.1 i,
          (left ze.2 i, right ze.2 i)) at he
        exact he
      exact heq ▸ hv
    · simp

/-- Every tuple whose actual columns lie in one fixed relation subspace
has at most `P^dim(S)` completions.  The projection-fiber cap is the only
local graph counting input; it includes all nonzero scalar projections. -/
theorem tupleSet_card_le (left right : E → ι → K) (P : ℕ)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hE : Fintype.card E ≤ P ^ 2)
    (hprojection : ∀ β γ : K, (β ≠ 0 ∨ γ ≠ 0) → ∀ q : ι → K,
      (projectionFiber left right β γ q).card ≤ P) :
    ∀ n (S : Submodule K (Fin n → K × K)),
      (tupleSet left right n S).card ≤ P ^ Module.finrank K S := by
  classical
  intro n
  induction n with
  | zero =>
    intro S
    have hr : Module.finrank K S = 0 := by
      have h := Submodule.finrank_le S
      have hamb : Module.finrank K (Fin 0 → K × K) = 0 := by
        rw [Module.finrank_pi_fintype]
        simp
      rw [hamb] at h
      omega
    rw [hr, pow_zero]
    exact (card_le_card (filter_subset ..)).trans_eq (by simp)
  | succ n ih =>
    intro S
    let T := S.map (splitRows (K := K) n).toLinearMap
    have hdim : Module.finrank K S = Module.finrank K T :=
      LinearEquiv.finrank_eq (Submodule.equivMapOfInjective
        (splitRows (K := K) n).toLinearMap (splitRows (K := K) n).injective S)
    rw [tuple_split_card]
    change (pairedSet left right (tupleColumn left right) T).card ≤ _
    calc
      _ ≤ (priorSet (tupleColumn left right) T).card * P ^ Module.finrank K (vertical T) :=
        pair_step_count left right (tupleColumn left right) P hinj hE hprojection T
      _ ≤ P ^ Module.finrank K (prefixSpace T) * P ^ Module.finrank K (vertical T) :=
        Nat.mul_le_mul_right _ (ih (prefixSpace T))
      _ = P ^ Module.finrank K S := by
        rw [← pow_add, rank_increment, ← hdim]

end ThreeSum.TernaryCoverTupleCount
