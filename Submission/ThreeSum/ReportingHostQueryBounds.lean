import Submission.ThreeSum.LightBlockQuery

/-! # Output bounds and stored-table preservation for actual query batching -/

namespace ThreeSum.ReportingHostQueryBounds

open Light Finset ThreeSum.SubsetAddress
open scoped BigOperators

def value {W : ℕ} (f g : Finset (Fin W) → ℤ) (stage : ℕ)
    (preL preR Q : Finset (Fin W)) : ℤ :=
  Subset.mobius (fun S => SubsetStages.stageValue f stage (preL ∪ S)*
    SubsetStages.stageValue g stage (preR ∪ S)) Q

theorem abs_value_le {W cut stage B D : ℕ} (f g : Finset (Fin W) → ℤ)
    (preL preR Q : Finset (Fin W)) (hstage : stage ≤ W)
    (hL : (preL ∪ Q).card ≤ cut) (hR : (preR ∪ Q).card ≤ cut)
    (hf : ∀ S, S.card ≤ cut → |f S| ≤ B)
    (hg : ∀ S, S.card ≤ cut → |g S| ≤ D) :
    |value f g stage preL preR Q| ≤ ((2^W*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) := by
  unfold value
  rw [SignedLeaf.mobius_eq_signed_sum,abs_mul,abs_neg_one_pow,one_mul]
  have hc : Q.card ≤ W := by simpa using Finset.card_le_univ Q
  calc
    _ ≤ ∑ S ∈ Q.powerset, |SignedLeaf.value f g stage preL preR S| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _S ∈ Q.powerset, (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) := by
      apply Finset.sum_le_sum
      intro S hS
      have hs := Finset.mem_powerset.mp hS
      exact SignedLeaf.abs_value_le f g stage preL preR S hstage
        ((Finset.card_le_card (Finset.union_subset_union (le_refl preL) hs)).trans hL)
        ((Finset.card_le_card (Finset.union_subset_union (le_refl preR) hs)).trans hR) hf hg
    _ = ((2^Q.card*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) := by simp [Nat.cast_mul]
    _ ≤ _ := by
      exact_mod_cast (Nat.mul_le_mul_right ((2^stage*B)*(2^stage*D))
        (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hc))

theorem abs_value_le_word {W cut stage t B D : ℕ} {lim : Limits}
    (f g : Finset (Fin W) → ℤ) (preL preR Q : Finset (Fin W)) (hstage : stage ≤ W)
    (hL : (preL ∪ Q).card ≤ cut) (hR : (preR ∪ Q).card ≤ cut)
    (hf : ∀ S, S.card ≤ cut → |f S| ≤ B)
    (hg : ∀ S, S.card ≤ cut → |g S| ≤ D)
    (hw : (LightSparseQuery.magnitudeBound W stage Q.card t B D : ℤ) ≤ lim.word) :
    |value f g stage preL preR Q| ≤ lim.word := by
  have hbase := abs_value_le f g preL preR Q hstage hL hR hf hg
  have hm : 2^W*((2^stage*B)*(2^stage*D)) ≤ LightSparseQuery.magnitudeBound W stage Q.card t B D :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hmInt : ((2^W*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤
      (LightSparseQuery.magnitudeBound W stage Q.card t B D : ℤ) := by exact_mod_cast hm
  exact hbase.trans (hmInt.trans hw)

theorem boxStored_of_on {W cut base : ℕ} {μ μ' : ℕ → ℤ} {f : Finset (Fin W) → ℤ}
    (h : LightBoxStages.StoredThrough μ base cut f W)
    (hkeep : ∀ i, base ≤ i → i < base+(W+1)*downsetCap W cut → μ' i = μ i) :
    LightBoxStages.StoredThrough μ' base cut f W := by
  intro j hj S hS
  have hr := subsetRank_lt hS
  have hm := Nat.mul_le_mul_right (downsetCap W cut) (Nat.succ_le_succ hj)
  simp only [Nat.succ_mul] at hm
  have he := hkeep (base+j*downsetCap W cut+subsetRank S) (by omega) (by
    simp only [Nat.succ_mul]
    omega)
  exact he.trans (h j hj S hS)

end ThreeSum.ReportingHostQueryBounds
