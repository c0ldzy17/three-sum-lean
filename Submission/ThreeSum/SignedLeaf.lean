import Submission.ThreeSum.SubsetStages
import Submission.ThreeSum.MaskDifference
import Submission.ThreeSum.QueryCoordinates

/-!
# Signed leaf weights and the explicit part of sparse queries

The alternating sign is separated from the query cardinality, allowing
the same leaf weights to be used in stored boxes and direct leaf reads.
-/

namespace ThreeSum.SignedLeaf

open Finset ThreeSum.SubsetAddress
open scoped BigOperators

/-- Union of disjoint coordinate masks is ordinary integer addition. -/
theorem subsetMask_disjoint_union {W : ℕ} (A B : Finset (Fin W)) (hd : Disjoint A B) :
    subsetMask (A ∪ B) = subsetMask A+subsetMask B := by
  simp only [MaskDifference.subsetMask_sum,Finset.sum_union hd]

def value {W : ℕ} (f g : Finset (Fin W) → ℤ) (stage : ℕ)
    (preL preR S : Finset (Fin W)) : ℤ :=
  (-1 : ℤ)^S.card *
    (SubsetStages.stageValue f stage (preL ∪ S)*SubsetStages.stageValue g stage (preR ∪ S))

theorem abs_value_le {W cut B C : ℕ} (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (preL preR S : Finset (Fin W))
    (hstage : stage ≤ W) (hL : (preL ∪ S).card ≤ cut) (hR : (preR ∪ S).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ C) :
    |value f g stage preL preR S| ≤ (((2^stage*B)*(2^stage*C) : ℕ) : ℤ) := by
  rw [value,abs_mul,abs_neg_one_pow,one_mul,abs_mul]
  have h₁ := SubsetStages.stageValue_abs_le f hf stage hstage (preL ∪ S) hL
  have h₂ := SubsetStages.stageValue_abs_le g hg stage hstage (preR ∪ S) hR
  simpa only [Nat.cast_mul] using mul_le_mul h₁ h₂ (abs_nonneg _) (Int.natCast_nonneg _)

theorem neg_one_pow_sub {a b : ℕ} (h : b ≤ a) :
    (-1 : ℤ)^(a-b) = (-1 : ℤ)^a*(-1 : ℤ)^b := by
  have ha : a = (a-b)+b := by omega
  rw [ha,pow_add,mul_assoc,← pow_add]
  have hb : b+b = 2*b := by omega
  rw [hb,pow_mul]
  norm_num

theorem mobius_eq_signed_sum {W : ℕ} (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (preL preR Q : Finset (Fin W)) :
    Subset.mobius
      (fun S => SubsetStages.stageValue f stage (preL ∪ S)*
        SubsetStages.stageValue g stage (preR ∪ S)) Q =
      (-1 : ℤ)^Q.card * ∑ S ∈ Q.powerset, value f g stage preL preR S := by
  rw [Subset.mobius,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [neg_one_pow_sub (Finset.card_le_card (Finset.mem_powerset.mp hS)),value]
  ring

/-- Missing sets in all layers strictly below `t`. -/
def explicitMissing {W : ℕ} (Q : Finset (Fin W)) (t : ℕ) : List (Finset (Fin W)) :=
  (List.range t).flatMap (QueryCoordinates.missingSets Q)

def explicitLeaves {W : ℕ} (Q : Finset (Fin W)) (t : ℕ) : List (Finset (Fin W)) :=
  (explicitMissing Q t).map fun U => Q \ U

@[simp] theorem mem_explicitMissing {W : ℕ} (Q U : Finset (Fin W)) (t : ℕ) :
    U ∈ explicitMissing Q t ↔ U ⊆ Q ∧ U.card < t := by
  simp only [explicitMissing,List.mem_flatMap,List.mem_range,QueryCoordinates.missingSets_mem]
  constructor
  · rintro ⟨j,hj,hU,hcard⟩
    exact ⟨hU,by omega⟩
  · rintro ⟨hU,ht⟩
    exact ⟨U.card,ht,hU,rfl⟩

theorem explicitMissing_nodup {W : ℕ} (Q : Finset (Fin W)) (t : ℕ) :
    (explicitMissing Q t).Nodup := by
  rw [explicitMissing,List.nodup_flatMap]
  constructor
  · intro j hj
    exact QueryCoordinates.missingSets_nodup Q j
  · refine (List.nodup_range (n := t)).imp ?_
    intro a b hab
    apply List.disjoint_left.mpr
    intro U hU hV
    have h₁ := (QueryCoordinates.missingSets_mem Q U a).mp hU
    have h₂ := (QueryCoordinates.missingSets_mem Q U b).mp hV
    omega

theorem explicitLeaves_nodup {W : ℕ} (Q : Finset (Fin W)) (t : ℕ) :
    (explicitLeaves Q t).Nodup := by
  apply (explicitMissing_nodup Q t).map_on
  intro A hA B hB he
  have ha := (mem_explicitMissing Q A t).mp hA
  have hb := (mem_explicitMissing Q B t).mp hB
  have hh := congrArg (fun U => Q \ U) he
  rwa [Finset.sdiff_sdiff_eq_self ha.1,Finset.sdiff_sdiff_eq_self hb.1] at hh

theorem mem_explicitLeaves {W : ℕ} (Q S : Finset (Fin W)) (t : ℕ) :
    S ∈ explicitLeaves Q t ↔ S ⊆ Q ∧ (Q \ S).card < t := by
  constructor
  · intro h
    obtain ⟨U,hU,rfl⟩ := List.mem_map.mp h
    have hu := (mem_explicitMissing Q U t).mp hU
    exact ⟨Finset.sdiff_subset,by rw [Finset.sdiff_sdiff_eq_self hu.1]; exact hu.2⟩
  · rintro ⟨hS,ht⟩
    exact List.mem_map.mpr ⟨Q \ S,(mem_explicitMissing Q _ t).mpr ⟨Finset.sdiff_subset,ht⟩,
      Finset.sdiff_sdiff_eq_self hS⟩

end ThreeSum.SignedLeaf
