import Submission.ThreeSum.LightBlockBoxes

/-!
# Local suffix coordinates with exact global source semantics

The remaining ambient ground set has width V, whereas source transforms use
the original width W. A contiguous shift embeds local box masks into global
source masks. Enumeration and box-table addresses can therefore use V without
changing the original raw-incidence query.
-/

namespace ThreeSum.ReportingHostSuffix

open Finset ThreeSum.SubsetAddress BlockIndexedQuery BlockRows BlockIndex BlockForced
open GlobalEncoding LocalCoverBounds StoredReporting LightBlockQuery
open scoped BigOperators

def shiftEmbedding {W V : ℕ} (offset : ℕ) (hfit : offset+V ≤ W) : Fin V ↪ Fin W where
  toFun i := ⟨offset+i.val,(Nat.add_lt_add_left i.isLt offset).trans_le hfit⟩
  inj' := by intro i j he; apply Fin.ext; have := congrArg Fin.val he; simp only at this; omega

@[simp] theorem shiftEmbedding_val {W V offset : ℕ} (hfit : offset+V ≤ W) (i : Fin V) :
    (shiftEmbedding offset hfit i).val = offset+i.val := rfl

def liftSet {W V offset : ℕ} (hfit : offset+V ≤ W) (S : Finset (Fin V)) : Finset (Fin W) :=
  S.map (shiftEmbedding offset hfit)

@[simp] theorem liftSet_card {W V offset : ℕ} (hfit : offset+V ≤ W) (S : Finset (Fin V)) :
    (liftSet hfit S).card = S.card := Finset.card_map _

@[simp] theorem liftSet_empty {W V offset : ℕ} (hfit : offset+V ≤ W) :
    liftSet hfit ∅ = ∅ := Finset.map_empty _

theorem liftSet_injective {W V offset : ℕ} (hfit : offset+V ≤ W) :
    Function.Injective (liftSet hfit) := Finset.map_injective _

theorem liftSet_subset {W V offset : ℕ} (hfit : offset+V ≤ W) (S T : Finset (Fin V)) :
    liftSet hfit S ⊆ liftSet hfit T ↔ S ⊆ T := Finset.map_subset_map

theorem liftSet_mask {W V offset : ℕ} (hfit : offset+V ≤ W) (S : Finset (Fin V)) :
    subsetMask (liftSet hfit S) = 2^offset*subsetMask S := by
  simp only [MaskDifference.subsetMask_sum,liftSet,Finset.sum_map,shiftEmbedding_val,
    pow_add,Finset.mul_sum]

theorem liftSet_mask_int {W V offset : ℕ} (hfit : offset+V ≤ W) (S : Finset (Fin V)) :
    (subsetMask (liftSet hfit S) : ℤ) = (2^offset : ℕ)*(subsetMask S : ℤ) := by
  rw [liftSet_mask]
  push_cast
  rfl

def lowerSet {W V offset : ℕ} (hfit : offset+V ≤ W) (Q : Finset (Fin W)) : Finset (Fin V) :=
  univ.filter fun i => shiftEmbedding offset hfit i ∈ Q

@[simp] theorem mem_lowerSet {W V offset : ℕ} (hfit : offset+V ≤ W) (Q : Finset (Fin W))
    (i : Fin V) : i ∈ lowerSet hfit Q ↔ shiftEmbedding offset hfit i ∈ Q := by
  simp [lowerSet]

theorem lift_lowerSet {W V offset : ℕ} (hfit : offset+V ≤ W) (Q : Finset (Fin W))
    (hQ : ∀ i ∈ Q, offset ≤ i.val ∧ i.val < offset+V) : liftSet hfit (lowerSet hfit Q) = Q := by
  ext i
  constructor
  · intro hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
    exact (mem_lowerSet hfit Q j).mp hj
  · intro hi
    have hb := hQ i hi
    let j : Fin V := ⟨i.val-offset,by omega⟩
    have he : shiftEmbedding offset hfit j = i := by apply Fin.ext; simp [j]; omega
    exact Finset.mem_map.mpr ⟨j,(mem_lowerSet hfit Q j).mpr (he.symm ▸ hi),he⟩

theorem sum_powerset_lift {W V offset : ℕ} (hfit : offset+V ≤ W) (Q : Finset (Fin V))
    (f : Finset (Fin W) → ℤ) :
    (∑ S ∈ (liftSet hfit Q).powerset, f S) = ∑ S ∈ Q.powerset, f (liftSet hfit S) := by
  simp only [liftSet,Finset.map_eq_image]
  rw [Finset.powerset_image,Finset.sum_image]
  intro A _ B _ he
  exact (Finset.image_inj (shiftEmbedding offset hfit).injective).mp he

theorem mobius_lift {W V offset : ℕ} (hfit : offset+V ≤ W) (Q : Finset (Fin V))
    (f : Finset (Fin W) → ℤ) :
    Subset.mobius f (liftSet hfit Q) = Subset.mobius (fun S => f (liftSet hfit S)) Q := by
  unfold Subset.mobius
  rw [sum_powerset_lift]
  simp only [liftSet_card]

def leafWeight {W V offset : ℕ} (hfit : offset+V ≤ W)
    (f g : Finset (Fin W) → ℤ) (stage : ℕ) (preL preR : Finset (Fin W))
    (S : Finset (Fin V)) : ℤ := SignedLeaf.value f g stage preL preR (liftSet hfit S)

theorem leafWeight_abs_le {W V offset sourceCut stage B D : ℕ} (hfit : offset+V ≤ W)
    (f g : Finset (Fin W) → ℤ) (preL preR : Finset (Fin W)) (S : Finset (Fin V))
    (hstage : stage ≤ W) (hL : (preL ∪ liftSet hfit S).card ≤ sourceCut)
    (hR : (preR ∪ liftSet hfit S).card ≤ sourceCut)
    (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D) :
    |leafWeight hfit f g stage preL preR S| ≤ (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) :=
  SignedLeaf.abs_value_le f g stage preL preR _ hstage hL hR hf hg

theorem query_eq_local_signed_sum {W V offset : ℕ} (hfit : offset+V ≤ W)
    (f g : Finset (Fin W) → ℤ) (stage : ℕ) (preL preR : Finset (Fin W)) (Q : Finset (Fin V)) :
    Subset.mobius (fun S => SubsetStages.stageValue f stage (preL ∪ S)*
      SubsetStages.stageValue g stage (preR ∪ S)) (liftSet hfit Q) =
        (-1 : ℤ)^Q.card * ∑ S ∈ Q.powerset, leafWeight hfit f g stage preL preR S := by
  rw [SignedLeaf.mobius_eq_signed_sum,sum_powerset_lift,liftSet_card]
  rfl

theorem block_fit {J L k : ℕ} (hk : k ≤ J) : k*L+(J-k)*L ≤ J*L := by
  rw [← Nat.add_mul,Nat.add_sub_of_le hk]

theorem block_query_in_range {J L k : ℕ} (hk : k ≤ J) (Q : Fin J → Finset (Fin L))
    (i : Fin (J*L)) (hi : i ∈ querySet k Q) : k*L ≤ i.val ∧ i.val < k*L+(J-k)*L := by
  have hs := (SubsetStages.mem_suffix i).mp (querySet_subset_suffix hk Q hi)
  have he : J*L-(J-k)*L = k*L := by rw [← Nat.sub_mul,Nat.sub_sub_self hk]
  constructor
  · simpa only [suffixStage,he] using hs
  · rw [← Nat.add_mul,Nat.add_sub_of_le hk]
    exact i.isLt

def localQuery {J L k : ℕ} (hk : k ≤ J) (Q : Fin J → Finset (Fin L)) :
    Finset (Fin ((J-k)*L)) := lowerSet (block_fit hk) (querySet k Q)

theorem lift_localQuery {J L k : ℕ} (hk : k ≤ J) (Q : Fin J → Finset (Fin L)) :
    liftSet (block_fit hk) (localQuery hk Q) = querySet k Q :=
  lift_lowerSet (block_fit hk) _ (block_query_in_range hk Q)

theorem localQuery_card {J L h k : ℕ} (hk : k ≤ J) (Q : Fin J → Finset (Fin L))
    (hQ : ∀ i, (Q i).card = 2*h) : (localQuery hk Q).card = (J-k)*(2*h) := by
  rw [← liftSet_card (block_fit hk),lift_localQuery,querySet_card hk Q hQ]

section Original

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
open RawIncidences RawReporting RawPrefixCounts

theorem original_query_local {h J k : ℕ} (pMod shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ)
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k ≤ J)
    (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1 % pMod+lift w.2.1*pMod+shift)-globalKey w.2.2) :
    (-1 : ℤ)^(localQuery hk (outputRows w.2.2)).card *
      ∑ S ∈ (localQuery hk (outputRows w.2.2)).powerset,
        leafWeight (block_fit hk) (leftSource pMod B b w.2.2) (rightSource pMod shift C c w.2.2)
          (suffixStage J (512*h) k) (leftPrefix k (prefixRows (J := J) pre))
          (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) pre)) S =
      (prefixQuery (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k pre : ℤ) := by
  rw [← query_eq_local_signed_sum,lift_localQuery]
  exact queryValue_eq_prefixQuery pMod shift A B C a b c w pre hk hp hkey

end Original
end ThreeSum.ReportingHostSuffix
