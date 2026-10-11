import Submission.ThreeSum.LightZetaCell
import Submission.ThreeSum.MaskDecode
import Mathlib.Data.List.GetD

/-!
# The actual compact enumeration uses the actual compact table addresses

This bridges a sequentially constructed source array to `TableAt`: the mask
stored at `subsetRank S` by the existing enumerator is exactly `subsetMask S`.
No additional scatter, rank oracle, or arbitrary enumeration is required.
-/

namespace ThreeSum.SourceTableLayout

open SubsetAddress

set_option maxHeartbeats 800000

theorem layerRank_zero (L : ℕ) : layerRank L 0 0 = 0 := by
  induction L with
  | zero => rfl
  | succ L ih => simpa only [layerRank,if_pos (Nat.two_pow_pos L)] using ih

theorem getD_map_of_lt {α β : Type*} (l : List α) (f : α → β)
    (a : α) (b : β) {i : ℕ} (hi : i < l.length) :
    (l.map f).getD i b = f (l.getD i a) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getD_eq_getElem _ _ hi]
  exact List.getElem_map ..

theorem enumerateLayer_getD_rank {L k m : ℕ} (hm : IsMask L k m) (fallback : ℕ) :
    (enumerateLayer L k).getD (layerRank L k m) fallback = m := by
  induction L generalizing k m fallback with
  | zero =>
      have hk := hm.le_width
      have hb := hm.1
      have hk0 : k=0 := by omega
      have hm0 : m=0 := by simp only [pow_zero] at hb; omega
      subst k; subst m
      simp [enumerateLayer,layerRank]
  | succ L ih =>
      cases k with
      | zero =>
          have hm0 := (isMask_zero (L+1) m).mp hm
          subst m
          simp [enumerateLayer,layerRank_zero]
      | succ k =>
          rw [enumerateLayer,if_pos hm.le_width]
          by_cases hc : m < 2^L
          · rw [layerRank,if_pos hc]
            rw [List.getD_append _ _ _ _ (by
              rw [enumerateLayer_length]
              exact layerRank_lt (hm.low hc))]
            exact ih (hm.low hc) fallback
          · have hh := (hm.high (Nat.le_of_not_gt hc)).2
            simp only [Nat.add_sub_cancel] at hh
            rw [layerRank,if_neg hc]
            simp only [Nat.add_sub_cancel]
            rw [List.getD_append_right _ _ _ _ (by
              rw [enumerateLayer_length]
              omega),enumerateLayer_length,Nat.add_sub_cancel_left]
            rw [getD_map_of_lt _ _ 0 _ (by
              rw [enumerateLayer_length]
              exact layerRank_lt hh),ih hh 0]
            omega

theorem enumerateThrough_getD_rank {L k m cut : ℕ} (hm : IsMask L k m)
    (hk : k ≤ cut) (fallback : ℕ) :
    (enumerateThrough L cut).getD (downsetRank L m) fallback = m := by
  induction cut with
  | zero =>
      have hk0 : k=0 := by omega
      subst k
      simpa only [enumerateThrough,downsetRank,hm.2,layerOffset_zero,zero_add] using
        enumerateLayer_getD_rank hm fallback
  | succ cut ih =>
      rw [enumerateThrough]
      by_cases hlow : k ≤ cut
      · rw [List.getD_append _ _ _ _ (by
          rw [enumerateThrough_length]
          have hlt := layerRank_lt hm
          have hle := layerOffset_mono L (Nat.succ_le_succ hlow)
          simp only [Nat.succ_eq_add_one] at hle
          rw [layerOffset_succ L k] at hle
          unfold downsetRank
          rw [hm.2]
          omega)]
        exact ih hlow
      · have he : k=cut+1 := by omega
        subst k
        rw [downsetRank,hm.2]
        rw [List.getD_append_right _ _ _ _ (by
          rw [enumerateThrough_length]
          omega),enumerateThrough_length,Nat.add_sub_cancel_left]
        exact enumerateLayer_getD_rank hm fallback

theorem enumerateDownset_getD_rank {L cut m : ℕ}
    (hm : m < 2^L) (hk : weight L m ≤ cut) (fallback : ℕ) :
    (enumerateDownset L cut).getD (downsetRank L m) fallback = m := by
  exact enumerateThrough_getD_rank ⟨hm,rfl⟩ (le_min hk (weight_le_width hm)) fallback

theorem enumerateDownset_getD_subsetRank {L cut : ℕ} (S : Finset (Fin L))
    (hS : S.card ≤ cut) (fallback : ℕ) :
    (enumerateDownset L cut).getD (subsetRank S) fallback = subsetMask S := by
  have hmask := subsetMask_isMask S
  exact enumerateDownset_getD_rank hmask.1 (hmask.2.trans_le hS) fallback

def maskAt (L cut i : ℕ) : ℕ := (enumerateDownset L cut).getD i 0

def setAt (L cut i : ℕ) : Finset (Fin L) := MaskDecode.decode L (maskAt L cut i)

theorem maskAt_mem {L cut i : ℕ} (hi : i < downsetCap L cut) :
    maskAt L cut i ∈ enumerateDownset L cut := by
  unfold maskAt
  rw [List.getD_eq_getElem _ _ (by simpa only [enumerateDownset_length] using hi)]
  exact List.getElem_mem _

theorem maskAt_lt {L cut i : ℕ} (hi : i < downsetCap L cut) :
    maskAt L cut i < 2^L :=
  ((mem_enumerateDownset L cut _).mp (maskAt_mem hi)).1

theorem setAt_card {L cut i : ℕ} (hi : i < downsetCap L cut) :
    (setAt L cut i).card ≤ cut := by
  rw [setAt,MaskDecode.decode_card (maskAt_lt hi)]
  exact ((mem_enumerateDownset L cut _).mp (maskAt_mem hi)).2

theorem subsetMask_setAt {L cut i : ℕ} (hi : i < downsetCap L cut) :
    subsetMask (setAt L cut i) = maskAt L cut i :=
  MaskDecode.subsetMask_decode (maskAt_lt hi)

theorem setAt_subsetRank {L cut : ℕ} (S : Finset (Fin L)) (hS : S.card ≤ cut) :
    setAt L cut (subsetRank S) = S := by
  rw [setAt,maskAt,enumerateDownset_getD_subsetRank S hS,MaskDecode.decode_subsetMask]

/-- A sequential source-array construction using the actual enumerated masks
already has the address layout consumed by the suffix zeta program. -/
theorem tableAt_of_enumeration {L cut base : ℕ} {μ : ℕ → ℤ}
    (value : ℕ → ℤ) (f : Finset (Fin L) → ℤ)
    (hread : ∀ i < downsetCap L cut,
      μ (base+i) = value ((enumerateDownset L cut).getD i 0))
    (hvalue : ∀ S, S.card ≤ cut → value (subsetMask S) = f S) :
    LightZetaCell.TableAt μ base cut f := by
  intro S hS
  rw [hread _ (subsetRank_lt hS),enumerateDownset_getD_subsetRank S hS]
  exact hvalue S hS

theorem tableAt_of_setAt {L cut base : ℕ} {μ : ℕ → ℤ}
    (f : Finset (Fin L) → ℤ)
    (hread : ∀ i < downsetCap L cut, μ (base+i) = f (setAt L cut i)) :
    LightZetaCell.TableAt μ base cut f := by
  intro S hS
  rw [hread _ (subsetRank_lt hS),setAt_subsetRank S hS]

end ThreeSum.SourceTableLayout
