import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Embedding
import Mathlib.Combinatorics.Colex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Compact addresses for bounded-cardinality bit masks

Both ranking and enumeration recurse on the highest available bit. The
enumerator stops immediately when the requested layer is empty. In
particular, it does not enumerate the ambient Boolean cube and filter it.
-/

namespace ThreeSum.SubsetAddress

set_option maxRecDepth 4000

open Finset
open scoped BigOperators

/-- Number of selected bits among the first `L` positions, evaluated by
removing the highest available bit. Its intended domain is `m < 2^L`. -/
def weight : ℕ → ℕ → ℕ
  | 0, _ => 0
  | L + 1, m => if m < 2 ^ L then weight L m else weight L (m - 2 ^ L) + 1

def IsMask (L k m : ℕ) : Prop := m < 2 ^ L ∧ weight L m = k

instance (L k m : ℕ) : Decidable (IsMask L k m) := by
  unfold IsMask
  infer_instance

private theorem pow_two_succ (L : ℕ) : 2 ^ (L + 1) = 2 ^ L + 2 ^ L := by
  rw [pow_succ]
  omega

@[simp] theorem weight_zero (L : ℕ) : weight L 0 = 0 := by
  induction L with
  | zero => rfl
  | succ L ih => simpa [weight, Nat.two_pow_pos] using ih

theorem weight_le_width {L m : ℕ} (hm : m < 2 ^ L) : weight L m ≤ L := by
  induction L generalizing m with
  | zero => simp [weight]
  | succ L ih =>
      rw [pow_two_succ] at hm
      by_cases hc : m < 2 ^ L
      · simpa [weight, hc] using (ih hc).trans (Nat.le_succ L)
      · have hr : m - 2 ^ L < 2 ^ L := by omega
        simpa [weight, hc] using Nat.succ_le_succ (ih hr)

theorem IsMask.le_width {L k m : ℕ} (hm : IsMask L k m) : k ≤ L := by
  rw [← hm.2]
  exact weight_le_width hm.1

theorem weight_eq_zero_iff {L m : ℕ} (hm : m < 2 ^ L) :
    weight L m = 0 ↔ m = 0 := by
  induction L generalizing m with
  | zero =>
      simp only [pow_zero] at hm
      have hz : m = 0 := by omega
      simp [hz, weight]
  | succ L ih =>
      by_cases hc : m < 2 ^ L
      · simpa [weight, hc] using ih hc
      · have hp := Nat.two_pow_pos L
        have hn : m ≠ 0 := by omega
        simp [weight, hc, hn]

@[simp] theorem isMask_zero (L m : ℕ) : IsMask L 0 m ↔ m = 0 := by
  constructor
  · intro hm
    exact (weight_eq_zero_iff hm.1).mp hm.2
  · rintro rfl
    exact ⟨Nat.two_pow_pos L, weight_zero L⟩

theorem IsMask.low {L k m : ℕ} (hm : IsMask (L + 1) k m) (hc : m < 2 ^ L) :
    IsMask L k m := ⟨hc, by simpa [weight, hc] using hm.2⟩

theorem IsMask.high {L k m : ℕ} (hm : IsMask (L + 1) k m) (hc : 2 ^ L ≤ m) :
    0 < k ∧ IsMask L (k - 1) (m - 2 ^ L) := by
  have hb := hm.1
  rw [pow_two_succ] at hb
  have hw := hm.2
  simp only [weight, if_neg (Nat.not_lt.mpr hc)] at hw
  exact ⟨by omega, by constructor <;> omega⟩

theorem IsMask.succ_low {L k m : ℕ} (hm : IsMask L k m) : IsMask (L + 1) k m := by
  have hb := hm.1
  refine ⟨?_, ?_⟩
  · rw [pow_two_succ]
    omega
  · simpa [weight, hm.1] using hm.2

theorem IsMask.succ_high {L k m : ℕ} (hm : IsMask L k m) :
    IsMask (L + 1) (k + 1) (2 ^ L + m) := by
  have hb := hm.1
  refine ⟨?_, ?_⟩
  · rw [pow_two_succ]
    omega
  · have hc : ¬2 ^ L + m < 2 ^ L := by omega
    simpa [weight, hc] using hm.2

/-- Zero-based rank within a fixed-cardinality layer. The table-based
implementation below replaces each binomial coefficient by a lookup. -/
def layerRank : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | L + 1, k, m =>
      if m < 2 ^ L then layerRank L k m
      else L.choose k + layerRank L (k - 1) (m - 2 ^ L)

theorem layerRank_lt {L k m : ℕ} (hm : IsMask L k m) : layerRank L k m < L.choose k := by
  induction L generalizing k m with
  | zero =>
      have hk := hm.le_width
      have : k = 0 := by omega
      simp [this, layerRank]
  | succ L ih =>
      by_cases hc : m < 2 ^ L
      · simpa only [layerRank, if_pos hc] using
          (ih (hm.low hc)).trans_le (Nat.choose_le_succ L k)
      · obtain ⟨hk, hr⟩ := hm.high (Nat.le_of_not_gt hc)
        have hb := ih hr
        rw [layerRank, if_neg hc, Nat.choose_succ_left L k hk]
        omega

theorem layerRank_injective {L k m n : ℕ} (hm : IsMask L k m) (hn : IsMask L k n)
    (he : layerRank L k m = layerRank L k n) : m = n := by
  induction L generalizing k m n with
  | zero =>
      have hm' := hm.1
      have hn' := hn.1
      simp only [pow_zero] at hm' hn'
      omega
  | succ L ih =>
      by_cases hc : m < 2 ^ L <;> by_cases hd : n < 2 ^ L
      · apply ih (hm.low hc) (hn.low hd)
        simpa only [layerRank, if_pos hc, if_pos hd] using he
      · have hb := layerRank_lt (hm.low hc)
        simp only [layerRank, if_pos hc, if_neg hd] at he
        omega
      · have hb := layerRank_lt (hn.low hd)
        simp only [layerRank, if_neg hc, if_pos hd] at he
        omega
      · have hr := (hm.high (Nat.le_of_not_gt hc)).2
        have hs := (hn.high (Nat.le_of_not_gt hd)).2
        have hrest : layerRank L (k - 1) (m - 2 ^ L) =
            layerRank L (k - 1) (n - 2 ^ L) := by
          simpa only [layerRank, if_neg hc, if_neg hd, Nat.add_left_cancel_iff] using he
        have hi := ih hr hs hrest
        omega

/-- Construct every `k`-bit mask once, lower half before upper half. The
guard prevents recursion through empty layers. -/
def enumerateLayer : ℕ → ℕ → List ℕ
  | _, 0 => [0]
  | 0, _ + 1 => []
  | L + 1, k + 1 =>
      if k + 1 ≤ L + 1 then
        enumerateLayer L (k + 1) ++ (enumerateLayer L k).map (fun m => 2 ^ L + m)
      else []

theorem enumerateLayer_length (L k : ℕ) : (enumerateLayer L k).length = L.choose k := by
  induction L generalizing k with
  | zero => cases k <;> simp [enumerateLayer]
  | succ L ih =>
      cases k with
      | zero => simp [enumerateLayer]
      | succ k =>
          by_cases hk : k + 1 ≤ L + 1
          · simp [enumerateLayer, hk, ih, Nat.choose_succ_succ, Nat.add_comm]
          · simp [enumerateLayer, hk, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)]

theorem mem_enumerateLayer (L k m : ℕ) : m ∈ enumerateLayer L k ↔ IsMask L k m := by
  induction L generalizing k m with
  | zero =>
      cases k with
      | zero => simp [enumerateLayer]
      | succ k => simp [enumerateLayer, IsMask, weight]
  | succ L ih =>
      cases k with
      | zero => simp [enumerateLayer]
      | succ k =>
          by_cases hk : k + 1 ≤ L + 1
          · simp only [enumerateLayer, if_pos hk, List.mem_append, List.mem_map, ih]
            constructor
            · rintro (hm | ⟨a, ha, rfl⟩)
              · exact hm.succ_low
              · exact ha.succ_high
            · intro hm
              by_cases hc : m < 2 ^ L
              · exact Or.inl (hm.low hc)
              · right
                refine ⟨m - 2 ^ L, ?_, by omega⟩
                simpa only [Nat.add_sub_cancel] using (hm.high (Nat.le_of_not_gt hc)).2
          · have hn : ¬IsMask (L + 1) (k + 1) m := fun hm => hk hm.le_width
            simp [enumerateLayer, hk, hn]

theorem enumerateLayer_nodup (L k : ℕ) : (enumerateLayer L k).Nodup := by
  induction L generalizing k with
  | zero => cases k <;> simp [enumerateLayer]
  | succ L ih =>
      cases k with
      | zero => simp [enumerateLayer]
      | succ k =>
          by_cases hk : k + 1 ≤ L + 1
          · rw [enumerateLayer, if_pos hk]
            apply (ih (k + 1)).append
            · exact (ih k).map (fun _ _ h => Nat.add_left_cancel h)
            · intro m hm hn
              have hb := ((mem_enumerateLayer L (k + 1) m).mp hm).1
              obtain ⟨n, _, he⟩ := List.mem_map.mp hn
              omega
          · simp [enumerateLayer, hk]

/-- The work recurrence charges each recursive invocation, every emitted
upper mask, and every cell copied by the lower-list append. Bit-mask
addition and the guards are individual arithmetic operations. -/
def enumerationWork : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 1
  | L + 1, k + 1 =>
      if k + 1 ≤ L + 1 then
        1 + enumerationWork L (k + 1) + enumerationWork L k +
          (enumerateLayer L (k + 1)).length + (enumerateLayer L k).length
      else 1

theorem enumerationWork_bound (L k : ℕ) :
    enumerationWork L k ≤ (4 * L + 1) * L.choose k + 1 := by
  induction L generalizing k with
  | zero => cases k <;> simp [enumerationWork]
  | succ L ih =>
      cases k with
      | zero => simp [enumerationWork]
      | succ k =>
          by_cases hk : k + 1 ≤ L + 1
          · have hi := ih (k + 1)
            have hj := ih k
            have hp := Nat.choose_pos hk
            rw [Nat.choose_succ_succ] at hp
            simp only [enumerationWork, if_pos hk, enumerateLayer_length,
              Nat.choose_succ_succ]
            nlinarith
          · simp [enumerationWork, hk, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)]

/-- Offset of the layer of cardinality `k` within the full cardinality
ordering. -/
def layerOffset (L k : ℕ) : ℕ := ∑ r ∈ Finset.range k, L.choose r

@[simp] theorem layerOffset_zero (L : ℕ) : layerOffset L 0 = 0 := by
  simp [layerOffset]

theorem layerOffset_succ (L k : ℕ) :
    layerOffset L (k + 1) = layerOffset L k + L.choose k := by
  exact Finset.sum_range_succ _ _

theorem layerOffset_mono (L : ℕ) : Monotone (layerOffset L) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [layerOffset_succ]
  omega

def downsetCap (L cut : ℕ) : ℕ := layerOffset L (min cut L + 1)

def downsetRank (L m : ℕ) : ℕ :=
  layerOffset L (weight L m) + layerRank L (weight L m) m

theorem downsetRank_lt {L cut m : ℕ} (hm : m < 2 ^ L) (hk : weight L m ≤ cut) :
    downsetRank L m < downsetCap L cut := by
  have hmask : IsMask L (weight L m) m := ⟨hm, rfl⟩
  have hr := layerRank_lt hmask
  unfold downsetRank downsetCap
  calc
    _ < layerOffset L (weight L m) + L.choose (weight L m) := Nat.add_lt_add_left hr _
    _ = layerOffset L (weight L m + 1) := (layerOffset_succ L _).symm
    _ ≤ _ := layerOffset_mono L (Nat.succ_le_succ (le_min hk hmask.le_width))

private theorem downsetRank_lt_of_weight_lt {L m n : ℕ} (hm : m < 2 ^ L)
    (hk : weight L m < weight L n) : downsetRank L m < downsetRank L n := by
  have hr := layerRank_lt (show IsMask L (weight L m) m from ⟨hm, rfl⟩)
  have ho := layerOffset_mono L hk
  rw [layerOffset_succ] at ho
  unfold downsetRank
  omega

theorem downsetRank_injective {L m n : ℕ} (hm : m < 2 ^ L) (hn : n < 2 ^ L)
    (he : downsetRank L m = downsetRank L n) : m = n := by
  rcases lt_trichotomy (weight L m) (weight L n) with hk | hk | hk
  · have hlt := downsetRank_lt_of_weight_lt hm hk
    omega
  · have hr : layerRank L (weight L m) m = layerRank L (weight L m) n := by
      unfold downsetRank at he
      rw [← hk] at he
      omega
    exact layerRank_injective ⟨hm, rfl⟩ ⟨hn, hk.symm⟩ hr
  · have hlt := downsetRank_lt_of_weight_lt hn hk
    omega

/-- Enumerate consecutive layers by concatenation, with no ambient-cube
enumeration. The public downset enumerator caps the cutoff at the width. -/
def enumerateThrough (L : ℕ) : ℕ → List ℕ
  | 0 => enumerateLayer L 0
  | k + 1 => enumerateThrough L k ++ enumerateLayer L (k + 1)

def enumerateDownset (L cut : ℕ) : List ℕ := enumerateThrough L (min cut L)

theorem enumerateThrough_length (L k : ℕ) :
    (enumerateThrough L k).length = layerOffset L (k + 1) := by
  induction k with
  | zero => simp [enumerateThrough, enumerateLayer_length, layerOffset_succ]
  | succ k ih =>
      rw [enumerateThrough, List.length_append, ih, enumerateLayer_length,
        layerOffset_succ L (k + 1)]

theorem enumerateDownset_length (L cut : ℕ) :
    (enumerateDownset L cut).length = downsetCap L cut :=
  enumerateThrough_length L (min cut L)

theorem mem_enumerateThrough (L k m : ℕ) :
    m ∈ enumerateThrough L k ↔ m < 2 ^ L ∧ weight L m ≤ k := by
  induction k with
  | zero => simp [enumerateThrough, mem_enumerateLayer, IsMask]
  | succ k ih =>
      simp only [enumerateThrough, List.mem_append, ih, mem_enumerateLayer, IsMask]
      omega

theorem mem_enumerateDownset (L cut m : ℕ) :
    m ∈ enumerateDownset L cut ↔ m < 2 ^ L ∧ weight L m ≤ cut := by
  rw [enumerateDownset, mem_enumerateThrough]
  constructor
  · rintro ⟨hm, hk⟩
    exact ⟨hm, hk.trans (min_le_left _ _)⟩
  · rintro ⟨hm, hk⟩
    exact ⟨hm, le_min hk (weight_le_width hm)⟩

theorem enumerateThrough_nodup (L k : ℕ) : (enumerateThrough L k).Nodup := by
  induction k with
  | zero => exact enumerateLayer_nodup L 0
  | succ k ih =>
      apply ih.append (enumerateLayer_nodup L (k + 1))
      intro m hm hn
      have ht := (mem_enumerateThrough L k m).mp hm
      have hk := (mem_enumerateLayer L (k + 1) m).mp hn
      have hw := hk.2
      omega

theorem enumerateDownset_nodup (L cut : ℕ) : (enumerateDownset L cut).Nodup :=
  enumerateThrough_nodup L (min cut L)

def throughWork (L : ℕ) : ℕ → ℕ
  | 0 => enumerationWork L 0
  | k + 1 => throughWork L k + enumerationWork L (k + 1) +
      1 + (enumerateThrough L k).length

theorem throughWork_bound (L k : ℕ) :
    throughWork L k ≤ (4 * L + k + 1) * layerOffset L (k + 1) + 2 * k + 1 := by
  induction k with
  | zero => simp [throughWork, enumerationWork, layerOffset_succ]
  | succ k ih =>
      have hl := enumerationWork_bound L (k + 1)
      simp only [throughWork, enumerateThrough_length]
      rw [layerOffset_succ L (k + 1)]
      nlinarith

def downsetEnumerationWork (L cut : ℕ) : ℕ := throughWork L (min cut L)

theorem downsetEnumerationWork_bound (L cut : ℕ) :
    downsetEnumerationWork L cut ≤ (5 * L + 1) * downsetCap L cut + 2 * L + 1 := by
  have hw := throughWork_bound L (min cut L)
  have hk : min cut L ≤ L := min_le_right _ _
  unfold downsetEnumerationWork downsetCap
  nlinarith

/-- Integer bit mask of a finite set of coordinate positions. -/
def maskOf (s : Finset ℕ) : ℕ := ∑ i ∈ s, 2 ^ i

theorem maskOf_injective : Function.Injective maskOf :=
  Finset.geomSum_injective (by decide)

private theorem subset_range_pred {L : ℕ} {s : Finset ℕ}
    (hs : s ⊆ Finset.range (L + 1)) (hL : L ∉ s) : s ⊆ Finset.range L := by
  intro i hi
  have hb := Finset.mem_range.mp (hs hi)
  have hn : i ≠ L := by rintro rfl; exact hL hi
  exact Finset.mem_range.mpr (by omega)

theorem maskOf_isMask {L : ℕ} {s : Finset ℕ} (hs : s ⊆ Finset.range L) :
    IsMask L s.card (maskOf s) := by
  induction L generalizing s with
  | zero =>
      have he : s = ∅ := by simpa using hs
      subst s
      simp [maskOf]
  | succ L ih =>
      by_cases hL : L ∈ s
      · have ht : s.erase L ⊆ Finset.range L :=
          subset_range_pred ((Finset.erase_subset L s).trans hs) (Finset.notMem_erase _ _)
        have hm := (ih ht).succ_high
        have hcard : (s.erase L).card + 1 = s.card := Finset.card_erase_add_one hL
        have he : 2 ^ L + maskOf (s.erase L) = maskOf s :=
          Finset.add_sum_erase s (fun i => 2 ^ i) hL
        simpa only [hcard, he] using hm
      · exact (ih (subset_range_pred hs hL)).succ_low

def natPositions {L : ℕ} (s : Finset (Fin L)) : Finset ℕ := s.map Fin.valEmbedding

theorem natPositions_subset {L : ℕ} (s : Finset (Fin L)) :
    natPositions s ⊆ Finset.range L := by
  intro i hi
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
  exact Finset.mem_range.mpr j.isLt

@[simp] theorem natPositions_card {L : ℕ} (s : Finset (Fin L)) :
    (natPositions s).card = s.card := Finset.card_map _

theorem natPositions_injective (L : ℕ) :
    Function.Injective (@natPositions L) := Finset.map_injective _

def subsetMask {L : ℕ} (s : Finset (Fin L)) : ℕ := maskOf (natPositions s)

theorem subsetMask_isMask {L : ℕ} (s : Finset (Fin L)) :
    IsMask L s.card (subsetMask s) := by
  simpa only [natPositions_card, subsetMask] using maskOf_isMask (natPositions_subset s)

theorem subsetMask_injective (L : ℕ) : Function.Injective (@subsetMask L) :=
  maskOf_injective.comp (natPositions_injective L)

def subsetRank {L : ℕ} (s : Finset (Fin L)) : ℕ := downsetRank L (subsetMask s)

theorem subsetRank_lt {L cut : ℕ} {s : Finset (Fin L)} (hs : s.card ≤ cut) :
    subsetRank s < downsetCap L cut := by
  have hm := subsetMask_isMask s
  exact downsetRank_lt hm.1 (hm.2.trans_le hs)

theorem subsetRank_injective (L : ℕ) : Function.Injective (@subsetRank L) := by
  intro s t he
  apply subsetMask_injective L
  exact downsetRank_injective (subsetMask_isMask s).1 (subsetMask_isMask t).1 he

theorem subsetMask_mem_enumeration {L cut : ℕ} {s : Finset (Fin L)} (hs : s.card ≤ cut) :
    subsetMask s ∈ enumerateDownset L cut := by
  apply (mem_enumerateDownset L cut _).mpr
  have hm := subsetMask_isMask s
  exact ⟨hm.1, hm.2.trans_le hs⟩

/-- Packing a flagged subset and a canonical free-prefix length into a
single compact table address. -/
def recordAddress {L : ℕ} (flags : Finset (Fin L)) (freeCount : ℕ) : ℕ :=
  subsetRank flags * (L + 1) + freeCount

theorem recordAddress_lt {L cut : ℕ} {flags : Finset (Fin L)} {e : ℕ}
    (hflags : flags.card ≤ cut) (he : e ≤ L) :
    recordAddress flags e < downsetCap L cut * (L + 1) := by
  have hr := subsetRank_lt hflags
  have hp := Nat.mul_le_mul_right (L + 1) hr
  unfold recordAddress
  nlinarith

theorem recordAddress_injective {L : ℕ} {s t : Finset (Fin L)} {e f : ℕ}
    (he : e ≤ L) (hf : f ≤ L) (h : recordAddress s e = recordAddress t f) :
    s = t ∧ e = f := by
  have he' : e < L + 1 := by omega
  have hf' : f < L + 1 := by omega
  have hfree : e = f := by
    have hmod := congrArg (fun x => x % (L + 1)) h
    simpa [recordAddress, Nat.add_mod, Nat.mod_eq_of_lt he', Nat.mod_eq_of_lt hf'] using hmod
  have hmul : subsetRank s * (L + 1) = subsetRank t * (L + 1) := by
    unfold recordAddress at h
    omega
  have hr : subsetRank s = subsetRank t := Nat.eq_of_mul_eq_mul_right (by omega) hmul
  exact ⟨subsetRank_injective L hr, hfree⟩

end ThreeSum.SubsetAddress
