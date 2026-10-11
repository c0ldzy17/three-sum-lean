import Submission.ThreeSum.LightHistogram
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn

/-!
# Exact positions of original indices in retained residue buckets

Counting-sort positions preserve every input incidence. The resulting fiber
segments contain no repeated physical indices even when input values agree.
All inverse-enumeration reasoning is semantic; the actual scatter program
writes these positions using a cursor and never searches an input band.
-/

namespace ThreeSum.SourceBuckets

open Finset LightHistogram

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000

def offset (key : ℕ → ℕ) (N r : ℕ) : ℕ := ∑ s ∈ range r, count key s N

@[simp] theorem offset_zero (key : ℕ → ℕ) (N : ℕ) : offset key N 0 = 0 := by
  simp [offset]

theorem offset_succ (key : ℕ → ℕ) (N r : ℕ) :
    offset key N (r+1) = offset key N r+count key r N := by
  exact Finset.sum_range_succ _ _

theorem offset_mono (key : ℕ → ℕ) (N : ℕ) : Monotone (offset key N) := by
  intro r s hrs
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hrs)

theorem count_mono (key : ℕ → ℕ) (r : ℕ) : Monotone (count key r) := by
  intro i j hij
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hij))

theorem count_strict {key : ℕ → ℕ} {r i j : ℕ} (hij : i < j) (hkey : key i = r) :
    count key r i < count key r j := by
  have he := count_succ key r i
  simp only [hkey,ite_true] at he
  have hm := count_mono key r (show i+1 ≤ j by omega)
  omega

theorem offset_total {key : ℕ → ℕ} {N M : ℕ} (hkey : ∀ i < N, key i < M) :
    offset key N M = N := by
  unfold offset count
  have he := Finset.card_eq_sum_card_fiberwise
    (f := key) (s := range N) (t := range M)
    (fun i hi => Finset.mem_range.mpr (hkey i (Finset.mem_range.mp hi)))
  simpa only [Finset.card_range] using he.symm

theorem offset_le {key : ℕ → ℕ} {N M r : ℕ} (hkey : ∀ i < N, key i < M) (hr : r ≤ M) :
    offset key N r ≤ N := by
  exact (offset_mono key N hr).trans_eq (offset_total hkey)

def position (key : ℕ → ℕ) (N i : ℕ) : ℕ := offset key N (key i)+count key (key i) i

theorem position_start (key : ℕ → ℕ) (N i : ℕ) :
    offset key N (key i) ≤ position key N i := Nat.le_add_right _ _

theorem position_end {key : ℕ → ℕ} {N i : ℕ} (hi : i < N) :
    position key N i < offset key N (key i+1) := by
  rw [offset_succ]
  exact Nat.add_lt_add_left (count_strict hi rfl) _

theorem position_lt {key : ℕ → ℕ} {N M i : ℕ} (hkey : ∀ i < N, key i < M) (hi : i < N) :
    position key N i < N :=
  (position_end hi).trans_le (offset_le hkey (by have hk := hkey i hi; omega))

theorem position_lt_of_key_lt {key : ℕ → ℕ} {N i j : ℕ}
    (hi : i < N) (hij : key i < key j) : position key N i < position key N j :=
  (position_end hi).trans_le ((offset_mono key N (by omega)).trans (position_start key N j))

theorem position_injective {key : ℕ → ℕ} {N i j : ℕ}
    (hi : i < N) (hj : j < N) (he : position key N i = position key N j) : i = j := by
  have hk : key i = key j := by
    rcases lt_trichotomy (key i) (key j) with h | h | h
    · have hh := position_lt_of_key_lt hi h
      omega
    · exact h
    · have hh := position_lt_of_key_lt hj h
      omega
  unfold position at he
  rw [hk] at he
  have hcount : count key (key j) i = count key (key j) j := by omega
  rcases lt_trichotomy i j with h | h | h
  · have hh := count_strict h hk
    omega
  · exact h
  · have hh := count_strict (r := key j) h rfl
    omega

theorem position_bucket_iff {key : ℕ → ℕ} {N i r : ℕ} (hi : i < N) :
    offset key N r ≤ position key N i ∧ position key N i < offset key N (r+1) ↔ key i = r := by
  constructor
  · rintro ⟨ha,hb⟩
    rcases lt_trichotomy (key i) r with h | h | h
    · have he := (position_end hi).trans_le (offset_mono key N (show key i+1 ≤ r by omega))
      omega
    · exact h
    · have he := (offset_mono key N (show r+1 ≤ key i by omega)).trans (position_start key N i)
      omega
  · intro he
    have ha := position_start key N i
    have hb := position_end (key := key) hi
    simpa only [he] using And.intro ha hb

theorem exists_position {key : ℕ → ℕ} {N M : ℕ} (hkey : ∀ i < N, key i < M)
    {t : ℕ} (ht : t < N) : ∃ i < N, position key N i = t := by
  let f : Fin N → Fin N := fun i => ⟨position key N i.val,position_lt hkey i.isLt⟩
  have hf : Function.Injective f := by
    intro i j he
    exact Fin.ext (position_injective i.isLt j.isLt (congrArg Fin.val he))
  obtain ⟨i,hi⟩ := Finite.surjective_of_injective hf ⟨t,ht⟩
  exact ⟨i.val,i.isLt,congrArg Fin.val hi⟩

theorem exists_bucket_position {key : ℕ → ℕ} {N M r t : ℕ}
    (hkey : ∀ i < N, key i < M) (hr : r < M) (ht : t < count key r N) :
    ∃ i < N, key i = r ∧ position key N i = offset key N r+t := by
  have htN : offset key N r+t < N := by
    have he := offset_le hkey (show r+1 ≤ M by omega)
    rw [offset_succ] at he
    omega
  obtain ⟨i,hi,he⟩ := exists_position hkey htN
  refine ⟨i,hi,?_,he⟩
  apply (position_bucket_iff hi).mp
  rw [he,offset_succ]
  omega

/-- Concrete array contract produced by prefix offsets and cursor scatter. -/
structure Stored (μ : ℕ → ℤ) (key : ℕ → ℕ) (N M offsets flat : ℕ) : Prop where
  offsets : ∀ r ≤ M, μ (offsets+r) = (offset key N r : ℤ)
  indices : ∀ i < N, μ (flat+position key N i) = (i : ℤ)

def bucketList (μ : ℕ → ℤ) (flat start length : ℕ) : List ℕ :=
  List.ofFn (fun t : Fin length => (μ (flat+start+t.val)).toNat)

theorem bucketList_length (μ : ℕ → ℤ) (flat start length : ℕ) :
    (bucketList μ flat start length).length = length := by simp [bucketList]

theorem Stored.read_bucket {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r t : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M)
    (hr : r < M) (ht : t < count key r N) :
    ∃ i < N, key i = r ∧ position key N i = offset key N r+t ∧
      μ (flat+offset key N r+t) = (i : ℤ) := by
  obtain ⟨i,hi,hki,hpos⟩ := exists_bucket_position hkey hr ht
  refine ⟨i,hi,hki,hpos,?_⟩
  simpa only [hpos,Nat.add_assoc] using H.indices i hi

theorem Stored.mem_bucketList {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r i : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M) (hr : r < M) :
    i ∈ bucketList μ flat (offset key N r) (count key r N) ↔ i < N ∧ key i = r := by
  simp only [bucketList,List.mem_ofFn]
  constructor
  · rintro ⟨t,he⟩
    obtain ⟨j,hj,hkj,_,hread⟩ := H.read_bucket hkey hr t.isLt
    rw [hread,Int.toNat_natCast] at he
    subst i
    exact ⟨hj,hkj⟩
  · rintro ⟨hi,hki⟩
    have ht : count key r i < count key r N := count_strict hi hki
    refine ⟨⟨count key r i,ht⟩,?_⟩
    have he := H.indices i hi
    unfold position at he
    rw [hki] at he
    simpa only [Nat.add_assoc,Int.toNat_natCast] using congrArg Int.toNat he

theorem Stored.nodup_bucketList {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M) (hr : r < M) :
    (bucketList μ flat (offset key N r) (count key r N)).Nodup := by
  apply List.nodup_ofFn.mpr
  intro s t he
  obtain ⟨i,hi,hki,hpi,hri⟩ := H.read_bucket hkey hr s.isLt
  obtain ⟨j,hj,hkj,hpj,hrj⟩ := H.read_bucket hkey hr t.isLt
  dsimp only at he
  rw [hri,hrj,Int.toNat_natCast,Int.toNat_natCast] at he
  subst j
  apply Fin.ext
  omega

theorem Stored.offsets_end {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M) :
    μ offsets = 0 ∧ μ (offsets+M) = (N : ℤ) := by
  constructor
  · simpa only [Nat.add_zero,offset_zero,Nat.cast_zero] using H.offsets 0 (by omega)
  · simpa only [offset_total hkey] using H.offsets M le_rfl

end ThreeSum.SourceBuckets
