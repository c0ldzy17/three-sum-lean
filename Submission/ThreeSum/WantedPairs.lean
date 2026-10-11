import Submission.ThreeSum.SourceBucketView
import Submission.ThreeSum.RawAKeyLists
import Submission.ThreeSum.LightResidues

/-!
# Exact output-sensitive residue join semantics

The join visits a stored right-index fiber once for each left input
position. Its output is the literal list of matching position pairs.
The count is the guarded wanted mass when the left codes include the
selected common shift and the right codes are the original output keys.
-/

namespace ThreeSum.WantedPairs

open Light SourceBuckets
open scoped BigOperators

set_option maxHeartbeats 1200000

def count (left right : ℕ → ℕ) (NR NL : ℕ) : ℕ :=
  ∑ i ∈ Finset.range NL, LightHistogram.count right (left i) NR

@[simp] theorem count_zero (left right : ℕ → ℕ) (NR : ℕ) : count left right NR 0=0 := by
  simp [count]

theorem count_succ (left right : ℕ → ℕ) (NR n : ℕ) :
    count left right NR (n+1)=count left right NR n+LightHistogram.count right (left n) NR :=
  Finset.sum_range_succ _ _

theorem count_mono (left right : ℕ → ℕ) (NR : ℕ) : Monotone (count left right NR) := by
  intro i j hij
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hij)

def row (μ : ℕ → ℤ) (offsets flat : ℕ) (left : ℕ → ℕ) (i : ℕ) : List (ℕ × ℕ) :=
  (SourceBucketView.indices μ offsets flat (left i)).map (fun j => (i,j))

def pairs (μ : ℕ → ℤ) (offsets flat : ℕ) (left : ℕ → ℕ) (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap (row μ offsets flat left)

@[simp] theorem pairs_zero (μ : ℕ → ℤ) (offsets flat : ℕ) (left : ℕ → ℕ) :
    pairs μ offsets flat left 0=[] := rfl

theorem pairs_succ (μ : ℕ → ℤ) (offsets flat : ℕ) (left : ℕ → ℕ) (n : ℕ) :
    pairs μ offsets flat left (n+1)=pairs μ offsets flat left n++row μ offsets flat left n := by
  simp only [pairs,List.range_succ,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil]

theorem row_length {μ : ℕ → ℤ} {offsets flat NR M i : ℕ} {left right : ℕ → ℕ}
    (H : Stored μ right NR M offsets flat) (hi : left i < M) :
    (row μ offsets flat left i).length=LightHistogram.count right (left i) NR := by
  rw [row,List.length_map,SourceBucketView.indices_length H hi]

theorem pairs_length {μ : ℕ → ℤ} {offsets flat NR M : ℕ} {left right : ℕ → ℕ}
    (H : Stored μ right NR M offsets flat) : ∀ n,
    (∀ i < n, left i < M) →
      (pairs μ offsets flat left n).length=count left right NR n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hleft
    rw [pairs_succ,List.length_append,ih (fun i hi => hleft i (by omega)),
      row_length H (hleft n (by omega)),count_succ]

theorem mem_pairs {μ : ℕ → ℤ} {offsets flat NR NL M i j : ℕ} {left right : ℕ → ℕ}
    (H : Stored μ right NR M offsets flat) (hl : ∀ a < NL, left a < M)
    (hr : ∀ b < NR, right b < M) :
    (i,j) ∈ pairs μ offsets flat left NL ↔ i < NL ∧ j < NR ∧ right j=left i := by
  constructor
  · intro hh
    obtain ⟨a,ha,hb⟩ := List.mem_flatMap.mp hh
    have ha' : a < NL := List.mem_range.mp ha
    obtain ⟨b,hb,he⟩ := List.mem_map.mp hb
    have hai : a=i := congrArg Prod.fst he
    have hbj : b=j := congrArg Prod.snd he
    subst a
    subst b
    exact ⟨ha',(SourceBucketView.mem_indices H hr (hl i ha')).mp hb⟩
  · rintro ⟨hi,hj,hkey⟩
    apply List.mem_flatMap.mpr
    refine ⟨i,List.mem_range.mpr hi,?_⟩
    apply List.mem_map.mpr
    exact ⟨j,(SourceBucketView.mem_indices H hr (hl i hi)).mpr ⟨hj,hkey⟩,rfl⟩

theorem pairs_nodup {μ : ℕ → ℤ} {offsets flat NR NL M : ℕ} {left right : ℕ → ℕ}
    (H : Stored μ right NR M offsets flat) (hl : ∀ a < NL, left a < M)
    (hr : ∀ b < NR, right b < M) : (pairs μ offsets flat left NL).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro i hi
    exact (SourceBucketView.nodup_indices H hr (hl i (List.mem_range.mp hi))).map
      (fun _ _ he => congrArg Prod.snd he)
  · apply (List.nodup_range (n := NL)).imp
    intro i j hij
    apply List.disjoint_left.mpr
    intro p hp hq
    obtain ⟨a,_,ha⟩ := List.mem_map.mp hp
    obtain ⟨b,_,hb⟩ := List.mem_map.mp hq
    exact hij ((congrArg Prod.fst ha).trans (congrArg Prod.fst hb).symm)

def cells (ps : List (ℕ × ℕ)) : List ℤ := ps.flatMap (fun p => [p.1,p.2])

theorem cells_length (ps : List (ℕ × ℕ)) : (cells ps).length=2*ps.length := by
  induction ps with
  | nil => simp [cells]
  | cons p ps ih => simp only [cells,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil] at *; omega

theorem cells_append (as bs : List (ℕ × ℕ)) : cells (as++bs)=cells as++cells bs :=
  List.flatMap_append ..

theorem row_segment {μ ν : ℕ → ℤ} {offsets flat NR M i dst previous : ℕ}
    {left right : ℕ → ℕ} (H : Stored μ right NR M offsets flat)
    (hr : ∀ j < NR, right j < M) (hi : left i < M)
    (hout : ∀ t < LightHistogram.count right (left i) NR,
      ν (dst+2*(previous+t))=(i : ℤ) ∧
      ν (dst+2*(previous+t)+1)=μ (flat+offset right NR (left i)+t)) :
    Seg ν (dst+2*previous) (cells (row μ offsets flat left i)) := by
  unfold cells row
  rw [List.flatMap_map]
  apply LocalKeyArraySemantics.seg_flatMap_rows _ _ 2 (dst+2*previous) (by simp)
  intro j hj a ha
  have hj' : j < LightHistogram.count right (left i) NR := by
    simpa only [SourceBucketView.indices_length H hi] using hj
  obtain ⟨b,hb,hkb,hpos,hread⟩ := H.read_bucket hr hi hj'
  have hindex : (SourceBucketView.indices μ offsets flat (left i))[j]=b := by
    simp only [SourceBucketView.indices_eq H hi,bucketList,List.getElem_ofFn]
    rw [hread,Int.toNat_natCast]
  have haddress : dst+2*previous+j*2=dst+2*(previous+j) := by ring
  have hacases : a=0 ∨ a=1 := by omega
  rcases hacases with rfl | rfl
  · change ν (dst+2*previous+j*2+0)=(i : ℤ)
    simpa only [Nat.add_zero,haddress] using (hout j hj').1
  · change ν (dst+2*previous+j*2+1)=
      ((SourceBucketView.indices μ offsets flat (left i))[j] : ℤ)
    rw [haddress,hindex]
    exact (hout j hj').2.trans hread

theorem residue_eq_iff {M : ℕ} (hM : 0 < M) (a b d : ℤ) :
    LightResidues.residue M 1 b=LightResidues.residue M 1 (a+d) ↔ (M : ℤ) ∣ a+d-b := by
  rw [← Nat.cast_inj (R := ℤ),LightResidues.residue_cast hM,
    LightResidues.residue_cast hM,one_mul,one_mul]
  exact Int.modEq_iff_dvd

theorem count_modulo (M : ℕ) (hM : 0 < M) (as bs : List ℤ) (d : ℤ) :
    count (fun i => LightResidues.residue M 1 (as.getD i 0+d))
      (fun j => LightResidues.residue M 1 (bs.getD j 0)) bs.length as.length =
      ∑ i : Fin as.length, ∑ j : Fin bs.length,
        if (M : ℤ) ∣ as.getD i.val 0+d-bs.getD j.val 0 then 1 else 0 := by
  unfold count LightHistogram.count
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp only [residue_eq_iff hM]

theorem count_global (M : ℕ) (hM : 0 < M) (as : List ℤ) (h J : ℕ) (d : ℤ) :
    count (fun i => LightResidues.residue M 1 (as.getD i 0+d))
      (fun j => LightResidues.residue M 1 ((GlobalKeyEnumeration.globalKeys h J).getD j 0))
      (GlobalKeyEnumeration.globalKeys h J).length as.length =
      GlobalKeyOffset.wantedCount M as h J d := by
  rw [count_modulo M hM,GlobalKeyOffset.wantedCount_eq_divisibility,
    GlobalKeyOffset.keys_length_records]
  apply Finset.sum_congr rfl
  intro i _
  apply Fintype.sum_equiv (GlobalKeyOffset.recordEquiv h J)
  intro j
  simp only [GlobalKeyOffset.key_getD_record]

theorem selected_join_bound (M : ℕ) [NeZero M] (P : ℤ) (xs : List ℤ) (h J : ℕ) :
    M*count
      (fun i => LightResidues.residue M 1
        ((RawAKeyLists.keys P xs).getD i 0+RawAKeyLists.selected M P xs h J))
      (fun j => LightResidues.residue M 1 ((GlobalKeyEnumeration.globalKeys h J).getD j 0))
      (GlobalKeyEnumeration.globalKeys h J).length (RawAKeyLists.keys P xs).length ≤
      3*xs.length*(GlobalEncoding.scheduleSize h^J*LocalCoverBounds.outputCount (512*h) h^J) := by
  rw [count_global M (Nat.pos_of_ne_zero (NeZero.ne M)),RawAKeyLists.wantedCount_eq_guardedCount]
  exact RawAKeyLists.selected_guarded_bound M P xs h J

end ThreeSum.WantedPairs
