import Submission.ThreeSum.ReportingHostPairEnumeration
import Submission.ThreeSum.RadixKeyLists
import Submission.ThreeSum.BlockMaskLayout

/-!
# Positional products are the physical masks of the complete shared prefix catalog

Both left and right products use one common tuple list. Every original valid
prefix has a key in that list, and the tuple encodes exactly its original
row-major global masks.
-/

namespace ThreeSum.ReportingHostPrefixMasks

open Finset ThreeSum.SubsetAddress BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open BlockForced
open ReportingHostPrefixCatalog ReportingHostPairEnumeration
open scoped BigOperators

set_option maxHeartbeats 500000

variable {α : Type*}

theorem positionalHash_ofFn (p : ℤ) (raw : α → ℤ) {k : ℕ} (f : Fin k → α) :
    Radix.positionalHash p raw (List.ofFn f) = ∑ i : Fin k, p^i.val*raw (f i) := by
  induction k with
  | zero => simp [Radix.positionalHash]
  | succ k ih =>
    rw [List.ofFn_succ,Radix.positionalHash,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,one_mul,Fin.val_succ,pow_succ]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem mask_rows_ofFin {J L k : ℕ} (hk : k ≤ J) (u : Fin k → Finset (Fin L)) :
    subsetMask (leftPrefix k (fun i : Fin J => if hi : i.val < k then u ⟨i.val,hi⟩ else ∅)) =
      ∑ i : Fin k, 2^(i.val*L)*subsetMask (u i) := by
  rw [leftPrefix,prefixLeft,mask_join]
  refine Finset.sum_bij (fun i hi => (⟨i.val,mem_prefixIndices.mp hi⟩ : Fin k)) ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_univ _
  · intro i hi j hj he
    exact Fin.ext (congrArg (fun a : Fin k => a.val) he)
  · intro i hi
    exact ⟨⟨i.val,i.isLt.trans_le hk⟩,mem_prefixIndices.mpr i.isLt,rfl⟩
  · intro i hi
    simp only [rowMask,dif_pos (mem_prefixIndices.mp hi)]

def tuple {h k : ℕ} (p : Prefix h k) : List (Finset (Fin (512*h)) × Finset (Fin (512*h))) :=
  List.ofFn fun i => (p i).val

theorem tuple_length {h k : ℕ} (p : Prefix h k) : (tuple p).length = k := by simp [tuple]

theorem leftSet_mask {h J k : ℕ} (hk : k ≤ J) (p : Prefix h k) :
    subsetMask (leftSet (J := J) p) = ∑ i : Fin k, 2^(i.val*(512*h))*subsetMask (p i).val.1 := by
  unfold leftSet leftRows
  exact mask_rows_ofFin (J := J) (L := 512*h) (k := k) hk (fun i => (p i).val.1)

theorem rightSet_mask {h J k : ℕ} (hk : k ≤ J) (p : Prefix h k) :
    subsetMask (rightSet (J := J) p) = ∑ i : Fin k, 2^(i.val*(512*h))*subsetMask (p i).val.2 := by
  unfold rightSet rightRows
  exact mask_rows_ofFin (J := J) (L := 512*h) (k := k) hk (fun i => (p i).val.2)

theorem leftHash_eq_mask {h J k : ℕ} (hk : k ≤ J) (p : Prefix h k) :
    Radix.positionalHash ((2^(512*h) : ℕ) : ℤ) (fun q => (subsetMask q.1 : ℤ)) (tuple p) =
      (subsetMask (leftSet (J := J) p) : ℤ) := by
  rw [tuple,positionalHash_ofFn,leftSet_mask hk]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  simp only [← pow_mul,Nat.mul_comm]

theorem rightHash_eq_mask {h J k : ℕ} (hk : k ≤ J) (p : Prefix h k) :
    Radix.positionalHash ((2^(512*h) : ℕ) : ℤ) (fun q => (subsetMask q.2 : ℤ)) (tuple p) =
      (subsetMask (rightSet (J := J) p) : ℤ) := by
  rw [tuple,positionalHash_ofFn,rightSet_mask hk]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  simp only [← pow_mul,Nat.mul_comm]

theorem tuple_mem {h k : ℕ} (p : Prefix h k) :
    tuple p ∈ RadixKeyLists.tuples (pairs (512*h) h) k := by
  apply (RadixKeyLists.mem_tuples _ _ _).mpr
  refine ⟨tuple_length p,?_⟩
  intro q hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  exact (pairs_mem _).mpr (p i).property

theorem tuple_injective {h k : ℕ} : Function.Injective (@tuple h k) := by
  intro p q he
  funext i
  apply Subtype.ext
  have hh := congrArg (fun xs => xs[i.val]?) he
  simpa only [tuple,List.getElem?_ofFn,dif_pos i.isLt,Option.some.injEq] using hh

def ofTuple {h k : ℕ} (xs : List (Finset (Fin (512*h)) × Finset (Fin (512*h))))
    (hlen : xs.length = k) (hmem : ∀ q ∈ xs, q ∈ pairs (512*h) h) : Prefix h k :=
  fun i => ⟨xs[i.val]'(by rw [hlen]; exact i.isLt),
    (pairs_mem _).mp (hmem _ (List.getElem_mem (by rw [hlen]; exact i.isLt)))⟩

theorem tuple_ofTuple {h k : ℕ} (xs : List (Finset (Fin (512*h)) × Finset (Fin (512*h))))
    (hlen : xs.length = k) (hmem : ∀ q ∈ xs, q ∈ pairs (512*h) h) :
    tuple (ofTuple xs hlen hmem) = xs := by
  apply List.ext_getElem
  · simp [tuple,hlen]
  · intro i hi hi'
    simp [tuple,ofTuple]

theorem tuple_mem_iff {h k : ℕ} (xs : List (Finset (Fin (512*h)) × Finset (Fin (512*h)))) :
    xs ∈ RadixKeyLists.tuples (pairs (512*h) h) k ↔ ∃ p : Prefix h k, tuple p = xs := by
  constructor
  · intro hx
    obtain ⟨hlen,hmem⟩ := (RadixKeyLists.mem_tuples _ _ _).mp hx
    exact ⟨ofTuple xs hlen hmem,tuple_ofTuple xs hlen hmem⟩
  · rintro ⟨p,rfl⟩
    exact tuple_mem p

theorem maskPair_injective {h J k : ℕ} (hk : k ≤ J) :
    Function.Injective (fun p : Prefix h k =>
      (subsetMask (leftSet (J := J) p),subsetMask (rightSet (J := J) p))) := by
  intro p q he
  have hL := subsetMask_injective (J*(512*h)) (congrArg Prod.fst he)
  have hR := subsetMask_injective (J*(512*h)) (congrArg Prod.snd he)
  funext i
  apply Subtype.ext
  apply Prod.ext
  · have hh := congrArg (fun S => row (unindexSet S) (⟨i.val,i.isLt.trans_le hk⟩ : Fin J)) hL
    simpa only [leftSet,leftPrefix,unindex_index,prefixLeft,row_join,mem_prefixIndices,
      dif_pos i.isLt,leftRows,i.isLt,ite_true,dite_true] using hh
  · have hh := congrArg (fun S => row (unindexSet S) (⟨i.val,i.isLt.trans_le hk⟩ : Fin J)) hR
    simpa only [rightSet,leftPrefix,unindex_index,prefixLeft,row_join,mem_prefixIndices,
      dif_pos i.isLt,rightRows,i.isLt,ite_true,dite_true] using hh

end ThreeSum.ReportingHostPrefixMasks
