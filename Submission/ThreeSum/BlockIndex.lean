import Submission.ThreeSum.OneHotMask
import Submission.ThreeSum.BlockEncoding
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Explicit row-major encoding of the block ground set

Block coordinates are numbered by `block * width + coordinate`. The
equivalence connects compact machine-mask tables on `Fin (J*L)` with the
sigma-typed block sets in the reporting proof. Flattened one-hot coefficients
already include their positional radix factors.
-/

namespace ThreeSum.BlockIndex

open Finset BlockRows BlockEncoding GlobalEncoding LocalHashMoments LocalCoverBounds
open scoped BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

def coordEquiv (J L : ℕ) : Coord J L ≃ Fin (J*L) :=
  (Equiv.sigmaEquivProd (Fin J) (Fin L)).trans finProdFinEquiv

@[simp] theorem coordEquiv_val {J L : ℕ} (i : Fin J) (x : Fin L) :
    (coordEquiv J L ⟨i,x⟩).val = i.val*L+x.val := by
  simp [coordEquiv, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

def indexSet {J L : ℕ} (S : Finset (Coord J L)) : Finset (Fin (J*L)) :=
  S.map (coordEquiv J L).toEmbedding

def unindexSet {J L : ℕ} (S : Finset (Fin (J*L))) : Finset (Coord J L) :=
  S.map (coordEquiv J L).symm.toEmbedding

@[simp] theorem mem_indexSet {J L : ℕ} (S : Finset (Coord J L)) (c : Coord J L) :
    coordEquiv J L c ∈ indexSet S ↔ c ∈ S := by
  simp [indexSet]

@[simp] theorem indexSet_card {J L : ℕ} (S : Finset (Coord J L)) :
    (indexSet S).card = S.card := Finset.card_map _

@[simp] theorem unindex_index {J L : ℕ} (S : Finset (Coord J L)) :
    unindexSet (indexSet S) = S := by
  ext c
  simp [unindexSet,indexSet]

@[simp] theorem index_unindex {J L : ℕ} (S : Finset (Fin (J*L))) :
    indexSet (unindexSet (J := J) (L := L) S) = S := by
  ext c
  simp [unindexSet,indexSet]

theorem indexSet_injective (J L : ℕ) : Function.Injective (@indexSet J L) :=
  Finset.map_injective _

@[simp] theorem indexSet_subset {J L : ℕ} (S T : Finset (Coord J L)) :
    indexSet S ⊆ indexSet T ↔ S ⊆ T := by
  simp [indexSet]

@[simp] theorem indexSet_union {J L : ℕ} (S T : Finset (Coord J L)) :
    indexSet (S∪T) = indexSet S ∪ indexSet T := by
  exact Finset.map_union S T

theorem eval_indexSet {J L : ℕ} (S : Finset (Coord J L))
    (w0 w1 : Coord J L → ℕ) :
    OneHotMask.eval (OneHotMask.extend (w0 ∘ (coordEquiv J L).symm))
      (OneHotMask.extend (w1 ∘ (coordEquiv J L).symm))
      (J*L) (SubsetAddress.subsetMask (indexSet S)) =
      ∑ c : Coord J L, if c ∈ S then w1 c else w0 c := by
  rw [OneHotMask.eval_subsetMask]
  rw [← (coordEquiv J L).sum_comp
    (fun i => if i ∈ indexSet S then (w1 ∘ (coordEquiv J L).symm) i
      else (w0 ∘ (coordEquiv J L).symm) i)]
  apply sum_congr rfl
  intro c _
  simp only [Function.comp_apply, Equiv.symm_apply_apply, mem_indexSet]

theorem positionalHash_ofFn (p : ℤ) {J : ℕ} (f : Fin J → ℤ) :
    Radix.positionalHash p id (List.ofFn f) = ∑ i : Fin J, p^i.val * f i := by
  induction J with
  | zero => simp [Radix.positionalHash]
  | succ J ih =>
    simp only [List.ofFn_succ,Radix.positionalHash, id_eq,ih,
      Fin.sum_univ_succ,Fin.val_zero,pow_zero,one_mul,Fin.val_succ,pow_succ]
    rw [Finset.mul_sum]
    congr 1
    apply sum_congr rfl
    intro i _
    ring

def coefficient {h J : ℕ} (o : Occurrences h J) (b : Bool)
    (c : Coord J (512*h)) : ℕ :=
  localPrime h ^ c.1.val * (mapAt h (o c.1) (c.2,b)).val

def maskHash {h J : ℕ} (o : Occurrences h J) (flip : Bool)
    (S : Finset (Coord J (512*h))) : ℕ :=
  OneHotMask.eval
    (OneHotMask.extend (coefficient o flip ∘ (coordEquiv J (512*h)).symm))
    (OneHotMask.extend (coefficient o (!flip) ∘ (coordEquiv J (512*h)).symm))
    (J*(512*h)) (SubsetAddress.subsetMask (indexSet S))

theorem maskHash_left {h J : ℕ} (o : Occurrences h J)
    (S : Finset (Coord J (512*h))) :
    (maskHash o false S : ℤ) = endpointLeft o S := by
  unfold maskHash
  rw [eval_indexSet]
  unfold endpointLeft
  rw [positionalHash_ofFn]
  push_cast
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro i _
  unfold rawHash
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro x _
  by_cases hx : Sigma.mk i x ∈ S
  · simp [coefficient,LocalGraph.leftWord,mem_row,hx]
  · simp [coefficient,LocalGraph.leftWord,mem_row,hx]

theorem maskHash_right {h J : ℕ} (o : Occurrences h J)
    (S : Finset (Coord J (512*h))) :
    (maskHash o true S : ℤ) = endpointRight o S := by
  unfold maskHash
  rw [eval_indexSet]
  unfold endpointRight
  rw [positionalHash_ofFn]
  push_cast
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro i _
  unfold rawHash
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro x _
  by_cases hx : Sigma.mk i x ∈ S
  · simp [coefficient,LocalGraph.rightWord,mem_row,hx]
  · simp [coefficient,LocalGraph.rightWord,mem_row,hx]

end ThreeSum.BlockIndex
