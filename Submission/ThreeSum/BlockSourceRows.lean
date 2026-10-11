import Submission.ThreeSum.LightSourceRowScan
import Submission.ThreeSum.BlockCoefficientRows

/-!
# Global mask bits are the exact local block rows

The physical row scan's cardinality and two raw hashes agree with the local
subsets and one-hot words in `BlockEncoding`. This bridge allows independent
trimming to use the selected map's exact retained bucket-count table.
-/

namespace ThreeSum.BlockSourceRows

open Finset BlockRows BlockIndex LightSourceRowScan
open LocalHashMoments
open scoped BigOperators

set_option maxHeartbeats 1000000

def bits {J L : ℕ} (S : Finset (Coord J L)) (j : Fin J) (i : ℕ) : ℕ :=
  LightMaskBits.bit (J*L) (SubsetAddress.subsetMask (indexSet S)) (j.val*L+i)

theorem bits_fin {J L : ℕ} (S : Finset (Coord J L)) (j : Fin J) (i : Fin L) :
    bits S j i.val = if i ∈ row S j then 1 else 0 := by
  have hh := LightMaskBits.bit_subsetMask (indexSet S) (coordEquiv J L ⟨j,i⟩)
  simpa only [bits,coordEquiv_val,mem_indexSet,mem_row] using hh

theorem count_eq_card {J L : ℕ} (S : Finset (Coord J L)) (j : Fin J) :
    count (bits S j) L = (row S j).card := by
  rw [count,← Fin.sum_univ_eq_sum_range]
  have he : row S j = (univ : Finset (Fin L)).filter (fun i => i ∈ row S j) := by
    ext i
    simp
  conv_rhs => rw [he,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i hi
  exact bits_fin S j i

theorem hash_eq_eval {L : ℕ} (s : Finset (Fin L)) (b : ℕ → ℕ)
    (w0 w1 : Fin L → ℕ) (hb : ∀ i : Fin L, b i.val = if i ∈ s then 1 else 0) :
    hash b (OneHotMask.extend w0) (OneHotMask.extend w1) L =
      OneHotMask.eval (OneHotMask.extend w0) (OneHotMask.extend w1)
        L (SubsetAddress.subsetMask s) := by
  unfold LightSourceRowScan.hash
  rw [← Fin.sum_univ_eq_sum_range,OneHotMask.eval_subsetMask]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hb i,OneHotMask.extend_fin,OneHotMask.extend_fin]
  by_cases hmem : i ∈ s <;> simp [hmem]

theorem left_hash {h J : ℕ} (S : Finset (Coord J (512*h))) (j : Fin J)
    (w : Weight (512*h) (LocalField h)) :
    (hash (bits S j) (OneHotMask.extend fun i => (w (i,false)).val)
      (OneHotMask.extend fun i => (w (i,true)).val) (512*h) : ℤ) =
      GlobalEncoding.rawHash w (LocalGraph.leftWord (row S j)) := by
  rw [hash_eq_eval (row S j) (bits S j) _ _ (bits_fin S j),OneHotMask.eval_rawLeft]

theorem right_hash {h J : ℕ} (S : Finset (Coord J (512*h))) (j : Fin J)
    (w : Weight (512*h) (LocalField h)) :
    (hash (bits S j) (OneHotMask.extend fun i => (w (i,true)).val)
      (OneHotMask.extend fun i => (w (i,false)).val) (512*h) : ℤ) =
      GlobalEncoding.rawHash w (LocalGraph.rightWord (row S j)) := by
  rw [hash_eq_eval (row S j) (bits S j) _ _ (bits_fin S j),OneHotMask.eval_rawRight]

end ThreeSum.BlockSourceRows
