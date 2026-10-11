import Submission.ThreeSum.GlobalKeyEnumeration
import Submission.ThreeSum.BlockCoefficientRows

/-!
# Local output keys from ordinary stored masks and coefficient rows

This identifies the two nonnegative masked sums used by the imperative
local-key program with the unchanged signed `GlobalEncoding.rawOutput`.
-/

namespace ThreeSum.OutputKeyMasks

open GlobalEncoding LocalHashMoments LocalCoverBounds
open OneHotMask SubsetAddress
open scoped BigOperators

theorem extend_zero (L : ℕ) : extend (fun _ : Fin L => 0)=(fun _ : ℕ => 0) := by
  funext i
  simp [extend]

theorem eval_outside {L : ℕ} (Q : Finset (Fin L)) (w : Fin L → ℕ) :
    (eval (extend w) (fun _ => 0) L (subsetMask Q) : ℤ) =
      ∑ i : Fin L, if i ∈ Q then (0 : ℤ) else (w i : ℤ) := by
  rw [← extend_zero L,eval_subsetMask]
  push_cast
  rfl

theorem eval_difference {h L : ℕ} (w : Weight L (LocalField h))
    (Q : Finset (Fin L)) :
    (eval (extend fun i => (w (i,true)).val) (fun _ => 0) L (subsetMask Q) : ℤ)-
      (eval (extend fun i => (w (i,false)).val) (fun _ => 0) L (subsetMask Q) : ℤ)
      = rawOutput w Q := by
  rw [eval_outside,eval_outside,← Finset.sum_sub_distrib]
  unfold rawOutput
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ Q <;> simp [hi]

theorem mapRow_eq {h : ℕ} (b : Bool) (o : Occurrence h) :
    BlockCoefficientRows.mapRow h b o.val =
      extend (fun i : Fin (512*h) => (mapAt h o (i,b)).val) := by
  simp only [BlockCoefficientRows.mapRow,o.isLt,dite_true]

theorem indexed_blockKey {h : ℕ} (o : Occurrence h)
    (i : Fin ((512*h).choose (2*h))) :
    (eval (BlockCoefficientRows.mapRow h true o.val) (fun _ => 0) (512*h)
      (LocalMaskGraph.maskAt (512*h) (2*h) i.val) : ℤ)-
      (eval (BlockCoefficientRows.mapRow h false o.val) (fun _ => 0) (512*h)
      (LocalMaskGraph.maskAt (512*h) (2*h) i.val) : ℤ) =
      blockKey (o,GlobalKeyEnumeration.layerRecord h i) := by
  rw [mapRow_eq,mapRow_eq,← LocalMaskGraph.subsetMask_setAt i.isLt,eval_difference]
  rfl

end ThreeSum.OutputKeyMasks
