import Submission.ThreeSum.LightReportingGatherPair
import Submission.ThreeSum.ReportingHostPositive

/-! # Actual gathered positive mask arrays are the exact original next-prefix list -/

namespace ThreeSum.LightReportingPositiveMasks

open Light Finset ThreeSum.SubsetAddress
open BlockRows BlockIndexedQuery BlockForced StoredReporting GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open LightBlockChildrenIndexed ReportingHostPositive

set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false

theorem ofFn_getD_map {α β : Type*} (xs : List α) (fallback : α) (f : α → β) :
    List.ofFn (fun i : Fin xs.length => f (xs[i.val]?.getD fallback)) = xs.map f := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  have hi'' : i < xs.length := by simpa only [List.length_map] using hi'
  simp only [List.getElem_ofFn,List.getElem_map,List.getElem?_eq_getElem hi'',Option.getD_some]

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def selectedIndices {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k < J) : List ℕ :=
  LightReportingFilter.selected (fun i => prefixQuery I w (k+1) (childAt w.2.2 pre hk i)) (groupSize h)

theorem selected_index_lt {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k < J)
    {i : ℕ} (hi : i < (selectedIndices I w pre hk).length) :
    (selectedIndices I w pre hk)[i]?.getD 0 < groupSize h := by
  rw [List.getElem?_eq_getElem hi,Option.getD_some]
  exact (LightReportingFilter.mem_selected _ _ _).mp (List.getElem_mem hi) |>.1

theorem program_meets {μ : ℕ → ℤ} {h J k indices srcL srcR dstL dstR d : ℕ}
    (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (pre : List (Finset (Fin (512*h)))) (hk : k < J)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hindices : indices+(selectedIndices I w pre hk).length ≤ lim.space)
    (hsrcL : srcL+groupSize h ≤ lim.space) (hsrcR : srcR+groupSize h ≤ lim.space)
    (hdstL : dstL+(selectedIndices I w pre hk).length ≤ lim.space)
    (hdstR : dstR+(selectedIndices I w pre hk).length ≤ lim.space)
    (hsepIL : Apart indices (selectedIndices I w pre hk).length dstL (selectedIndices I w pre hk).length)
    (hsepIR : Apart indices (selectedIndices I w pre hk).length dstR (selectedIndices I w pre hk).length)
    (hsepLL : Apart srcL (groupSize h) dstL (selectedIndices I w pre hk).length)
    (hsepRL : Apart srcR (groupSize h) dstL (selectedIndices I w pre hk).length)
    (hsepRR : Apart srcR (groupSize h) dstR (selectedIndices I w pre hk).length)
    (hsepOut : Apart dstL (selectedIndices I w pre hk).length dstR (selectedIndices I w pre hk).length)
    (hreadI : SegN μ indices (selectedIndices I w pre hk))
    (hreadL : SegN μ srcL ((childPrefixes w.2.2 pre hk).map fun next =>
      subsetMask (leftPrefix (k+1) (prefixRows (J := J) next))))
    (hreadR : SegN μ srcR ((childPrefixes w.2.2 pre hk).map fun next =>
      subsetMask (rightPrefix (k+1) (outputRows w.2.2) (prefixRows (J := J) next))))
    (hword : ((2^(J*(512*h)+1) : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim LightReportingGatherPair.program 1 d
      [indices,srcL,srcR,(selectedIndices I w pre hk).length,groupSize h,dstL,dstR]
      μ (LightReportingGatherPair.time (selectedIndices I w pre hk).length)
      (fun _ ν =>
        SegN ν dstL ((positiveChildren I w pre hk).map fun next =>
          subsetMask (leftPrefix (k+1) (prefixRows (J := J) next))) ∧
        SegN ν dstR ((positiveChildren I w pre hk).map fun next =>
          subsetMask (rightPrefix (k+1) (outputRows w.2.2) (prefixRows (J := J) next))) ∧
        SameOutside2 μ ν dstL (selectedIndices I w pre hk).length dstR (selectedIndices I w pre hk).length) := by
  let index : ℕ → ℕ := fun i => (selectedIndices I w pre hk)[i]?.getD 0
  let left : ℕ → ℤ := fun i => (subsetMask (leftPrefix (k+1) (prefixRows (J := J) (childAt w.2.2 pre hk i))) : ℤ)
  let right : ℕ → ℤ := fun i => (subsetMask (rightPrefix (k+1) (outputRows w.2.2)
    (prefixRows (J := J) (childAt w.2.2 pre hk i))) : ℤ)
  have hI (i : ℕ) (hi : i < (selectedIndices I w pre hk).length) : μ (indices+i) = (index i : ℤ) := by
    have hh := hreadI.getElem hi
    simpa only [index,List.getElem?_eq_getElem hi,Option.getD_some] using hh
  have hL (i : ℕ) (hi : i < groupSize h) : μ (srcL+i) = left i := by
    unfold left
    rw [childAt_eq_get w.2.2 pre hk i hi]
    have hh := hreadL.getElem (i := i) (by simpa only [List.length_map,childPrefixes_length] using hi)
    simpa only [List.getElem_map] using hh
  have hR (i : ℕ) (hi : i < groupSize h) : μ (srcR+i) = right i := by
    unfold right
    rw [childAt_eq_get w.2.2 pre hk i hi]
    have hh := hreadR.getElem (i := i) (by simpa only [List.length_map,childPrefixes_length] using hi)
    simpa only [List.getElem_map] using hh
  have hmask (U : Finset (Fin (J*(512*h)))) : |(subsetMask U : ℤ)| ≤ lim.word := by
    rw [Int.abs_natCast]
    exact (Int.ofNat_le.mpr ((subsetMask_isMask U).1.le.trans
      (Nat.pow_le_pow_right (by decide) (by omega)))).trans hword
  have hh := LightReportingGatherPair.program_meets (d := d) (μ := μ) index left right
    hw hindices hsrcL hsrcR hdstL hdstR hsepIL hsepIR hsepLL hsepRL hsepRR hsepOut
    (fun i hi => selected_index_lt I w pre hk hi) hI hL hR
    (fun _ _ => hmask _) (fun _ _ => hmask _) hd
  have heL : List.ofFn (fun i : Fin (selectedIndices I w pre hk).length => left (index i.val)) =
      (((positiveChildren I w pre hk).map fun next => subsetMask
        (leftPrefix (k+1) (prefixRows (J := J) next))).map fun x : ℕ => (x : ℤ)) := by
    rw [ofFn_getD_map (selectedIndices I w pre hk) 0 left]
    simp only [positiveChildren,selectedIndices,List.map_map,left,Function.comp_def]
  have heR : List.ofFn (fun i : Fin (selectedIndices I w pre hk).length => right (index i.val)) =
      (((positiveChildren I w pre hk).map fun next => subsetMask
        (rightPrefix (k+1) (outputRows w.2.2) (prefixRows (J := J) next))).map fun x : ℕ => (x : ℤ)) := by
    rw [ofFn_getD_map (selectedIndices I w pre hk) 0 right]
    simp only [positiveChildren,selectedIndices,List.map_map,right,Function.comp_def]
  rw [heL,heR] at hh
  exact hh

end ThreeSum.LightReportingPositiveMasks
