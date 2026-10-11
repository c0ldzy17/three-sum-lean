import Submission.ThreeSum.WantedRecordCoverage
import Submission.ThreeSum.DenseGuard
import Mathlib.Data.List.FinRange

/-!
# Distinct wanted labels in the actual emitted array

The join's physical slots decode injectively, even when original integer
values or key values repeat. Consequently every prefix of the actual
array is a valid distinct-label input to the cumulative dense guard.
-/

namespace ThreeSum.DenseGuardWanted

open Light WantedRecordOrder

def leftIndex (μ : ℕ → ℤ) (free NL NR M slot : ℕ) : ℕ :=
  (μ (LightWantedSetup.pairBase free NL NR M+2*slot)).toNat

def rightIndex (μ : ℕ → ℤ) (free NL NR M slot : ℕ) : ℕ :=
  (μ (LightWantedSetup.pairBase free NL NR M+2*slot+1)).toNat

theorem pair_indices_injective {μ : ℕ → ℤ} {free NL NR M k k' : ℕ}
    {left right : ℕ → ℤ} {shift : ℤ}
    (H : LightWantedSetup.Output μ free M left right NL NR shift)
    (hk : k < (μ free).toNat) (hk' : k' < (μ free).toNat)
    (hl : leftIndex μ free NL NR M k=leftIndex μ free NL NR M k')
    (hr : rightIndex μ free NL NR M k=rightIndex μ free NL NR M k') : k=k' := by
  rcases H with ⟨hcount,_,_,_,ps,hlen,hn,_,hseg⟩
  have hk0 : k < ps.length := by rw [hlen]; simpa only [hcount,Int.toNat_natCast] using hk
  have hk1 : k' < ps.length := by rw [hlen]; simpa only [hcount,Int.toNat_natCast] using hk'
  have hv (i : ℕ) (hi : i < ps.length) :
      (leftIndex μ free NL NR M i,rightIndex μ free NL NR M i)=ps.get ⟨i,hi⟩ := by
    obtain ⟨hL,hR⟩ := segment_pair hseg hi
    simp only [leftIndex,rightIndex,hL,hR,Int.toNat_natCast,
      List.getD_eq_getElem _ _ hi,List.get_eq_getElem]
  have hp : ps.get ⟨k,hk0⟩=ps.get ⟨k',hk1⟩ :=
    (hv k hk0).symm.trans ((Prod.ext hl hr).trans (hv k' hk1))
  exact congrArg Fin.val (hn.injective_get hp)

theorem output_bounds {μ : ℕ → ℤ} {free M P h J slot : ℕ} {shift : ℤ} {xs : List ℤ}
    (H : LightWantedSetup.Output μ free M (LightGuardedWanted.left P xs)
      (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J) shift)
    (hk : slot < (μ free).toNat) :
    leftIndex μ free (3*xs.length) (LightGuardedWanted.totalKeys h J) M slot < 3*xs.length ∧
      rightIndex μ free (3*xs.length) (LightGuardedWanted.totalKeys h J) M slot <
        LightGuardedWanted.totalKeys h J := by
  obtain ⟨i,j,hi,hj,hL,hR,_⟩ := WantedRecordCoverage.output_pair H hk
  simpa only [leftIndex,rightIndex,hL,hR,Int.toNat_natCast] using And.intro hi hj

def labelAt {μ : ℕ → ℤ} {free M P h J : ℕ} {shift : ℤ} {xs : List ℤ}
    (H : LightWantedSetup.Output μ free M (LightGuardedWanted.left P xs)
      (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J) shift)
    (slot : Fin (μ free).toNat) : RawReporting.Wanted h J (Fin xs.length) :=
  label h J (leftIndex μ free (3*xs.length) (LightGuardedWanted.totalKeys h J) M slot.val)
    (rightIndex μ free (3*xs.length) (LightGuardedWanted.totalKeys h J) M slot.val)
    (output_bounds H slot.isLt).1

theorem labelAt_injective {μ : ℕ → ℤ} {free M P h J : ℕ} {shift : ℤ} {xs : List ℤ}
    (H : LightWantedSetup.Output μ free M (LightGuardedWanted.left P xs)
      (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J) shift) :
    Function.Injective (labelAt H) := by
  intro k k' he
  have hp := label_injective (output_bounds H k.isLt).1 (output_bounds H k'.isLt).1
    (output_bounds H k.isLt).2 (output_bounds H k'.isLt).2 he
  exact Fin.ext (pair_indices_injective H k.isLt k'.isLt hp.1 hp.2)

def labels {μ : ℕ → ℤ} {free M P h J : ℕ} {shift : ℤ} {xs : List ℤ}
    (H : LightWantedSetup.Output μ free M (LightGuardedWanted.left P xs)
      (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J) shift) :
    List (RawReporting.Wanted h J (Fin xs.length)) := List.ofFn (labelAt H)

theorem labels_nodup {μ : ℕ → ℤ} {free M P h J : ℕ} {shift : ℤ} {xs : List ℤ}
    (H : LightWantedSetup.Output μ free M (LightGuardedWanted.left P xs)
      (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J) shift) :
    (labels H).Nodup := List.nodup_ofFn_ofInjective (labelAt_injective H)

theorem prefix_nodup {μ : ℕ → ℤ} {free M P h J : ℕ} {shift : ℤ} {xs : List ℤ}
    (H : LightWantedSetup.Output μ free M (LightGuardedWanted.left P xs)
      (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J) shift)
    (n : ℕ) : ((labels H).take n).Nodup := (labels_nodup H).take

theorem prefix_step {μ : ℕ → ℤ} {free M P h J : ℕ} {shift : ℤ} {xs : List ℤ}
    (H : LightWantedSetup.Output μ free M (LightGuardedWanted.left P xs)
      (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J) shift)
    (slot : Fin (μ free).toNat) :
    (labels H).take (slot.val+1)=(labels H).take slot.val++[labelAt H slot] := by
  have hk : slot.val < (labels H).length := by simpa only [labels,List.length_ofFn] using slot.isLt
  rw [List.take_succ_eq_append_getElem hk]
  simp only [labels,List.getElem_ofFn]

theorem labelAt_mem {μ : ℕ → ℤ} {free M P h J : ℕ} {shift : ℤ} {xs : List ℤ}
    (H : LightWantedSetup.Output μ free M (LightGuardedWanted.left P xs)
      (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J) shift)
    (slot : Fin (μ free).toNat) : labelAt H slot ∈ RawAKeyLists.wanted M P xs h J shift := by
  obtain ⟨i,j,hi,_,hL,hR,hm⟩ := WantedRecordCoverage.output_pair H slot.isLt
  simpa only [labelAt,leftIndex,rightIndex,hL,hR,Int.toNat_natCast] using hm

theorem labels_complete {μ : ℕ → ℤ} {free M P h J : ℕ} {shift : ℤ} {xs : List ℤ}
    (H : LightWantedSetup.Output μ free M (LightGuardedWanted.left P xs)
      (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J) shift)
    {w : RawReporting.Wanted h J (Fin xs.length)}
    (hw : w ∈ RawAKeyLists.wanted M P xs h J shift) : w ∈ labels H := by
  obtain ⟨slot,i,j,hi,hk,_,hL,hR,he⟩ := WantedRecordCoverage.output_complete H hw
  apply List.mem_ofFn.mpr
  refine ⟨⟨slot,hk⟩,?_⟩
  simpa only [labelAt,leftIndex,rightIndex,hL,hR,Int.toNat_natCast] using he

end ThreeSum.DenseGuardWanted
