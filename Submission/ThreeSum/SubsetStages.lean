import Submission.ThreeSum.Subset
import Submission.ThreeSum.SubsetAddress

/-!
# Canonical suffix stages of a compact zeta table

Stage `j` has processed exactly the last `j` coordinates. Advancing one
stage is one ordinary zeta pass. Every value and every predecessor used
by these stages remains inside the same cardinality downset.
-/

namespace ThreeSum.SubsetStages

open Finset

/-- The last `j` coordinates of the width-`L` universe. -/
def suffix (L j : ℕ) : Finset (Fin L) := univ.filter fun a => L-j ≤ a.val

@[simp] theorem mem_suffix {L j : ℕ} (a : Fin L) : a ∈ suffix L j ↔ L-j ≤ a.val := by
  simp [suffix]

@[simp] theorem suffix_zero (L : ℕ) : suffix L 0 = ∅ := by
  ext a
  simp only [mem_suffix,Nat.sub_zero,not_le,Finset.notMem_empty,iff_false]
  exact a.isLt

@[simp] theorem suffix_all (L : ℕ) : suffix L L = univ := by
  ext a
  simp [mem_suffix]

def nextCoord {L : ℕ} (j : ℕ) (hj : j < L) : Fin L := ⟨L-1-j,by omega⟩

theorem nextCoord_not_mem {L j : ℕ} (hj : j < L) : nextCoord j hj ∉ suffix L j := by
  simp only [mem_suffix,nextCoord]
  omega

theorem suffix_succ {L j : ℕ} (hj : j < L) :
    suffix L (j+1) = insert (nextCoord j hj) (suffix L j) := by
  ext a
  simp only [mem_suffix,Finset.mem_insert,Fin.ext_iff,nextCoord]
  omega

def stageValue {L : ℕ} (f : Finset (Fin L) → ℤ) (j : ℕ) : Finset (Fin L) → ℤ :=
  Subset.partialZeta (suffix L j) f

@[simp] theorem stageValue_zero {L : ℕ} (f : Finset (Fin L) → ℤ) : stageValue f 0 = f := by
  funext S
  simp [stageValue,Subset.partialZeta_empty]

theorem stageValue_succ {L j : ℕ} (f : Finset (Fin L) → ℤ) (hj : j < L) :
    stageValue f (j+1) = Subset.zetaStep (nextCoord j hj) (stageValue f j) := by
  funext S
  rw [stageValue,suffix_succ hj]
  exact Subset.partialZeta_insert f S (suffix L j) (nextCoord j hj) (nextCoord_not_mem hj)

@[simp] theorem stageValue_all {L : ℕ} (f : Finset (Fin L) → ℤ) :
    stageValue f L = Subset.zeta f := by
  funext S
  have he : S \ univ = (∅ : Finset (Fin L)) := by
    ext a
    simp
  simp [stageValue,Subset.partialZeta,Subset.zeta,he]

/-- The absolute bound is derived from the original input values; no bound
on any intermediate transform is supplied as an extra assumption. -/
theorem stageValue_abs_le {L cut U : ℕ} (f : Finset (Fin L) → ℤ)
    (hf : ∀ S, S.card ≤ cut → |f S| ≤ U) :
    ∀ j ≤ L, ∀ S, S.card ≤ cut → |stageValue f j S| ≤ ((2^j*U : ℕ) : ℤ) := by
  intro j
  induction j with
  | zero =>
    intro hj S hS
    simpa only [stageValue_zero,pow_zero,one_mul] using hf S hS
  | succ j ih =>
    intro hj S hS
    have hjL : j < L := by omega
    have h₁ := ih (by omega) S hS
    have h₂ := ih (by omega) (S.erase (nextCoord j hjL))
      (Subset.zetaStep_stays_in_downset S (nextCoord j hjL) cut hS)
    have hdouble : ((2^(j+1)*U : ℕ) : ℤ) =
        ((2^j*U : ℕ) : ℤ)+((2^j*U : ℕ) : ℤ) := by
      push_cast
      rw [pow_succ]
      ring
    rw [stageValue_succ f hjL,Subset.zetaStep,hdouble]
    split
    · exact (abs_add_le _ _).trans (add_le_add h₁ h₂)
    · exact h₁.trans (by have hnonneg : (0 : ℤ) ≤ ((2^j*U : ℕ) : ℤ) := Int.natCast_nonneg _; omega)

/-- A forced prefix can be read directly from its stored suffix stage. -/
theorem stageValue_forced_prefix {L : ℕ} (f : Finset (Fin L) → ℤ)
    (j : ℕ) (pre tail : Finset (Fin L))
    (hp : Disjoint pre (suffix L j)) (ht : tail ⊆ suffix L j) :
    stageValue f j (pre ∪ tail) = ∑ x ∈ tail.powerset, f (pre ∪ x) :=
  Subset.partialZeta_forced_prefix f (suffix L j) pre tail hp ht

end ThreeSum.SubsetStages
