import Submission.ThreeSum.TernaryOriginalSpan

/-! Range-ordered field coefficients for the actual span catalog constructor. -/
noncomputable section
namespace ThreeSum.TernaryOriginalSpanCatalog
open Finset
set_option maxHeartbeats 2000000

variable {p J : ℕ}

def values (p : ℕ) : List (Fin J → ZMod p) → List (Fin J → ZMod p)
  | [] => [0]
  | row::rows => (List.range p).flatMap fun a : ℕ =>
      (values p rows).map fun old => (a : ZMod p) • row+old

theorem values_length (rows : List (Fin J → ZMod p)) : (values p rows).length=p^rows.length := by
  induction rows with
  | nil => simp [values]
  | cons row rows ih =>
    simp only [values,List.length_flatMap,List.length_map,ih,List.length_cons]
    simp [pow_succ,Nat.mul_comm]

theorem mem_values [Fact p.Prime] (rows : List (Fin J → ZMod p)) (v : Fin J → ZMod p) :
    v∈values p rows ↔ v∈Submodule.span (ZMod p) {w | w∈rows} := by
  induction rows generalizing v with
  | nil => simp [values]
  | cons row rows ih =>
    have hs : {w | w∈row::rows}=insert row {w | w∈rows} := by
      ext w
      simp only [Set.mem_setOf_eq,Set.mem_insert_iff,List.mem_cons]
    rw [hs]
    refine Iff.trans ?_ (Submodule.mem_span_insert (R := ZMod p) (x := v) (y := row)
      (s := {w | w∈rows})).symm
    simp only [values,List.mem_flatMap,List.mem_map,List.mem_range]
    constructor
    · rintro ⟨a,ha,w,hw,rfl⟩
      exact ⟨(a : ZMod p),w,(ih w).mp hw,rfl⟩
    · rintro ⟨a,w,hw,he⟩
      refine ⟨a.val,ZMod.val_lt a,w,(ih w).mpr hw,?_⟩
      simpa only [ZMod.natCast_zmod_val] using he.symm

theorem representative_axpy [NeZero p] (a : ℕ) (row old : Fin J → ZMod p) (i : Fin J) :
    (((a : ZMod p) • row+old) i).val=((old i).val+a*(row i).val)%p := by
  have he : (((old i).val+a*(row i).val : ℕ) : ZMod p)=((a : ZMod p) • row+old) i := by
    simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_zmod_val,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [←he,ZMod.val_natCast]

end ThreeSum.TernaryOriginalSpanCatalog
