import Submission.ThreeSum.TernaryOriginalRowMenu

/-! Literal recursive enumeration of the previous ORIGINAL digit-row span.
The list has `p^j` rows including repetitions, so the charged histogram-size
enumeration tests admissibility without a rank primitive or field advice. -/

noncomputable section
namespace ThreeSum.TernaryOriginalSpan

variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V]

def values (K : Type*) [Field K] [Fintype K] [DecidableEq K] [Module K V] : List V → List V
  | [] => [0]
  | row::rows => (Finset.univ : Finset K).toList.flatMap fun a =>
      (values K rows).map fun v => a • row+v

theorem values_length (rows : List V) : (values K rows).length = Fintype.card K^rows.length := by
  induction rows with
  | nil => simp [values]
  | cons row rows ih =>
    simp only [values,List.length_flatMap,List.length_map,ih,List.length_cons]
    simp [pow_succ,Nat.mul_comm]

theorem mem_values (rows : List V) (v : V) :
    v ∈ values K rows ↔ v ∈ Submodule.span K {w | w ∈ rows} := by
  induction rows generalizing v with
  | nil => simp [values]
  | cons row rows ih =>
    have hset : {w | w ∈ row::rows} = insert row {w | w ∈ rows} := by
      ext w
      simp only [Set.mem_setOf_eq,Set.mem_insert_iff,List.mem_cons]
    rw [hset]
    refine Iff.trans ?_ (Submodule.mem_span_insert (R := K) (x := v) (y := row)
      (s := {w | w ∈ rows})).symm
    simp only [values,List.mem_flatMap,List.mem_map,Finset.mem_toList,Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨a,w,hw,rfl⟩
      exact ⟨a,w,(ih w).mp hw,rfl⟩
    · rintro ⟨a,w,hw,rfl⟩
      exact ⟨a,w,(ih w).mpr hw,rfl⟩

theorem not_mem_values_iff (rows : List V) (v : V) :
    v ∉ values K rows ↔ v ∉ Submodule.span K {w | w ∈ rows} :=
  not_congr (mem_values rows v)

end ThreeSum.TernaryOriginalSpan
