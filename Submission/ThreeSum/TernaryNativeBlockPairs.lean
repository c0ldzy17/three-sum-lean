import Submission.ThreeSum.TernaryRepeatedWords
import Submission.ThreeSum.TernaryPhysicalTupleRecords

noncomputable section
namespace ThreeSum.TernaryNativeBlockPairs
open Finset TernaryJointType TernaryCoverLocal TernaryRepeatedWords
attribute [local instance] Classical.propDecidable

variable {r L F : ℕ} {α π : DigitType}

theorem canonical_adds_iff (a b q : Fin r→TritWord L) :
    TernaryConvolution.Adds (canonical a) (canonical b) (canonical q) ↔
      ∀ i, PointwiseSum (a i) (b i) (q i) := by
  constructor
  · intro h i j
    have hh := h (finProdFinEquiv (i.rev,j))
    simpa only [canonical,word_at,Fin.rev_rev] using hh
  · exact canonical_adds a b q

theorem canonical_injective : Function.Injective (@canonical r L) := by
  intro a b h
  funext i j
  have hh := congrFun h (finProdFinEquiv (i.rev,j))
  simpa only [canonical,word_at,Fin.rev_rev] using hh

def occurrenceCode (occ : Fin r→Fin F) : ℕ :=
  Nat.ofDigits F (List.ofFn fun i => (Fintype.equivFin (Fin F) (occ i)).val)

/-- The physical same-map bank code retains every local map occurrence. -/
theorem occurrenceCode_injective : Function.Injective (@occurrenceCode r F) := by
  intro a b h
  by_cases hF : 1<F
  · have hl : (List.ofFn fun i => (Fintype.equivFin (Fin F) (a i)).val)=
        List.ofFn fun i => (Fintype.equivFin (Fin F) (b i)).val := by
      apply Nat.ofDigits_inj_of_len_eq hF (by simp)
      · intro n hn
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hn
        simpa using (Fintype.equivFin (Fin F) (a i)).isLt
      · intro n hn
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hn
        simpa using (Fintype.equivFin (Fin F) (b i)).isLt
      · exact h
    funext i
    apply (Fintype.equivFin (Fin F)).injective
    apply Fin.ext
    have hi := congrArg (fun xs : List ℕ => xs[i.val]?) hl
    simpa using hi
  · funext i
    apply Fin.ext
    have ha := (a i).isLt
    have hb := (b i).isLt
    omega

/-- An actual canonical word pair reconstructs each retained local partition. -/
def edges (a b : Fin r→{w // w∈vertices L α}) (q : Fin r→{w // w∈vertices L π})
    (h : TernaryConvolution.Adds (canonical fun i => (a i).val)
      (canonical fun i => (b i).val) (canonical fun i => (q i).val)) : Fin r→LocalEdge L α π :=
  fun i => ⟨((a i).val,(b i).val,(q i).val),by
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_,?_,?_,(canonical_adds_iff _ _ _).mp h i⟩
    · exact (mem_filter.mp (a i).property).2
    · exact (mem_filter.mp (b i).property).2
    · exact (mem_filter.mp (q i).property).2⟩

@[simp] theorem edges_left (a b : Fin r→{w // w∈vertices L α})
    (q : Fin r→{w // w∈vertices L π}) (h) (i : Fin r) : left (edges a b q h i)=(a i).val := rfl
@[simp] theorem edges_right (a b : Fin r→{w // w∈vertices L α})
    (q : Fin r→{w // w∈vertices L π}) (h) (i : Fin r) : right (edges a b q h i)=(b i).val := rfl
@[simp] theorem edges_output (a b : Fin r→{w // w∈vertices L α})
    (q : Fin r→{w // w∈vertices L π}) (h) (i : Fin r) : output (edges a b q h i)=(q i).val := rfl

end ThreeSum.TernaryNativeBlockPairs
