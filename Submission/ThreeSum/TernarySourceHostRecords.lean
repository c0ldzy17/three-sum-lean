import Submission.ThreeSum.WantedPairs
namespace ThreeSum.TernarySourceHostRecords
open Light

theorem cells_left (ps : List (ℕ × ℕ)) : ∀ i,
    (WantedPairs.cells ps).getD (2*i) 0=((ps.getD i (0,0)).1 : ℤ) := by
  induction ps with
  | nil => intro i; simp [WantedPairs.cells]
  | cons p ps ih =>
    intro i
    cases i with
    | zero => simp [WantedPairs.cells]
    | succ i => simpa [WantedPairs.cells,Nat.mul_succ,List.getD] using ih i

theorem cells_right (ps : List (ℕ × ℕ)) : ∀ i<ps.length,
    (WantedPairs.cells ps).getD (2*i+1) 0=((ps.getD i (0,0)).2 : ℤ) := by
  induction ps with
  | nil => intro i hi; simp at hi
  | cons p ps ih =>
    intro i hi
    cases i with
    | zero => simp [WantedPairs.cells]
    | succ i => simpa [WantedPairs.cells,Nat.mul_succ,List.getD,Nat.add_assoc] using ih i (by simpa using hi)

theorem pair_reads (ps : List (ℕ × ℕ)) (μ : ℕ → ℤ) (base : ℕ)
    (hseg : Seg μ base (WantedPairs.cells ps)) (i : ℕ) (hi : i<ps.length) :
    μ (base+2*i)=((ps.getD i (0,0)).1 : ℤ) ∧
      μ (base+2*i+1)=((ps.getD i (0,0)).2 : ℤ) := by
  have h0 : 2*i<(WantedPairs.cells ps).length := by rw [WantedPairs.cells_length]; omega
  have h1 : 2*i+1<(WantedPairs.cells ps).length := by rw [WantedPairs.cells_length]; omega
  constructor
  · exact (hseg _ h0).trans (by simpa only [List.getD_eq_getElem _ _ h0] using cells_left ps i)
  · have h := (hseg _ h1).trans (by simpa only [List.getD_eq_getElem _ _ h1] using cells_right ps i hi)
    simpa only [Nat.add_assoc] using h
end ThreeSum.TernarySourceHostRecords
