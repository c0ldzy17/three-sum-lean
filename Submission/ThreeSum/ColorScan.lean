import Submission.ThreeSum.ColorParameters

/-! # Correctness of a prefix of the literal coloring family -/

namespace ThreeSum.ColorScan

open ColorParameters

def Hit {n : ℕ} (x : Fin n → ℤ) (W t : ℕ) : Prop :=
  ∃ i, ∃ hi : i < count W, i < t ∧ ColorClassLists.witness (parameter hi) x

theorem hit_zero {n W : ℕ} (x : Fin n → ℤ) : ¬ Hit x W 0 := by
  rintro ⟨i,hi,hlt,_⟩
  omega

theorem hit_mono {n W a b : ℕ} {x : Fin n → ℤ} (hab : a ≤ b) :
    Hit x W a → Hit x W b := by
  rintro ⟨i,hi,hlt,hx⟩
  exact ⟨i,hi,hlt.trans_le hab,hx⟩

theorem hit_succ {n W t : ℕ} (x : Fin n → ℤ) (ht : t < count W) :
    Hit x W (t+1) ↔ Hit x W t ∨ ColorClassLists.witness (parameter ht) x := by
  constructor
  · rintro ⟨i,hi,hlt,hx⟩
    by_cases he : i=t
    · subst i
      exact Or.inr hx
    · exact Or.inl ⟨i,hi,by omega,hx⟩
  · rintro (⟨i,hi,hlt,hx⟩ | hx)
    · exact ⟨i,hi,by omega,hx⟩
    · exact ⟨t,ht,by omega,hx⟩

theorem hit_complete {n W : ℕ} (x : Fin n → ℤ) (hn : n ≤ 2^W) :
    Hit x W (count W) ↔ Coloring.DistinctZeroSum x := by
  rw [ColorParameters.reduction_correct x hn]
  constructor
  · rintro ⟨i,hi,_,hx⟩
    exact ⟨i,hi,hx⟩
  · rintro ⟨i,hi,hx⟩
    exact ⟨i,hi,hi,hx⟩

end ThreeSum.ColorScan
