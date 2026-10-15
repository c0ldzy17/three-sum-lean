import Submission.ThreeSum.LightTernarySignedRow

/-! Explicit physical offsets for original digit coordinates and both tags. -/
namespace ThreeSum.TernarySignedLayout
open TernarySignedReduction

def offset (J i : ℕ) : ℕ := if i<J then J-1-i else i
def feature {J : ℕ} (f : Coordinate J→ℤ) (i : ℕ) : ℤ :=
  if h : i<J then f (.inl ⟨i,h⟩) else if i=J then f (.inr false) else f (.inr true)

theorem offset_lt {J i : ℕ} (hi : i<J+2) : offset J i<J+2 := by
  unfold offset
  split_ifs <;> omega

theorem offset_involutive {J i : ℕ} (hi : i<J+2) : offset J (offset J i)=i := by
  by_cases h : i<J
  · have hr : J-1-i<J := by omega
    simp only [offset,if_pos h,if_pos hr]
    omega
  · simp only [offset,if_neg h]

theorem row_logical_read {μ : ℕ→ℤ} {dst J : ℕ} {f : Coordinate J→ℤ}
    (hrow : LightTernarySignedRow.Row μ dst J f) {i : ℕ} (hi : i<J+2) :
    μ (dst+offset J i)=feature f i := by
  by_cases hd : i<J
  · have he : dst+(J-1-i)=dst+J-1-i := by omega
    simp only [offset,if_pos hd,feature,dif_pos hd,he]
    exact hrow.1 ⟨i,hd⟩
  · by_cases hz : i=J
    · subst i
      simpa [offset,feature] using hrow.2.1
    · have he : i=J+1 := by omega
      subst i
      simpa [offset,feature,Nat.add_assoc] using hrow.2.2

theorem row_physical_read {μ : ℕ→ℤ} {dst J : ℕ} {f : Coordinate J→ℤ}
    (hrow : LightTernarySignedRow.Row μ dst J f) {i : ℕ} (hi : i<J+2) :
    μ (dst+i)=feature f (offset J i) := by
  have h := row_logical_read hrow (offset_lt hi)
  rwa [offset_involutive hi] at h

theorem feature_abs {J U : ℕ} {f : Coordinate J→ℤ}
    (hf : ∀ k, |f k|≤(U : ℤ)) (i : ℕ) : |feature f i|≤(U : ℤ) := by
  unfold feature
  split_ifs <;> exact hf _

end ThreeSum.TernarySignedLayout
