import Submission.ThreeSum.TernaryArenaLayout
import Submission.ThreeSumApsp.Lang.Tasks

/-! A proved polynomial need is realized by one fixed arena capacity with
runtime capacity base n+U, including repeated original inputs. -/
namespace ThreeSum.TernaryArenaCapacity
open Light TernaryArenaLayout

theorem polyBound_le_capacity (s k n U : ℕ) :
    polyBound s k [n,U]≤capacity (2^s) (2*k) (n+U) := by
  have hmul := Nat.mul_le_mul (show n+1≤n+U+1 by omega)
    (show U+1≤n+U+1 by omega)
  calc
    _=2^s*((n+1)*(U+1))^k := by simp [polyBound]
    _≤2^s*((n+U+1)*(n+U+1))^k :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmul k)
    _=2^s*(n+U+1)^(2*k) := by rw [← pow_two,← pow_mul]
    _≤_ := by unfold capacity; gcongr; omega

theorem exists_capacity {need : ℕ→ℕ→Need} (h : PolyNeed need) :
    ∃ D E : ℕ, ∀ n U,
      (need n U).word≤capacity D E (n+U) ∧
      (need n U).cells≤capacity D E (n+U) ∧
      (need n U).depth≤capacity D E (n+U) := by
  obtain ⟨s,k,h⟩ := h
  refine ⟨2^s,2*k,?_⟩
  intro n U
  have hb := polyBound_le_capacity s k n U
  exact ⟨(h n U).1.trans hb,(h n U).2.1.trans hb,(h n U).2.2.trans hb⟩

end ThreeSum.TernaryArenaCapacity
