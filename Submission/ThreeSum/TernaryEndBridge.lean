import Submission.ThreeSumApsp.RunningTimes.Sec3.Theorem22.ThreeSumLayout
import Submission.ThreeSumApsp.RunningTimes.FromClaims.Bounds
import Submission.ThreeSumApsp.Statements.Exponents

/-!
# Exponent-independent transfer of a concrete 3SUM solver

This is only the existing compiler and end-statement transfer, generalized
over the natural running-time function and rational exponent.  Every premise
is an actual executable task contract, a polynomial resource proof, or a
bound on that executable's own running time.  The benchmark definition is
imported unchanged.
-/

namespace ThreeSum.TernaryEndBridge

open Light

noncomputable section

theorem realized_of_solves {P : Program} {p : ℕ}
    {T : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need}
    (hs : Solves s3Task P p T need) (hp : PolyNeed need) :
    ThreeSumApsp.WordRam.Realized EndStatement.ThreeSum (timeUpTo T) :=
  Light.Sec3.realized_threeSum _ (hs.solvedIn hp)

theorem solvedAt_of_solves {κ : ℕ} {P : Program} {p : ℕ}
    {T : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need} {a : ℝ}
    (hs : Solves s3Task P p T need) (hp : PolyNeed need)
    (ht : ∀ᶠ n : ℕ in Filter.atTop,
      timeUpTo T n ((n : ℝ) ^ (κ : ℝ)) ≤ (n : ℝ) ^ a) :
    ThreeSumApsp.WordRam.SolvedInTimeAt EndStatement.ThreeSum κ a 0 := by
  apply ThreeSumApsp.FromClaims.solvedAt_of_realized
    (timeUpTo T) κ (realized_of_solves hs hp) (C := 1)
  simpa only [pow_zero, mul_one, one_mul] using ht

/-- A uniform natural bound on the actual admissible magnitude parameters
also bounds the real finite supremum used by the existing compiler. -/
theorem timeUpTo_eventually_of_uniform {κ : ℕ} {T : ℕ → ℕ → ℕ} {a : ℝ}
    (ht : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ U : ℕ, U ≤ n ^ κ → (T n U : ℝ) ≤ (n : ℝ) ^ a) :
    ∀ᶠ n : ℕ in Filter.atTop,
      timeUpTo T n ((n : ℝ) ^ (κ : ℝ)) ≤ (n : ℝ) ^ a := by
  filter_upwards [ht] with n hn
  apply timeUpTo_le
  intro U hU
  have hnonneg : (0 : ℝ) ≤ (n : ℝ) ^ (κ : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hcast : (U : ℝ) ≤ (n : ℝ) ^ (κ : ℝ) :=
    hU.trans (max_le le_rfl hnonneg)
  rw [Real.rpow_natCast] at hcast
  have hnat : U ≤ n ^ κ := by exact_mod_cast hcast
  exact hn U hnat

/-- An executable solver for every fixed magnitude exponent, together with
its own proved running time, gives the exact rational benchmark statement. -/
theorem endStatement_of_solvers {r : ℚ} (hr : 0 ≤ r)
    (h : ∀ κ : ℕ,
      ∃ (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (need : ℕ → ℕ → Need),
        Solves s3Task P p T need ∧ PolyNeed need ∧
        ∀ᶠ n : ℕ in Filter.atTop,
          timeUpTo T n ((n : ℝ) ^ (κ : ℝ)) ≤ (n : ℝ) ^ (r : ℝ)) :
    EndStatement.ThreeSum.SolvedInTime r := by
  have hall : ThreeSumApsp.WordRam.SolvedInTime EndStatement.ThreeSum (r : ℝ) 0 := by
    intro κ
    obtain ⟨P, p, T, need, hs, hp, ht⟩ := h κ
    exact solvedAt_of_solves hs hp ht
  exact hall.endStatement rfl hr

theorem endStatement_of_uniform_solvers {r : ℚ} (hr : 0 ≤ r)
    (h : ∀ κ : ℕ,
      ∃ (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (need : ℕ → ℕ → Need),
        Solves s3Task P p T need ∧ PolyNeed need ∧
        ∀ᶠ n : ℕ in Filter.atTop,
          ∀ U : ℕ, U ≤ n ^ κ → (T n U : ℝ) ≤ (n : ℝ) ^ (r : ℝ)) :
    EndStatement.ThreeSum.SolvedInTime r := by
  apply endStatement_of_solvers hr
  intro κ
  obtain ⟨P, p, T, need, hs, hp, ht⟩ := h κ
  exact ⟨P, p, T, need, hs, hp, timeUpTo_eventually_of_uniform ht⟩

end
end ThreeSum.TernaryEndBridge
