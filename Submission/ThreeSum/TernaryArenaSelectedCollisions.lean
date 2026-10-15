import Submission.ThreeSum.TernaryArenaFixedParameters

noncomputable section
namespace ThreeSum.TernaryArenaSelectedCollisions
open TernaryCoverScale TernaryOversizePrime TernaryPairedCollisionRate
open TernaryArenaSourceSetup TernaryArenaSeedCandidate TernaryArenaSelectedBudgets
open TernaryArenaSelectedSigned TernaryCoverGoodMaps
set_option maxHeartbeats 3000000

/-- The paid collision cleanup exponent includes the actual selector's
factor nine, and holds for every ordered collision budget. -/
theorem bounded {K m n value : ℕ} (hm : 0<m) (hn : 1<n)
    (hp : 9<nativePrime K m) (hrate : charge K m<(7483/10000 : ℝ))
    (hbudget : (nativePrime K m)^(radixLength m n)*value≤9^(radixLength m n)*n^2) :
    (value : ℝ)≤(n : ℝ)^(7483/10000 : ℝ) := by
  exact (TernaryPairedBudgetCollision.collision_bound hm hn hp hbudget).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn.le) hrate.le)

/-- The collision budgets of the selected original row state are exactly
the two actual packed-key scores consumed by cleanup. -/
theorem selected {K m n F : ℕ} (maps : Fin F→Weight m (nativePrime K m)) (τ cap : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (nA U radix U0 : ℕ)
    (s : State (p := nativePrime K m) A) (X B C : ℕ→ℤ)
    (hm : 0<m) (hn : 1<n) (hp : 9<nativePrime K m) (hrate : charge K m<(7483/10000 : ℝ))
    (hbudget : Budget maps τ cap Q (base I A.J nA) A K n U0
      (left U radix A.J B) (right U radix A.J C) (requester U radix A.J X) (radixLength m n) s) :
    let H := selectedHash A s (radixLength m n)
    ((TernaryOriginalCollisions.collisionPairs (fun i : Fin I.nB =>
      TernaryExtensionEncoding.coefficientCode (TernaryNativeRequesterCoverage.sourceLeft H U radix (B i.val)))).card : ℝ)≤
      (n : ℝ)^(7483/10000 : ℝ) ∧
    ((TernaryOriginalCollisions.collisionPairs (fun i : Fin I.nC =>
      TernaryExtensionEncoding.coefficientCode (TernaryNativeRequesterCoverage.sourceRight H U radix (C i.val)))).card : ℝ)≤
      (n : ℝ)^(7483/10000 : ℝ) := by
  dsimp only
  rw [left_key_collisions,right_key_collisions]
  exact ⟨bounded hm hn hp hrate hbudget.left,bounded hm hn hp hrate hbudget.right⟩

end ThreeSum.TernaryArenaSelectedCollisions
