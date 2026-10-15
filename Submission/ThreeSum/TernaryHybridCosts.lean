import Submission.ThreeSum.TernaryHybridCore
import Submission.ThreeSum.TernaryEndBridge

/-!
# Running time of the generic concrete hybrid wrapper

A proved bound for the actual fast executable supplies the same bound with
arbitrarily small slack after the fixed power/caller overhead.  Both runtime
guards and all natural supplied magnitude bounds are retained.
-/

namespace ThreeSum.TernaryHybridCosts

open Light StageBounds Filter

noncomputable section

def fastTime (T : ℕ → ℕ) (κ n : ℕ) : ℕ :=
  T n + LightNatPower.time κ + 1000

theorem time_of_large {T : ℕ → ℕ} {κ cutoff n U : ℕ}
    (hn : cutoff ≤ n) (hU : U ≤ n^κ) :
    TernaryHybridCore.time T κ cutoff n U = fastTime T κ n := by
  simp only [TernaryHybridCore.time,fastTime,
    if_neg (not_or_intro (Nat.not_lt.mpr hn) (Nat.not_lt.mpr hU))]

theorem fastTime_powerBound {T : ℕ → ℕ} {a : ℝ}
    (hT : PowerBound T a) (ha : 0 ≤ a) (κ : ℕ) :
    PowerBound (fastTime T κ) a := by
  have hp := (PowerBound.const (LightNatPower.time κ)).mono_exponent ha
  have hc := (PowerBound.const 1000).mono_exponent ha
  exact (hT.add_same hp).add_same hc

/-- A single eventual size threshold bounds every admissible natural U. -/
theorem time_eventually_uniform {T : ℕ → ℕ} {a b : ℝ}
    (hT : PowerBound T a) (ha : 0 ≤ a) (hab : a < b) (κ cutoff : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ U : ℕ, U ≤ n^κ →
      (TernaryHybridCore.time T κ cutoff n U : ℝ) ≤ (n : ℝ)^b := by
  have ht := fastTime_powerBound hT ha κ (b-a) (sub_pos.mpr hab)
  filter_upwards [ht,eventually_ge_atTop cutoff] with n hn hcut
  intro U hU
  rw [time_of_large hcut hU]
  simpa only [add_sub_cancel] using hn

theorem timeUpTo_eventually {T : ℕ → ℕ} {a b : ℝ}
    (hT : PowerBound T a) (ha : 0 ≤ a) (hab : a < b) (κ cutoff : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      timeUpTo (TernaryHybridCore.time T κ cutoff) n ((n : ℝ)^(κ : ℝ)) ≤
        (n : ℝ)^b :=
  TernaryEndBridge.timeUpTo_eventually_of_uniform
    (time_eventually_uniform hT ha hab κ cutoff)

end
end ThreeSum.TernaryHybridCosts
