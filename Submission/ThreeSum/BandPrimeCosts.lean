import Submission.ThreeSum.LightBandPrimeSetup
import Submission.ThreeSum.BandPrimeScales

/-!
# Charge the executed common-prime setup

The bound includes the generated pool, every aggregate candidate minimum,
all original band-score calls, and the computed chain depth. The size-only
budget uses the same quadratic owner bound as the physical mass theorem.
-/

namespace ThreeSum.BandPrimeCosts

open Scales BandScales CostLedger ArithmeticStageBounds

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

def unit (p g U : ℕ) : ℕ :=
  LightModuloCounts.time p g g g U+LightWeightedScore.jointTime p+1000

theorem unit_ge (p g U : ℕ) : 1000 ≤ unit p g U := by unfold unit; omega

theorem cell_time_le (p g s U : ℕ) :
    LightBandWeightedScoreCell.time p g s U ≤ (s+1)*unit p g U := by
  unfold LightBandWeightedScoreCell.time LightBandWeightedScoreSlice.time
    LightWeightedScore.runtimeTime LightWeightedScore.time unit
  nlinarith

theorem aggregate_time_le (p g R s U : ℕ) :
    LightBandWeightedScore.time p g R s U ≤ 2*(R+1)*(s+1)*unit p g U := by
  have hc := Nat.mul_le_mul_left R (Nat.add_le_add_right (cell_time_le p g s U) 100)
  have hv : 1000 ≤ (s+1)*unit p g U :=
    (unit_ge p g U).trans (Nat.le_mul_of_pos_left _ (by omega))
  calc
    _ ≤ R*((s+1)*unit p g U+100)+50 := Nat.add_le_add_right hc 50
    _ ≤ R*(2*((s+1)*unit p g U))+(s+1)*unit p g U := by
      apply Nat.add_le_add
      · apply Nat.mul_le_mul_left; omega
      · omega
    _ ≤ 2*(R+1)*((s+1)*unit p g U) := by nlinarith
    _ = _ := by ring

theorem minimum_time_le (p g R s U : ℕ) :
    LightBandPrimeMinimum.time p g R s U ≤ 3*(R+1)*(s+1)^2*unit p g U := by
  have hv : 1000 ≤ (R+1)*(s+1)*unit p g U :=
    (unit_ge p g U).trans (Nat.le_mul_of_pos_left _ (by positivity))
  have hh := aggregate_time_le p g R s U
  calc
    _ = (s+1)*(LightBandWeightedScore.time p g R s U+140) := by
      unfold LightBandPrimeMinimum.time; ring
    _ ≤ (s+1)*(3*((R+1)*(s+1)*unit p g U)) := by
      apply Nat.mul_le_mul_left
      nlinarith
    _ = _ := by ring

def core (p g R s U : ℕ) : ℕ := (R+1)*(s+1)^2*unit p g U

theorem core_ge (p g R s U : ℕ) : 1000 ≤ core p g R s U := by
  have hp : 0 < (R+1)*(s+1)^2 := by positivity
  exact (unit_ge p g U).trans (Nat.le_mul_of_pos_left _ hp)

theorem chain_time_le (p g R s U levels : ℕ) :
    LightBandPrimeChain.time p g R s U levels ≤ 4*(levels+1)*core p g R s U := by
  have hm : LightBandPrimeMinimum.time p g R s U ≤ 3*core p g R s U := by
    simpa only [core,Nat.mul_assoc] using minimum_time_le p g R s U
  have hh := Nat.mul_le_mul_left levels (Nat.add_le_add_right hm 140)
  have hc := core_ge p g R s U
  unfold LightBandPrimeChain.time
  nlinarith

theorem setup_time_le (p g R M y U : ℕ) :
    LightBandPrimeSetup.time p g R M y U ≤ LightPrimePool.time y+
      5*(LightBandPrimeDepth.depth M y+1)*(R+1)*(LightPrimePool.size y+1)^2*unit p g U := by
  have hc := chain_time_le p g R (LightPrimePool.size y) U (LightBandPrimeDepth.depth M y)
  have hg := core_ge p g R (LightPrimePool.size y) U
  have hh : LightBandPrimeDepth.time M y+
      LightBandPrimeChain.time p g R (LightPrimePool.size y) U (LightBandPrimeDepth.depth M y)+240 ≤
      5*(LightBandPrimeDepth.depth M y+1)*core p g R (LightPrimePool.size y) U := by
    unfold LightBandPrimeDepth.time
    nlinarith
  unfold LightBandPrimeSetup.time LightBandPrimeConstruction.time
  simp only [core,Nat.mul_assoc] at hh ⊢
  omega

theorem pool_time_le (y : ℕ) : LightPrimePool.time y ≤ 100000*(y+1)^3 := by
  have hl : Nat.log 2 (4*y+1) ≤ 4*y+1 := Nat.log_le_self _ _
  have hn : 4*y-2 ≤ 4*y := Nat.sub_le _ _
  have ht := Nat.mul_le_mul hn
    (show LightResidues.residueBudget (4*y)+70 ≤ 43*(4*y+2)+104 by
      unfold LightResidues.residueBudget; omega)
  have hp := Nat.mul_le_mul_left (3*y) (Nat.add_le_add_right ht 170)
  calc
    _ ≤ 3*y*(4*y*(43*(4*y+2)+104)+170)+100 := by
      unfold LightPrimePool.time LightPrimality.time
      simpa only [Nat.add_assoc,show 70+100=170 by decide] using Nat.add_le_add_right hp 100
    _ ≤ _ := by nlinarith [Nat.zero_le (y^3)]

theorem unit_le_budget {n : ℕ} (k : ℕ) (hn : 0 < n) :
    unit (maxMod n) (bandSize n) (n^k) ≤ 3*perTripleBudget k n := by
  have hc := invocation_le_budget (p := maxMod n) k hn le_rfl le_rfl le_rfl le_rfl
  have hp := (KaratsubaInterface.le_capacity (maxMod n)).trans (ModuloCosts.capacity_le_roundedPower (maxMod n))
  have hl : Nat.log 2 (maxMod n+1) ≤ maxMod n+1 := Nat.log_le_self _ _
  have hj : LightWeightedScore.jointTime (maxMod n) ≤ perTripleBudget k n := by
    unfold LightWeightedScore.jointTime LightResidues.residueBudget perTripleBudget
    omega
  have hlarge : 1000 ≤ perTripleBudget k n := by unfold perTripleBudget; omega
  unfold unit
  omega

def timeBudget (k n : ℕ) : ℕ := LightPrimePool.time (primeWindow n)+
  15*(primeDepth radix n+1)*(3*bandCount n^2+1)*
    (LightPrimePool.size (primeWindow n)+1)^2*perTripleBudget k n

theorem setup_time_le_budget {n R : ℕ} (k : ℕ) (hn : 0 < n)
    (hR : R ≤ 3*bandCount n^2) :
    LightBandPrimeSetup.time (maxMod n) (bandSize n) R (radix n) (primeWindow n) (n^k) ≤
      timeBudget k n := by
  have ht := setup_time_le (maxMod n) (bandSize n) R (radix n) (primeWindow n) (n^k)
  rw [LightBandPrimeDepth.depth_eq_primeDepth] at ht
  refine ht.trans ?_
  unfold timeBudget
  apply Nat.add_le_add_left
  calc
    _ ≤ 5*(primeDepth radix n+1)*(3*bandCount n^2+1)*
        (LightPrimePool.size (primeWindow n)+1)^2*(3*perTripleBudget k n) := by
      gcongr
      exact unit_le_budget k hn
    _ = _ := by ring

end ThreeSum.BandPrimeCosts
