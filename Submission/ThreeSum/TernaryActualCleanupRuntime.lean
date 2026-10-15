import Submission.ThreeSum.LightTernaryPreparedPostSelection
import Submission.ThreeSum.TernaryCountFrontendBudget

noncomputable section
namespace ThreeSum.TernaryActualCleanupRuntime
open Light TernaryLocalParameters
set_option maxHeartbeats 6000000

def collisions (keys : ℕ→ℕ) (n : ℕ) : ℕ :=
  (TernaryOriginalCollisions.collisionPairs (fun i : Fin n=>keys i.val)).card

theorem stage_bound (keys : ℕ→ℕ) (size scan L n : ℕ) (hs : size≤n) (hscan : scan≤n) :
    LightOriginalSurvivorStage.time keys size scan L≤
      280*n+720+collisions keys size*(n*(120*L+330)+300) := by
  have hbad:=LightOriginalCollisionCleanup.bad_length_le_collisions keys size
  have hsurv:=(LightOriginalSurvivors.length_le keys size).trans hs
  have hcost : scan*(120*L+330)+300≤n*(120*L+330)+300 :=
    Nat.add_le_add_right (Nat.mul_le_mul_right _ hscan) _
  have hm:=Nat.mul_le_mul hbad hcost
  unfold LightOriginalSurvivorStage.time LightOriginalCollisionCleanup.time
    LightOriginalBucketFilter.time LightDeletedTwoSum.time LightColoredTwoSum.time
    LightBandLookup.time LightBandLookup.searchTime LightReportingGather.time
  change _≤280*n+720+collisions keys size*(n*(120*L+330)+300)
  change (LightOriginalCollisionCleanup.badIndices keys size).length*
    (scan*(120*L+330)+300)≤collisions keys size*(n*(120*L+330)+300) at hm
  nlinarith only [hm,hs,hsurv]

/-- Literal post-selection preparation, both exact collision cleanup passes,
and both compactions. The reporter's actual cost remains an explicit term. -/
theorem prepared_nat {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (H : ℕ)
    (c : LightOriginalSurvivorPair.Layout) (keysB keysC : ℕ→ℕ) (n : ℕ)
    (hA : c.nA≤n) (hB : c.nB≤n) (hC : c.nC≤n) :
    LightTernaryPreparedPostSelection.time S H c keysB keysC+673≤
      LightTernaryMomentReporter.time S H+
        10000*(c.L+1)*(n+c.q+1+(collisions keysB c.nB+collisions keysC c.nC)*(n+1)) := by
  have hsb:=stage_bound keysB c.nB c.nA c.L n hB hA
  have hsc:=stage_bound keysC c.nC c.nA c.L n hC hA
  have hbase : 708*n+26*c.q+17*c.L+3972≤5000*(c.L+1)*(n+c.q+1) := by
    nlinarith [Nat.zero_le (c.L*n),Nat.zero_le (c.L*c.q)]
  have hinner : n*(120*c.L+330)+300≤1000*(c.L+1)*(n+1) := by
    nlinarith [Nat.zero_le (c.L*n)]
  have hbad:=Nat.mul_le_mul_left (collisions keysB c.nB+collisions keysC c.nC) hinner
  have hall : LightTernaryPreparedPostSelection.time S H c keysB keysC+673≤
      LightTernaryMomentReporter.time S H+708*n+26*c.q+17*c.L+3972+
        (collisions keysB c.nB+collisions keysC c.nC)*(n*(120*c.L+330)+300) := by
    unfold LightTernaryPreparedPostSelection.time LightTernaryFinalPreparation.time
      LightTernaryPostSelection.time LightOriginalSurvivorPair.time LightTernaryCompactReporter.time
    rw [LightOriginalCollisionScore.time_eq,LightOriginalCollisionScore.time_eq]
    unfold powTableTime
    nlinarith only [hsb,hsc,hB,hC]
  apply hall.trans
  have hrem :
      5000*(c.L+1)*(n+c.q+1)+
        (collisions keysB c.nB+collisions keysC c.nC)*(1000*(c.L+1)*(n+1))≤
      10000*(c.L+1)*(n+c.q+1+(collisions keysB c.nB+collisions keysC c.nC)*(n+1)) := by
    nlinarith [Nat.zero_le ((c.L+1)*(n+c.q+1)),
      Nat.zero_le ((c.L+1)*(collisions keysB c.nB+collisions keysC c.nC)*(n+1))]
  nlinarith only [hbase,hbad,hrem]

/-- The real executed cleanup and preparation fit below the frontend
exponent, using both actual original collision-cardinality bounds. -/
theorem prepared_post_bound {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (H : ℕ)
    (c : LightOriginalSurvivorPair.Layout) (keysB keysC : ℕ→ℕ) (m J n : ℕ) (V : ℝ)
    (hn : 1<n) (hV : 0≤V)
    (hA : c.nA≤n) (hB : c.nB≤n) (hC : c.nC≤n)
    (hq : (c.q : ℝ)≤V*(n : ℝ)^TernaryCountFrontendBudget.frontendExponent)
    (hL : c.L≤2*fixedLength m*J)
    (hcolB : (collisions keysB c.nB : ℝ)≤(n : ℝ)^(7483/10000 : ℝ))
    (hcolC : (collisions keysC c.nC : ℝ)≤(n : ℝ)^(7483/10000 : ℝ)) :
    (LightTernaryPreparedPostSelection.time S H c keysB keysC+673 : ℕ)≤
      (LightTernaryMomentReporter.time S H : ℝ)+
        (1000000*(fixedLength m+1) : ℕ)*(J+1:ℕ)*(V+1)*
          (n : ℝ)^TernaryCountFrontendBudget.frontendExponent := by
  have hnR : (1 : ℝ)≤n := by exact_mod_cast hn.le
  have hn0 : (0 : ℝ)<n := by positivity
  let P:=(n : ℝ)^TernaryCountFrontendBudget.frontendExponent
  let R:=(n : ℝ)^(7483/10000 : ℝ)
  have hP : (n : ℝ)≤P := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hnR
      (show (1 : ℝ)≤TernaryCountFrontendBudget.frontendExponent by norm_num [TernaryCountFrontendBudget.frontendExponent])
  have hP1 : 1≤P := hnR.trans hP
  have hR0 : 0≤R := by positivity
  have hprod : (n : ℝ)*R≤P := by
    calc
      _=(n : ℝ)^(1+(7483/10000 : ℝ)) := by rw [Real.rpow_add hn0,Real.rpow_one]
      _≤_ := Real.rpow_le_rpow_of_exponent_le hnR (by norm_num [TernaryCountFrontendBudget.frontendExponent])
  have hcol : (collisions keysB c.nB+collisions keysC c.nC : ℕ)*(n+1:ℕ)≤4*P := by
    have hc : (collisions keysB c.nB+collisions keysC c.nC : ℕ)≤2*R := by
      push_cast
      dsimp only [R] at *
      linarith
    have hh := mul_le_mul hc (show ((n+1:ℕ):ℝ)≤2*n by push_cast;linarith) (by positivity) (by positivity)
    nlinarith only [hh,hprod]
  have hsize : (n+c.q+1+(collisions keysB c.nB+collisions keysC c.nC)*(n+1) : ℕ)≤6*(V+1)*P := by
    push_cast
    push_cast at hcol
    have hVP : 0≤V*P := mul_nonneg hV (by positivity)
    nlinarith only [hP,hP1,hq,hcol,hVP]
  have hL' : ((c.L+1 : ℕ):ℝ)≤((2*fixedLength m+1 : ℕ):ℝ)*(J+1 : ℕ) := by
    exact_mod_cast (show c.L+1≤(2*fixedLength m+1)*(J+1) by nlinarith)
  have hraw : (LightTernaryPreparedPostSelection.time S H c keysB keysC+673 : ℕ)≤
      (LightTernaryMomentReporter.time S H : ℝ)+
        10000*(c.L+1:ℕ)*(n+c.q+1+(collisions keysB c.nB+collisions keysC c.nC)*(n+1):ℕ) := by
    exact_mod_cast prepared_nat S H c keysB keysC n hA hB hC
  have hh:=mul_le_mul hL' hsize (by positivity) (by positivity)
  have hcoef : (10000 : ℝ)*(2*fixedLength m+1)*6≤1000000*(fixedLength m+1) := by
    have hlen : (0 : ℝ)≤(fixedLength m : ℝ) := by positivity
    nlinarith only [hlen]
  have hpos : 0≤((J+1:ℕ):ℝ)*(V+1)*P := by positivity
  have hfinal:=mul_le_mul_of_nonneg_right hcoef hpos
  dsimp only [P] at *
  push_cast at hraw hfinal hh ⊢
  nlinarith only [hraw,hh,hfinal]

end ThreeSum.TernaryActualCleanupRuntime
