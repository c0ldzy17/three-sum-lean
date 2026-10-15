import Submission.ThreeSum.LightTernaryMomentReporter

/-! The literal reporting program adds only a fixed-degree multiplicative
constant to the actual source/count host and its physical input/output sizes. -/
noncomputable section
namespace ThreeSum.TernaryMomentReporterBudget
open Light TernaryMomentSchedule TernaryWeightChannels

def circuitCost (c : ℕ×ℕ) : ℕ :=
  ((leftMoment c.1 c.2).compile LightTernaryScalarChannel.atoms).cost+
  ((rightMoment c.1 c.2).compile LightTernaryScalarChannel.atoms).cost+1000

def weightBudget (terms : ℕ) : ℕ :=
  (channels terms).foldr (fun c n => max (circuitCost c) n) 1000

theorem fold_floor (xs : List (ℕ×ℕ)) :
    1000≤xs.foldr (fun c n => max (circuitCost c) n) 1000 := by
  induction xs with
  | nil => rfl
  | cons c cs ih => exact ih.trans (Nat.le_max_right _ _)

theorem fold_member (xs : List (ℕ×ℕ)) (c : ℕ×ℕ) (hc : c∈xs) :
    circuitCost c≤xs.foldr (fun c n => max (circuitCost c) n) 1000 := by
  induction xs with
  | nil => simp at hc
  | cons e es ih =>
    rcases List.mem_cons.mp hc with rfl|hc
    · exact Nat.le_max_left _ _
    · exact (ih hc).trans (Nat.le_max_right _ _)

def base {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) : ℕ :=
  S.left.NL+S.right.NL+S.front.count+S.runtime+1

theorem cost_bound {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (terms : ℕ) (c : ℕ×ℕ) (hc : c∈channels terms) :
    LightTernaryCertifiedMomentDriver.cost S c≤weightBudget terms*base S := by
  have hC : 1000≤weightBudget terms := fold_floor _
  have hcC : circuitCost c≤weightBudget terms := fold_member _ c hc
  have hL : ((leftMoment c.1 c.2).compile LightTernaryScalarChannel.atoms).cost+12≤weightBudget terms := by
    unfold circuitCost at hcC
    omega
  have hR : ((rightMoment c.1 c.2).compile LightTernaryScalarChannel.atoms).cost+12≤weightBudget terms := by
    unfold circuitCost at hcC
    omega
  have hl := Nat.mul_le_mul_left S.left.NL hL
  have hr := Nat.mul_le_mul_left S.right.NL hR
  have hq := Nat.mul_le_mul_right S.front.count (show 24≤weightBudget terms by omega)
  have ht := Nat.mul_le_mul_right S.runtime (show 1≤weightBudget terms by omega)
  unfold LightTernaryCertifiedMomentDriver.cost LightTernaryMomentChannelStep.time
    LightTernaryScalarChannel.time LightTernaryMomentAccumulate.time base
  nlinarith only [hl,hr,hq,ht,hC]

def driverConstant (terms : ℕ) : ℕ :=
  terms^2*(weightBudget terms+117)+13*terms+106

theorem driver_time_bound {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (terms : ℕ) :
    LightTernaryCertifiedMomentDriver.time S terms≤driverConstant terms*base S := by
  let steps := channels terms
  have hB : 1≤base S := by unfold base; omega
  have hcount : S.front.count≤base S := by unfold base; omega
  have hc : ∀ c∈LightTernaryMomentDriver.labels steps,
      LightTernaryCertifiedMomentDriver.cost S (steps.getD c.1 (0,0))≤weightBudget terms*base S := by
    intro c hc
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hc
    have hi' : i<steps.length := List.mem_range.mp hi
    apply cost_bound S terms
    rw [List.getD_eq_getElem _ _ hi']
    exact List.getElem_mem hi'
  have ht := LightTernaryFixedChannelLoop.time_le_length
    (LightTernaryMomentDriver.labels steps) 115 (weightBudget terms*base S)
    (fun c => LightTernaryCertifiedMomentDriver.cost S (steps.getD c.1 (0,0))) hc
  simp only [LightTernaryMomentDriver.labels,List.length_map,List.length_range] at ht
  have hn := length_le terms
  have ha : 117+weightBudget terms*base S≤(weightBudget terms+117)*base S := by nlinarith
  have hmul := Nat.mul_le_mul_left steps.length ha
  have hnum := Nat.mul_le_mul_right ((weightBudget terms+117)*base S) hn
  have hrow := Nat.mul_le_mul_left (13*terms) hcount
  have hconst := Nat.mul_le_mul_left 106 hB
  unfold LightTernaryCertifiedMomentDriver.time LightTernaryMomentDriver.time
  rw [LightTernaryMomentChannelFactory.backend_length]
  simp only [Nat.reduceAdd,fillTime]
  unfold driverConstant LightTernaryMomentDriver.labels
  dsimp only [steps] at ht hmul
  nlinarith only [ht,hmul,hnum,hrow,hconst]

def reporterConstant (H : ℕ) : ℕ :=
  driverConstant (2*H+1)+LightTernaryMomentRow.time H+500

theorem reporter_time_bound {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (H : ℕ) :
    LightTernaryMomentReporter.time S H≤reporterConstant H*base S := by
  have hd := driver_time_bound S (2*H+1)
  have hB : 1≤base S := by unfold base; omega
  have hcount : S.front.count≤base S := by unfold base; omega
  have hrow := Nat.mul_le_mul_right (LightTernaryMomentRow.time H+200) hcount
  have hconst := Nat.mul_le_mul_left 500 hB
  unfold LightTernaryMomentReporter.time LightTernaryMomentBatch.time reporterConstant
  nlinarith only [hd,hrow,hconst]

end ThreeSum.TernaryMomentReporterBudget
