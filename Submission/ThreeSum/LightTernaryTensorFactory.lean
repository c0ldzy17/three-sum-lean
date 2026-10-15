import Submission.ThreeSum.LightTernaryTensorDriverProof
import Submission.ThreeSum.LightTernaryPairedPotentialBatchFinal
import Submission.ThreeSum.TernarySourceCountWeightSeed

noncomputable section
namespace ThreeSum.LightTernaryTensorFactory
open Light TernaryJointType

abbrev program {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (K : ℕ) : Program :=
  LightTernaryTensorDriver.program S.left.xs S.left.ys S.left.zs S.right.xs S.right.ys S.right.zs K

def leftWeights (J q : ℕ) (L : ℕ→ℕ→ℤ) (i : ℕ) : ℤ :=
  L i (LightTernaryTensorDriver.digit J q 0)*L i (LightTernaryTensorDriver.digit J q 1)
def rightWeights (J q : ℕ) (R : ℕ→ℕ→ℤ) (i : ℕ) : ℤ :=
  R i (LightTernaryTensorDriver.digit J q 2)*R i (LightTernaryTensorDriver.digit J q 3)

def score {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (J : ℕ) (L R : ℕ→ℕ→ℤ) (wanted q : ℕ) : ℤ :=
  TernaryConvolution.factorial (S.front.Q wanted)*
    TernaryWeightedPhysicalSources.pairWeight
      (TernarySourceHostModel.channel S.left.records S.left.group (S.front.group wanted))
      (TernarySourceHostModel.channel S.right.records S.right.group (S.front.group wanted))
      (fun pair => S.front.E.word (S.left.key pair.2))
      (fun pair => S.front.E.word (S.right.key pair.2))
      (fun pair => leftWeights J q L pair.1) (fun pair => rightWeights J q R pair.1) (S.front.Q wanted)

def extras (K : ℕ) : Program :=
  LightTernaryTaggedChannel.program.map (ReportingHostRelocation.relocate 123)++
  LightWeightRow.program.map (ReportingHostRelocation.relocate 126)++
  (LightTernaryPairedPotential.program K).map (ReportingHostRelocation.relocate 129)++
  [LightTernaryPairedPotentialBatch.body 129,LightTernaryTensorScatter.body,
    LightTernaryQuarticStep.body 123 122 136,LightTernaryTensorDriver.body 130 126 137 135]

theorem program_split {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (K : ℕ) :
    program S K=S.program++extras K := by
  simp only [program,LightTernaryTensorDriver.program,LightTernaryTensorDriver.potentialLibraries,
    LightTernaryTensorDriver.quadLibraries,LightTernaryTensorDriver.channelLibraries,
    ReportingHostRelocation.program,TernarySourceCountExecutionFactory.Setup.program,
    LightTernarySourceCountHost.program_length,LightTernaryTensorDriver.channelLibraries_length,
    LightTernaryTensorDriver.quadLibraries_length,List.length_append,List.length_map,
    LightTernaryTaggedChannel.program,LightWeightRow.program,List.length_cons,List.length_nil,
    Nat.reduceAdd,extras,List.append_assoc]

structure Procs {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (K : ℕ) : Prop where
  main : (program S K)[138]?=some (LightTernaryTensorDriver.body 130 126 137 135)
  powers : (program S K)[130]?=some powTableBody
  row : (program S K)[126]?=some (LightWeightRow.body 127)
  digit : (program S K)[127]?=some (LightRadixDigit.body 128)
  divide : (program S K)[128]?=some LightSmallDivide.body
  channel : (program S K)[123]?=some (LightTernaryTaggedChannel.body 124 125)
  offset : (program S K)[124]?=some LightTernaryTaggedChannel.offsetBody
  product : (program S K)[125]?=some LightTernaryProductChannel.body
  scatter : (program S K)[136]?=some LightTernaryTensorScatter.body
  step : (program S K)[137]?=some (LightTernaryQuarticStep.body 123 122 136)
  batch : (program S K)[135]?=some (LightTernaryPairedPotentialBatch.body 129)
  potential : (program S K)[129]?=some (LightTernaryPairedPotential.body K 130 131 134)
  potentialRow : (program S K)[131]?=some (LightWeightRow.body 132)
  potentialDigit : (program S K)[132]?=some (LightRadixDigit.body 133)
  potentialDivide : (program S K)[133]?=some LightSmallDivide.body
  polynomial : (program S K)[134]?=some (LightTernaryPairedPolynomial.body K)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 5000000 in
theorem procs {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (K : ℕ) : Procs S K := by
  constructor <;> rw [program_split,
    List.getElem?_append_right (by simp [TernarySourceCountExecutionFactory.Setup.program]),
    show S.program.length=123 by simp [TernarySourceCountExecutionFactory.Setup.program]] <;> rfl

end ThreeSum.LightTernaryTensorFactory
