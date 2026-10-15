import Submission.ThreeSum.LightTernaryPrefixLoop

noncomputable section
namespace ThreeSum.LightTernaryPrefixLoop
open Light
set_option maxHeartbeats 5000000

/-- Concrete procedures appended after the existing seed controller. -/
def tail : Program :=
  LightTernaryPrefixSetup.allocatedProgram.map (ReportingHostRelocation.relocate 167)++
    LightTernaryInitialKeys.program.map (ReportingHostRelocation.relocate 173)++
    LightTernaryCommitKeys.program.map (ReportingHostRelocation.relocate 175)++
    LightTernaryCommitSpan.program.map (ReportingHostRelocation.relocate 177)++
    [LightTernaryRepeatWord.body,headerBody,stepBody,loopBody,initBody,LightTernaryBudgetStep.body,prepareBody]

theorem program_eq_controller_append (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ) :
    program p R S K raws words maps xl yl zl xr yr zr=
      LightTernarySeedController.program p R S K raws words maps xl yl zl xr yr zr++tail :=by
  simp only [program,priorProcs,tail,List.append_assoc]

@[simp] theorem tail_length : tail.length=18 :=by
  simp [tail,LightTernaryPrefixSetup.allocatedProgram,LightTernaryPrefixSetup.program,
    LightTernaryInitialKeys.program,LightTernaryCommitKeys.program,LightTernaryCommitSpan.program]

structure Library (P : Program) : Prop where
  prefixMain : P[167]?=some (LightTernaryPrefixSetup.body 168 169)
  power : P[168]?=some LightNatPower.body
  setup : P[169]?=some (LightTernaryEnumerationSetup.body 170 171)
  powers : P[170]?=some powTableBody
  enumeration : P[171]?=some (LightTernaryEnumeration.body 171)
  allocate : P[172]?=some (LightTernaryPrefixSetup.allocateBody 168 167)
  initialFill : P[173]?=some fillBody
  initialMain : P[174]?=some (ReportingHostRelocation.relocate 173 LightTernaryInitialKeys.body)
  commitCopy : P[175]?=some copyBody
  commitMain : P[176]?=some (ReportingHostRelocation.relocate 175 LightTernaryCommitKeys.body)
  spanCopy : P[177]?=some copyBody
  repeatWord : P[178]?=some LightTernaryRepeatWord.body
  header : P[179]?=some headerBody
  step : P[180]?=some stepBody
  loop : P[181]?=some loopBody
  initial : P[182]?=some initBody
  budget : P[183]?=some LightTernaryBudgetStep.body
  prepare : P[184]?=some prepareBody

theorem program_library (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ) : Library (program p R S K raws words maps xl yl zl xr yr zr) :=by
  rw [program_eq_controller_append]
  constructor <;>
    simp only [List.getElem?_append,LightTernarySeedController.program_length] <;>
    norm_num only <;>
    simp [tail,LightTernaryPrefixSetup.allocatedProgram,LightTernaryPrefixSetup.program,
      LightTernaryInitialKeys.program,LightTernaryCommitKeys.program,LightTernaryCommitSpan.program,
      LightTernaryPrefixSetup.body,LightTernaryPrefixSetup.allocateBody,
      LightTernaryEnumerationSetup.body,LightTernaryEnumeration.body,copyBody,fillBody,pass,LightNatPower.body,powTableBody,powTableRound]

end ThreeSum.LightTernaryPrefixLoop
