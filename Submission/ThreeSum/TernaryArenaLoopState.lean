import Submission.ThreeSum.TernaryArenaPhaseBudget
import Submission.ThreeSum.TernaryArenaPhaseFrames
import Submission.ThreeSum.LightTernaryPrefixInit

noncomputable section
namespace ThreeSum.TernaryArenaLoop
open Light TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps TernaryArenaLayout
open TernaryArenaSourceSetup TernaryArenaSeedCandidate TernaryArenaSeedData
open TernaryArenaSelectedBudgets TernaryArenaAllocation TernaryArenaPrefixInputs
open LightTernarySeedScoreFactory LightTernaryControllerFactory
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

structure Setup (p m F K N : ℕ) [Fact p.Prime]
    (E : Type*) [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E] where
  maps : Fin F→Weight m p
  threshold : ℕ
  cap : ℕ
  Q : TernaryGoodOutputCatalog.Output m
  M : ℕ
  radix : ℕ
  H : ℕ
  drift : ℕ
  scale : ℕ
  allocation : Allocation maps threshold cap M radix K H drift scale
  input : Input
  arrays : Inputs
  n : ℕ
  U : ℕ
  rounds : ℕ
  U0 : ℕ
  featureBound : ℕ
  tagBound : ℕ
  positionCap : ℕ
  valueTag : ℕ
  V : ℕ
  scoreBound : ℕ
  enumeration : (E×E)≃Fin N
  ell : E→ₗ[ZMod p] ZMod p
  L : ℕ→ℕ→ℤ
  R : ℕ→ℕ→ℤ
  O : ℕ→ℕ→ℤ
  catalogs : ℕ→ℕ→ℕ→ℕ
  initial : ℕ→ℤ

variable {p m F K N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

abbrev Setup.alpha (_S : Setup p m F K N E) : ℕ :=p^(2*K)
abbrev Setup.beta (_S : Setup p m F K N E) : ℕ :=9*TernaryArenaBudgetExistence.pairFactor m F K
abbrev Setup.budgetScale (_S : Setup p m F K N E) : ℕ :=2^(fixedPi m 2*K)
abbrev Setup.wordRadix (_S : Setup p m F K N E) : ℕ :=4^fixedLength m
abbrev Setup.raws (S : Setup p m F K N E) :=TernaryGoodOutputCatalog.raws S.maps S.threshold
abbrev Setup.words (S : Setup p m F K N E) :=TernaryGoodOutputCatalog.wordCodes S.maps S.threshold
abbrev Setup.mapCodes (S : Setup p m F K N E) :=TernaryGoodOutputCatalog.mapCodes S.maps S.threshold
abbrev Setup.newSpan (S : Setup p m F K N E) :=addr S.input.free S.input.capacity 8

def Setup.state (S : Setup p m F K N E) (j : ℕ) : State (p:=p) S.arrays :=
  run S.maps S.threshold S.cap S.valueTag S.V S.scoreBound S.Q S.input S.arrays S.featureBound K S.n S.U0
    S.enumeration S.ell S.L S.R S.O S.catalogs j

def Setup.family (S : Setup p m F K N E) (j : ℕ) (catalog : ℕ→ℕ→ℕ) :=
  TernaryArenaPhase.family S.maps S.threshold S.cap S.tagBound S.Q S.input S.arrays j S.featureBound
    S.ell (TernaryArenaFamilyBudget.seedAt S.enumeration) S.L S.R S.O (S.state j) catalog

def Setup.prefixInput (S : Setup p m F K N E) (j : ℕ) :=
  TernaryArenaPrefixPrepare.inputs p m F j S.arrays.J S.n S.U0 S.alpha S.beta S.budgetScale S.input S.Q

def Setup.seedHeader (S : Setup p m F K N E) (j : ℕ) :=
  LightTernaryPrefixFinish.header (config p j S.input S.arrays 0) N (p^j) (p^j) (S.alpha^j)
    (9^j*S.n^2) (9^j*S.n^2) (S.U0*(S.beta*S.budgetScale)^j) S.newSpan

def Setup.chosen (S : Setup p m F K N E) (j : ℕ) (catalog : ℕ→ℕ→ℕ) :=
  (S.family j catalog).pick K N (p^(j+1)) (p^(j+1)) (S.alpha^(j+1))
    (9^(j+1)*S.n^2) (9^(j+1)*S.n^2) (S.U0*(S.beta*S.budgetScale)^(j+1))-1

/-- Physical facts from the literal final phase, retained for the final
reporter's bank, header, wanted records and original endpoint semantics. -/
structure LastRecord (S : Setup p m F K N E) (j : ℕ) (ω : ℕ→ℤ) where
  before : ℕ→ℤ
  catalog : ℕ→ℕ→ℕ
  oldMemory : TernaryArenaPrefixState.Memory S.input S.arrays (fun i t=>S.L i t.val)
    (fun i t=>S.R i t.val) (fun i t=>S.O i t.val) j (S.state j) catalog S.initial before
  oldTemplate : Seg before (addr S.input.free S.input.capacity 0)
    (TernaryArenaHeaderAgreement.templateValues S.input p m F)
  preparedMemory : ℕ→ℤ
  prepared : LightTernaryPrefixStep.Prepared (S.prefixInput j) before preparedMemory
  finalMemory : ℕ→ℤ
  final : TernaryArenaControllerPlan.Final S.input (S.family j catalog) K S.wordRadix F
    (S.chosen j catalog) S.newSpan S.raws S.words S.mapCodes preparedMemory finalMemory
  committed : LightTernaryPrefixFinish.Committed (config p (j+1) S.input S.arrays 0)
    (p^(j+1)) S.newSpan finalMemory ω

def Invariant (S : Setup p m F K N E) (j : ℕ) (μ : ℕ→ℤ) : Prop :=
  ∃catalog,
    TernaryArenaPrefixState.Memory S.input S.arrays (fun i t=>S.L i t.val)
      (fun i t=>S.R i t.val) (fun i t=>S.O i t.val) j (S.state j) catalog S.initial μ ∧
    Seg μ (addr S.input.free S.input.capacity 3) (S.seedHeader j) ∧
    Seg μ (addr S.input.free S.input.capacity 0) (TernaryArenaHeaderAgreement.templateValues S.input p m F) ∧
    match j with
    | 0=>True
    | j+1=>Nonempty (LastRecord S j μ)

/-- The exact natural budget of a phase; physical catalog representations
have no effect on loop counts or kernel time bounds. -/
def Setup.timeAt (S : Setup p m F K N E) (j : ℕ) : ℕ :=
  LightTernaryPrefixStep.time (S.prefixInput j) (config p (j+1) S.input S.arrays 0) N
    (TernaryArenaControllerCore.seedTime (S.family j (fun _ _=>0)) K S.wordRadix F N S.raws S.words S.mapCodes)

def Setup.stepTime (S : Setup p m F K N E) : ℕ :=(Finset.range S.rounds).sup S.timeAt

def Setup.time (S : Setup p m F K N E) : ℕ :=LightTernaryPrefixLoop.time S.rounds S.stepTime


def Setup.program (S : Setup p m F K N E) : Program :=
  LightTernaryPrefixLoop.program p S.wordRadix F K S.raws S.words S.mapCodes
    ((TernaryNativeCompleteFrontend.localRecords S.maps S.cap false).map (TernaryCanonicalDictionaries.native false S.maps))
    ((TernaryNativeCompleteFrontend.localRecords S.maps S.cap false).map TernaryCanonicalDictionaries.wordCode)
    ((TernaryNativeCompleteFrontend.localRecords S.maps S.cap false).map TernaryCanonicalDictionaries.mapCode)
    ((TernaryNativeCompleteFrontend.localRecords S.maps S.cap true).map (TernaryCanonicalDictionaries.native true S.maps))
    ((TernaryNativeCompleteFrontend.localRecords S.maps S.cap true).map TernaryCanonicalDictionaries.wordCode)
    ((TernaryNativeCompleteFrontend.localRecords S.maps S.cap true).map TernaryCanonicalDictionaries.mapCode)

def Setup.argv (S : Setup p m F K N E) : List ℤ :=
  LightTernaryPrefixLoop.args S.rounds m F p (addr S.input.free S.input.capacity 3)
    (addr S.input.free S.input.capacity 0) (addr S.input.free S.input.capacity 1)
    (addr S.input.free S.input.capacity 13) (fixedAlpha m 2) (alphaRank m)
    (TernaryCodeSemantics.address S.Q.val) S.wordRadix S.arrays.J S.alpha S.beta S.budgetScale

def Setup.initArgs (S : Setup p m F K N E) : List ℤ:=S.argv++[(addr S.input.free S.input.capacity 2:ℤ)]
def Setup.initTime (S : Setup p m F K N E) : ℕ:=
  LightTernaryPrefixInit.time (config p 0 S.input S.arrays 0) S.rounds S.stepTime

end ThreeSum.TernaryArenaLoop
