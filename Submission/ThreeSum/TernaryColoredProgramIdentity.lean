import Submission.ThreeSum.TernaryColoredLoopSetup
import Submission.ThreeSum.TernaryColoredPrefixCall

noncomputable section
namespace ThreeSum.TernaryColoredProgramIdentity
open Light TernaryConcreteProfile TernaryArenaSourceSetup
variable {κ : ℕ}

def libraries (P : Profile κ) : Program :=
  LightTernaryColoredSolver.libraries P.radix P.allocation.D P.allocation.E P.K P.radix
    (P.p^(2*P.K)) P.drift P.scale P.p (4^TernaryLocalParameters.fixedLength P.m) P.F
    (TernaryGoodOutputCatalog.raws P.maps P.threshold) (TernaryGoodOutputCatalog.wordCodes P.maps P.threshold)
    (TernaryGoodOutputCatalog.mapCodes P.maps P.threshold)
    ((TernaryExecutable.leftRecords P.maps P.cap).map (TernaryCanonicalDictionaries.native false P.maps))
    ((TernaryExecutable.leftRecords P.maps P.cap).map TernaryCanonicalDictionaries.wordCode)
    ((TernaryExecutable.leftRecords P.maps P.cap).map TernaryCanonicalDictionaries.mapCode)
    ((TernaryExecutable.rightRecords P.maps P.cap).map (TernaryCanonicalDictionaries.native true P.maps))
    ((TernaryExecutable.rightRecords P.maps P.cap).map TernaryCanonicalDictionaries.wordCode)
    ((TernaryExecutable.rightRecords P.maps P.cap).map TernaryCanonicalDictionaries.mapCode)

def driver (P : Profile κ) : Stmt :=
  LightTernaryColoredSolver.body (240+TernaryExecutable.reportingMain (p:=P.p) P.K)
    P.m P.F P.p (TernaryLocalParameters.fixedAlpha P.m 2) (alphaRank P.m)
    (TernaryCodeSemantics.address P.output.val) (4^TernaryLocalParameters.fixedLength P.m)
    (P.p^(2*P.K)) P.drift P.scale (TernaryLocalParameters.fixedLength P.m)

def suffix (P : Profile κ) : Program :=
  (TernaryExecutable.reporting P.maps P.cap P.K).map (ReportingHostRelocation.relocate 240)++[driver P]

@[simp] theorem libraries_length (P : Profile κ) : (libraries P).length=240 := by
  unfold libraries
  exact LightTernaryColoredSolver.libraries_length _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem color_eq (P : Profile κ) : P.color=libraries P++suffix P := by
  unfold Profile.color TernaryExecutable.color LightTernaryColoredSolver.program
  change (libraries P++(TernaryExecutable.reporting P.maps P.cap P.K).map
    (ReportingHostRelocation.relocate (libraries P).length))++[_]=_
  rw [libraries_length]
  simp only [suffix,driver,List.append_assoc,LightTernaryColoredSolver.libraries_length,Profile.drift,Profile.scale]

/-- Runtime source counts, keys and pointers do not change the compiled
reporter's six local dictionaries. -/
theorem reporting (P : Profile κ) (r : ℕ) (I : Input) :
    let S:=setup (r:=r) P.maps P.threshold P.cap P.output I
    TernaryExecutable.reporting P.maps P.cap P.K=
      LightTernaryPreparedPostSelection.closedProgram S.left.xs S.left.ys S.left.zs
        S.right.xs S.right.ys S.right.zs P.H := by
  rfl

/-- Exact body lookup for the concrete per-color program. -/
theorem main_lookup (P : Profile κ) :
    P.color[TernaryExecutable.colorMain (p:=P.p) P.K]?=
      some (LightTernaryColoredSolver.body (240+TernaryExecutable.reportingMain (p:=P.p) P.K)
        P.m P.F P.p (TernaryLocalParameters.fixedAlpha P.m 2)
        (TernaryArenaSourceSetup.alphaRank P.m) (TernaryCodeSemantics.address P.output.val)
        (4^(TernaryLocalParameters.fixedLength P.m)) (P.p^(2*P.K)) P.drift P.scale
        (TernaryLocalParameters.fixedLength P.m)) := by
  have hh:=TernaryColoredPrefixCall.main_lookup P.radix P.allocation.D P.allocation.E P.K P.radix
    (P.p^(2*P.K)) P.drift P.scale P.p (4^(TernaryLocalParameters.fixedLength P.m)) P.F P.m
    (TernaryLocalParameters.fixedAlpha P.m 2) (TernaryArenaSourceSetup.alphaRank P.m)
    (TernaryCodeSemantics.address P.output.val) (TernaryLocalParameters.fixedLength P.m)
    (TernaryGoodOutputCatalog.raws P.maps P.threshold) (TernaryGoodOutputCatalog.wordCodes P.maps P.threshold)
    (TernaryGoodOutputCatalog.mapCodes P.maps P.threshold)
    ((TernaryExecutable.leftRecords P.maps P.cap).map (TernaryCanonicalDictionaries.native false P.maps))
    ((TernaryExecutable.leftRecords P.maps P.cap).map TernaryCanonicalDictionaries.wordCode)
    ((TernaryExecutable.leftRecords P.maps P.cap).map TernaryCanonicalDictionaries.mapCode)
    ((TernaryExecutable.rightRecords P.maps P.cap).map (TernaryCanonicalDictionaries.native true P.maps))
    ((TernaryExecutable.rightRecords P.maps P.cap).map TernaryCanonicalDictionaries.wordCode)
    ((TernaryExecutable.rightRecords P.maps P.cap).map TernaryCanonicalDictionaries.mapCode)
    (TernaryExecutable.reporting P.maps P.cap P.K) (TernaryExecutable.reportingMain (p:=P.p) P.K)
  simpa only [Profile.color,TernaryExecutable.color,TernaryExecutable.colorMain,
    TernaryExecutable.reporting_length,Profile.H,Profile.drift,Profile.scale] using hh

end ThreeSum.TernaryColoredProgramIdentity
