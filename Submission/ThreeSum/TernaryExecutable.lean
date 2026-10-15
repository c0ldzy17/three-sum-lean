import Submission.ThreeSum.LightTernaryFastProgram
import Submission.ThreeSum.LightTernaryPreparedPostSelection
import Submission.ThreeSum.TernaryCanonicalDictionaries
import Submission.ThreeSum.TernaryArenaSourceSetup
import Submission.ThreeSum.TernaryGoodOutputCatalog

/-! A single fixed finite executable built only from the actual canonical
local catalogs and the verified component libraries. All input-dependent
counts, pointers, fields, rows and selected prefixes are runtime data. -/
noncomputable section
namespace ThreeSum.TernaryExecutable
open Light TernaryLocalParameters TernaryCoverGoodMaps TernaryCanonicalDictionaries
variable {p m F : ℕ} [Fact p.Prime]

def leftRecords (maps : Fin F→Weight m p) (cap : ℕ) :=records (α := fixedAlpha m) false maps cap
def rightRecords (maps : Fin F→Weight m p) (cap : ℕ) :=records (α := fixedAlpha m) true maps cap

def reporting (maps : Fin F→Weight m p) (cap K : ℕ) : Program :=
  LightTernaryPreparedPostSelection.closedProgram
    ((leftRecords maps cap).map (native false maps)) ((leftRecords maps cap).map wordCode)
    ((leftRecords maps cap).map mapCode) ((rightRecords maps cap).map (native true maps))
    ((rightRecords maps cap).map wordCode) ((rightRecords maps cap).map mapCode) (2*p^K)

def reportingMain (K : ℕ) :=127*(TernaryMomentSchedule.channels (2*(2*p^K)+1)).length+24

def color (maps : Fin F→Weight m p) (τ cap M radix K D E : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) : Program :=
  LightTernaryColoredSolver.program radix D E K radix
    (p^(2*K)) (9*F*M*(TernaryGoodOutputCatalog.Rbar m)^K)
    (2^((fixedPi m 2)*K)) p (4^(fixedLength m)) F m (fixedAlpha m 2)
    (TernaryArenaSourceSetup.alphaRank m) (TernaryCodeSemantics.address Q.val) (fixedLength m)
    (TernaryGoodOutputCatalog.raws maps τ) (TernaryGoodOutputCatalog.wordCodes maps τ)
    (TernaryGoodOutputCatalog.mapCodes maps τ)
    ((leftRecords maps cap).map (native false maps)) ((leftRecords maps cap).map wordCode)
    ((leftRecords maps cap).map mapCode) ((rightRecords maps cap).map (native true maps))
    ((rightRecords maps cap).map wordCode) ((rightRecords maps cap).map mapCode)
    (reporting maps cap K) (reportingMain (p := p) K)

def colorMain (K : ℕ) :=240+(reportingMain (p := p) K+1)

def program (maps : Fin F→Weight m p) (τ cap M radix K D E κ : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) : Program :=
  LightTernaryFastProgram.program M radix p K κ (color maps τ cap M radix K D E Q)
    (colorMain (p := p) K)

def main (K : ℕ) :=54+(colorMain (p := p) K+1)

@[simp] theorem reporting_length (maps : Fin F→Weight m p) (cap K : ℕ) :
    (reporting maps cap K).length=reportingMain (p := p) K+1 := by
  simp only [reporting,LightTernaryPreparedPostSelection.closedProgram_length,reportingMain] <;> omega

@[simp] theorem color_length (maps : Fin F→Weight m p) (τ cap M radix K D E : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) :
    (color maps τ cap M radix K D E Q).length=colorMain (p := p) K+1 := by
  unfold color LightTernaryColoredSolver.program
  simp only [List.length_append,ReportingHostRelocation.program,List.length_map,
    LightTernaryColoredSolver.libraries_length,reporting_length,List.length_cons,List.length_nil,colorMain] <;> omega

@[simp] theorem program_length (maps : Fin F→Weight m p) (τ cap M radix K D E κ : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) :
    (program maps τ cap M radix K D E κ Q).length=main (p := p) K+1 := by
  simp only [program,LightTernaryFastProgram.program_length,color_length,main] <;> omega

theorem main_lookup (maps : Fin F→Weight m p) (τ cap M radix K D E κ : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) :
    (program maps τ cap M radix K D E κ Q)[main (p := p) K]?=
      some (LightTernaryFastProgram.body
        (LightTernaryFastProgram.hostEntry (color maps τ cap M radix K D E Q))) := by
  have hh := LightTernaryFastProgram.main_lookup M radix p K κ
    (color maps τ cap M radix K D E Q) (colorMain (p := p) K)
  simpa only [program,LightTernaryFastProgram.mainEntry,color_length,main] using hh

end ThreeSum.TernaryExecutable
