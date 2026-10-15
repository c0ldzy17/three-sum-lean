import Submission.ThreeSum.LightTernaryColoredSolver
import Submission.ThreeSum.LightColorScanHost

/-! The original three-argument fast-program entry. It prepares the field
once, then executes the entire original-position coloring family. -/
noncomputable section
namespace ThreeSum.LightTernaryFastProgram
open Light
set_option maxRecDepth 24000

def colorsLibrary (M radix p K κ : ℕ) (color : Program) : Program :=
  ReportingHostRelocation.program (LightTernaryGlobalPrelude.program M radix p K κ) color

def parameterLibrary (M radix p K κ : ℕ) (color : Program) : Program :=
  ReportingHostRelocation.program (colorsLibrary M radix p K κ color) LightColorParameters.program

def scanEntry (color : Program) :=52+color.length
def hostEntry (color : Program) :=53+color.length
def mainEntry (color : Program) :=54+color.length

def body (pHost : ℕ) : Stmt :=
  .call 49 [v 1,v 2] 3 ;;
  .set 4 (M (v 3 +' k 6)) ;;
  .set 5 (M (v 3 +' k 8)) ;;
  .call pHost [v 0,v 1,v 4,v 5] 0

def program (M radix p K κ : ℕ) (color : Program) (colorMain : ℕ) : Program :=
  parameterLibrary M radix p K κ color++
    [LightColorScan.body (scanEntry color) (50+color.length) (50+colorMain),
      LightColorScanHost.body (scanEntry color),body (hostEntry color)]

@[simp] theorem colorsLibrary_length (M radix p K κ : ℕ) (color : Program) :
    (colorsLibrary M radix p K κ color).length=50+color.length := by
  simp [colorsLibrary,ReportingHostRelocation.program]
@[simp] theorem parameterLibrary_length (M radix p K κ : ℕ) (color : Program) :
    (parameterLibrary M radix p K κ color).length=52+color.length := by
  simp [parameterLibrary,ReportingHostRelocation.program,LightColorParameters.program]; omega
@[simp] theorem program_length (M radix p K κ : ℕ) (color : Program) (colorMain : ℕ) :
    (program M radix p K κ color colorMain).length=55+color.length := by simp [program]; omega

 def scan_procs (M radix p K κ : ℕ) (color : Program) (colorMain : ℕ) :
    LightColorScan.Procs (program M radix p K κ color colorMain) (scanEntry color) := by
  refine ⟨50+color.length,51+color.length,50+colorMain,?_,?_,?_⟩
  · unfold program scanEntry
    rw [List.getElem?_append_right (by rw [parameterLibrary_length])]
    rw [parameterLibrary_length,Nat.sub_self]
    rfl
  · have hp := ReportingHostRelocation.lookup
      (by rfl : LightColorParameters.program[0]?=some (LightColorParameters.body 1))
      (colorsLibrary M radix p K κ color)
    unfold program
    rw [List.getElem?_append_left (by rw [parameterLibrary_length]; omega)]
    simpa only [parameterLibrary,colorsLibrary_length,Nat.add_zero,
      ReportingHostRelocation.relocate,LightColorParameters.body,Nat.add_assoc,
      show 50+color.length+1=51+color.length by omega] using hp
  · have hp := ReportingHostRelocation.lookup
      (by rfl : LightColorParameters.program[1]?=some LightSmallDivide.body)
      (colorsLibrary M radix p K κ color)
    unfold program
    rw [List.getElem?_append_left (by rw [parameterLibrary_length]; omega)]
    simpa only [parameterLibrary,colorsLibrary_length,
      ReportingHostRelocation.relocate,LightSmallDivide.body,
      show 50+color.length+1=51+color.length by omega] using hp

def host_procs (M radix p K κ : ℕ) (color : Program) (colorMain : ℕ) :
    LightColorScanHost.Procs (program M radix p K κ color colorMain) (hostEntry color) := by
  refine ⟨scanEntry color,scan_procs M radix p K κ color colorMain,?_⟩
  unfold program hostEntry
  rw [List.getElem?_append_right (by rw [parameterLibrary_length]; omega),parameterLibrary_length]
  rw [show 53+color.length-(52+color.length)=1 by omega]
  rfl

theorem main_lookup (M radix p K κ : ℕ) (color : Program) (colorMain : ℕ) :
    (program M radix p K κ color colorMain)[mainEntry color]?=some (body (hostEntry color)) := by
  unfold program mainEntry
  rw [List.getElem?_append_right (by rw [parameterLibrary_length]; omega),parameterLibrary_length]
  rw [show 54+color.length-(52+color.length)=2 by omega]
  rfl

end ThreeSum.LightTernaryFastProgram
