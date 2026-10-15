import Submission.ThreeSum.LightTernaryQuarticStep

noncomputable section
namespace ThreeSum.LightTernaryTensorDriver
open Light

def channelLibraries (xl yl zl xr yr zr : List ℤ) : Program :=
  ReportingHostRelocation.program (LightTernarySourceCountHost.program xl yl zl xr yr zr)
    LightTernaryTaggedChannel.program

def quadLibraries (xl yl zl xr yr zr : List ℤ) : Program :=
  ReportingHostRelocation.program (channelLibraries xl yl zl xr yr zr) LightWeightRow.program

def potentialLibraries (xl yl zl xr yr zr : List ℤ) (K : ℕ) : Program :=
  ReportingHostRelocation.program (quadLibraries xl yl zl xr yr zr)
    (LightTernaryPairedPotential.program K)

def program (xl yl zl xr yr zr : List ℤ) (K : ℕ) : Program :=
  potentialLibraries xl yl zl xr yr zr K++
    [LightTernaryPairedPotentialBatch.body 129,LightTernaryTensorScatter.body,
      LightTernaryQuarticStep.body 123 122 136,body 130 126 137 135]

@[simp] theorem channelLibraries_length (xl yl zl xr yr zr : List ℤ) :
    (channelLibraries xl yl zl xr yr zr).length=126 := by
  simp [channelLibraries,ReportingHostRelocation.program,LightTernaryTaggedChannel.program]
@[simp] theorem quadLibraries_length (xl yl zl xr yr zr : List ℤ) :
    (quadLibraries xl yl zl xr yr zr).length=129 := by
  simp [quadLibraries,ReportingHostRelocation.program,LightWeightRow.program]
@[simp] theorem potentialLibraries_length (xl yl zl xr yr zr : List ℤ) (K : ℕ) :
    (potentialLibraries xl yl zl xr yr zr K).length=135 := by
  simp [potentialLibraries,ReportingHostRelocation.program,LightTernaryPairedPotential.program]
@[simp] theorem program_length (xl yl zl xr yr zr : List ℤ) (K : ℕ) :
    (program xl yl zl xr yr zr K).length=139 := by simp [program]

def entry : ℕ := 138

@[simp] theorem program_main (xl yl zl xr yr zr : List ℤ) (K : ℕ) :
    (program xl yl zl xr yr zr K)[entry]?=some (body 130 126 137 135) := by
  unfold program entry
  rw [show 138=(potentialLibraries xl yl zl xr yr zr K).length+3 by rw [potentialLibraries_length]]
  simp

end ThreeSum.LightTernaryTensorDriver
