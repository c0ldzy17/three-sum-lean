import Submission.ThreeSum.LightSourceBandSetup
import Submission.ThreeSum.SourceBandCosts

/-! # Closed original-band histogram and physical bucket program -/

namespace ThreeSum.LightSourceBandProgram

open Light

def program : Program :=
  LightSourceBucketOriginal.program ++
    [LightSourceBandStep.body 0,LightSourceBandBatch.body 9,
      LightSmallDivide.body,LightSourceBandSetup.body 11 10]

def originalProcs : LightSourceBucketOriginal.Procs program 0 :=
  ⟨1,6,⟨2,3,4,5,rfl,rfl,rfl,rfl,rfl⟩,⟨7,8,rfl,rfl,rfl⟩,rfl⟩

def programProcs : LightSourceBandSetup.Procs program 12 :=
  ⟨11,10,rfl,⟨9,⟨0,originalProcs,rfl⟩,rfl⟩,rfl⟩

theorem program_length : program.length=13 := rfl

end ThreeSum.LightSourceBandProgram
