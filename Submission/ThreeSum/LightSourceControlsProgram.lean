import Submission.ThreeSum.LightSourceControls

/-! # Closed source-dimension control program -/

namespace ThreeSum.LightSourceControlsProgram

open Light

def program : Program := LightDownsetSize.program ++
  [LightNatPower.body,log2Body,LightSourceControlsMax.body,
    LightSourceControlsSpan.body 11,LightSourceControls.body 9 0 10 12]

def programProcs : LightSourceControls.Procs program 13 :=
  ⟨9,0,10,12,11,1,2,3,4,5,6,7,8,rfl,rfl,
    ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl⟩

theorem program_length : program.length=14 := rfl

end ThreeSum.LightSourceControlsProgram
