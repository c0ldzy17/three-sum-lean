import Submission.ThreeSum.LightSourceBandBanks
import Submission.ThreeSum.LightBlockSourceBatchProgram

/-! # Closed program for one shared occurrence table and all original source banks -/

namespace ThreeSum.LightSourceBandBanksProgram

open Light

def program : Program := LightBlockSourceBatchProgram.program ++
  [LightSourceBandHistSelect.body,LightSourceBandBankStep.body 43 42,
    LightSourceBandBankBatch.body 44,LightSourceOccurrenceArray.body 47,
    LightOutputDecodeDigits.body 48,LightOutputDecodeDivide.body,LightSourceBandBanks.body 46 45]

def sourceProcs : LightBlockSourceRetainedHost.Procs program 0 :=
  ⟨1,2,3,4,5,22,rfl,rfl,rfl,rfl,
    ⟨6,12,⟨7,8,9,10,11,rfl,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨13,⟨14,15,16,17,rfl,rfl,rfl,⟨18,19,20,21,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩,
    ⟨23,24,25,rfl,rfl,
      ⟨26,27,28,40,29,30,31,32,33,34,35,36,37,38,39,
        rfl,rfl,rfl,rfl,rfl,rfl,rfl,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,rfl⟩,rfl⟩

def batchProcs : LightBlockSourceBatch.Procs program 42 :=
  ⟨41,⟨0,sourceProcs,rfl⟩,rfl⟩

def programProcs : LightSourceBandBanks.Procs program 49 :=
  ⟨46,47,48,45,rfl,rfl,rfl,⟨44,⟨43,42,rfl,batchProcs,rfl⟩,rfl⟩,rfl⟩

theorem program_length : program.length=50 := rfl

end ThreeSum.LightSourceBandBanksProgram
