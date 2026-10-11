import Submission.ThreeSum.LightSourceBandHost

/-! # Closed original-array-to-shared-source-bank program -/

namespace ThreeSum.LightSourceBandHostProgram

open Light

def program : Program := LightSourceBandBanksProgram.program ++
  [LightSourceBucketOriginal.body 51 56,LightSourceHistogram.body 52 54,
    LightSourceResidues.body 53,emodBody,LightHistogram.histogramBody 55,fillBody,
    LightSourceBucketFromHistogram.body 57 58,LightSourceBucketOffsets.body,LightSourceBucketScatter.body,
    LightSourceBandStep.body 50,LightSourceBandBatch.body 59,LightSmallDivide.body,
    LightSourceBandSetup.body 61 60,LightSourceBandPair.body 62 55,LightSourceBandHost.body 63 49]

def sourceProcs : LightBlockSourceRetainedHost.Procs program 0 :=
  ⟨1,2,3,4,5,22,rfl,rfl,rfl,rfl,
    ⟨6,12,⟨7,8,9,10,11,rfl,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨13,⟨14,15,16,17,rfl,rfl,rfl,⟨18,19,20,21,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩,
    ⟨23,24,25,rfl,rfl,
      ⟨26,27,28,40,29,30,31,32,33,34,35,36,37,38,39,
        rfl,rfl,rfl,rfl,rfl,rfl,rfl,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,rfl⟩,rfl⟩

def batchProcs : LightBlockSourceBatch.Procs program 42 := ⟨41,⟨0,sourceProcs,rfl⟩,rfl⟩

def banksProcs : LightSourceBandBanks.Procs program 49 :=
  ⟨46,47,48,45,rfl,rfl,rfl,⟨44,⟨43,42,rfl,batchProcs,rfl⟩,rfl⟩,rfl⟩

def originalProcs : LightSourceBucketOriginal.Procs program 50 :=
  ⟨51,56,⟨52,53,54,55,rfl,rfl,rfl,rfl,rfl⟩,⟨57,58,rfl,rfl,rfl⟩,rfl⟩

def setupProcs : LightSourceBandSetup.Procs program 62 :=
  ⟨61,60,rfl,⟨59,⟨50,originalProcs,rfl⟩,rfl⟩,rfl⟩

def pairProcs : LightSourceBandPair.Procs program 63 := ⟨62,55,setupProcs,rfl,rfl⟩

def programProcs : LightSourceBandHost.Procs program 64 := ⟨63,49,pairProcs,banksProcs,rfl⟩

theorem program_length : program.length=65 := rfl

end ThreeSum.LightSourceBandHostProgram
