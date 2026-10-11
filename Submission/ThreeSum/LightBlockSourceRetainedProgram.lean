import Submission.ThreeSum.LightBlockSourceRetainedHost

/-!
# Literal efficient program for original source-stage construction

The 41 procedures construct all occurrence-dependent data and reuse the
original band histograms. The cost has no factor proportional to the number
of original input incidences or the dense global modulus in this inner loop.
-/

namespace ThreeSum.LightBlockSourceRetainedProgram

open Light LightPascal LightSubsetAddress LightBlockSourceRetainedHost
open LocalCoverBounds SubsetAddress BlockSourceEncoding LightBlockSourceBuild

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

def program : Program :=
  [LightBlockSourceRetainedHost.body 1 5 22,
    LightDownsetEnumerationSetup.body 2 3,powTableBody,
    LightDownsetEnumeration.body 4,LightSubsetEnumeration.body 4,
    LightSourcePreparation.body 6 12,LightBlockSourceHashes.body 7 10,
    LightBlockCoefficients.body 8 9,powTableBody,LightScaleArray.body,
    LightMaskHashes.body 8 11,LightOneHot.body 11,
    LightSourceFlagArray.body 13,LightSourceMaskFlags.body 14 17,
    LightMaskBits.body 15 16,powTableBody,LightMaskErase.body 16,
    LightSourceTrim.body 18,LightSourceRowFlag.body 19 20 21,
    LightSourceRowScan.body,emodBody,LightSourceFlagTest.body,
    LightSourceRetainedStages.body 23 25,LightSourceGather.body 24,emodBody,
    LightZetaStages.body 26 27,LightDownsetSize.body 31 38,
    LightZetaPass.body 28 29,LightSubsetEnumerationSetup.body 36 40,
    LightZetaBatch.body 30,LightZetaCell.body 31 38 39 37,
    LightSubsetSetup.body 32 36 37,buildBody 33 34,fillBody,rowBody 35,
    LightArray.linearBody,powTableBody,rankBody 37,LightSubsetOffset.body,
    LightMaskErase.body 39,LightSubsetEnumeration.body 40]

def programProcs : LightBlockSourceRetainedHost.Procs program 0 :=
  ⟨1,2,3,4,5,22,rfl,rfl,rfl,rfl,
    ⟨6,12,⟨7,8,9,10,11,rfl,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨13,⟨14,15,16,17,rfl,rfl,rfl,⟨18,19,20,21,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩,
    ⟨23,24,25,rfl,rfl,
      ⟨26,27,28,40,29,30,31,32,33,34,35,36,37,38,39,
        rfl,rfl,rfl,rfl,rfl,rfl,rfl,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,rfl⟩,rfl⟩

theorem program_length : program.length = 41 := rfl

theorem time_bound {h J cut : ℕ} (hcut : cut ≤ J*(512*h)) :
    LightBlockSourceRetainedHost.time h J cut ≤
      1200*(J*(512*h)+1)^2*(downsetCap (J*(512*h)) cut+1)+
      300*(J+1)*(512*h+1)+600*(J*(512*h)+1)*(downsetCap (J*(512*h)) cut+1)+
      downsetCap (J*(512*h)) cut*(300*(J*(512*h)+1)^2+
        J*(150*(512*h)+464*(Nat.log 2 ((512*h)*localPrime h+1)+1)+250)+400)+
      314*downsetCap (J*(512*h)) cut*(Nat.log 2 (endpointBound h J+1)+1)+
      12000*(J*(512*h)+1)^4*(downsetCap (J*(512*h)) cut+1)+1122 := by
  have he := LightDownsetEnumerationSetup.time_bound hcut
  have hp := LightSourcePreparation.time_bound (downsetCap (J*(512*h)) cut) J (512*h) (localPrime h)
  have hs := LightSourceRetainedStages.time_bound (E := endpointBound h J) hcut
  unfold LightBlockSourceRetainedHost.time
  nlinarith

def factor (h J : ℕ) : ℕ :=
  1200*(J*(512*h)+1)^2+300*(J+1)*(512*h+1)+600*(J*(512*h)+1)+
  (300*(J*(512*h)+1)^2+J*(150*(512*h)+464*(Nat.log 2 ((512*h)*localPrime h+1)+1)+250)+400)+
  314*(Nat.log 2 (endpointBound h J+1)+1)+12000*(J*(512*h)+1)^4+1122

theorem time_le_factor {h J cut : ℕ} (hcut : cut ≤ J*(512*h)) :
    LightBlockSourceRetainedHost.time h J cut ≤ factor h J*(downsetCap (J*(512*h)) cut+1) := by
  have ht := time_bound hcut
  have hc := Nat.le_succ (downsetCap (J*(512*h)) cut)
  have hsetup : 300*(J+1)*(512*h+1) ≤
      300*(J+1)*(512*h+1)*(downsetCap (J*(512*h)) cut+1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have htrim := Nat.mul_le_mul_right
    (300*(J*(512*h)+1)^2+J*(150*(512*h)+464*(Nat.log 2 ((512*h)*localPrime h+1)+1)+250)+400) hc
  have hg := Nat.mul_le_mul_left (314*(Nat.log 2 (endpointBound h J+1)+1)) hc
  have hconst : 1122 ≤ 1122*(downsetCap (J*(512*h)) cut+1) := by omega
  unfold factor
  nlinarith

end ThreeSum.LightBlockSourceRetainedProgram
