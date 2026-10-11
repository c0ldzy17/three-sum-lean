import Submission.ThreeSum.SourceBandBanksCosts

/-! # Arithmetic dimensions of the original shared source bank -/

namespace ThreeSum.SourceControlLayout

open GlobalEncoding LocalCoverBounds BlockSourceEncoding SubsetAddress

def scratch (J W logP logE : ℕ) : ℕ :=
  max (max (max ((W+1)^2+(W+1)) (logE+2)) (logP+5)) (J+1)

def stride (W K : ℕ) : ℕ := 5*K+2*W+4+2*(W+1)*K

def span (J W K S logP logE : ℕ) : ℕ :=
  S*stride W K+K+W+2+scratch J W logP logE

def word (J W K S logP logE : ℕ) : ℕ :=
  span J W K S logP logE+stride W K+J+W+K+S+logP+logE+(W+1)^2+30

theorem scratch_eq (h J : ℕ) :
    scratch J (J*(512*h)) (Nat.log 2 ((512*h)*localPrime h+1))
      (Nat.log 2 (LightBlockSourceBuild.endpointBound h J+1)) =
      LightBlockSourceRetainedHost.space 0 h J := by
  unfold scratch LightBlockSourceRetainedHost.space LightSourcePreparation.space
    LightBlockSourceHashes.space LightSourceMaskFlags.space LightSourceRetainedStages.space
    LightPascal.tableSize
  omega

theorem stride_eq (W cut : ℕ) :
    stride W (downsetCap W cut)=LightBlockSourceBatchLayout.stride W cut+2 := by
  unfold stride LightBlockSourceBatchLayout.stride LightBlockSourceBatchLayout.family
  ring

theorem span_eq (h J cut : ℕ) :
    span J (J*(512*h)) (downsetCap (J*(512*h)) cut) (LightBlockSourceCatalog.count h J)
      (Nat.log 2 ((512*h)*localPrime h+1)) (Nat.log 2 (LightBlockSourceBuild.endpointBound h J+1)) =
      SourceBandBankLayout.span h J cut := by
  unfold span
  rw [scratch_eq,stride_eq,SourceBandBanksCosts.span_eq]

def values (h J cut : ℕ) : List ℤ :=
  [downsetCap (J*(512*h)) cut,LightBlockSourceCatalog.count h J,SourceBandBankLayout.span h J cut]

end ThreeSum.SourceControlLayout
