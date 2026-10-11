import Submission.ThreeSum.LightEncodedColorSources
import Submission.ThreeSum.SourceFiniteCosts

/-! # Original-size resource envelope for the actual source-header adapter -/

namespace ThreeSum.EncodedColorSourcesCosts

open Scales TrimScales BandScales

def time (n p U M : ℕ) : ℕ :=
  LightNatPower.time (blockCount (inputBits n))+SourceFiniteCosts.time n p U M+1000

theorem time_le {NL NR n p U M : ℕ} (hn : 0 < n) (hL : NL ≤ n) (hR : NR ≤ n) :
    LightEncodedColorSources.time NL NR (bandSize n) p (microHalf (inputBits n))
      (blockCount (inputBits n)) (mu n) U M ≤ time n p U M := by
  have h := SourceFiniteCosts.time_le (p := p) (U := U) (D := M) hn hL hR
  unfold LightEncodedColorSources.time time
  omega

theorem time_eq (n p U M : ℕ) :
    time n p U M=SourceFiniteCosts.time n p U M+20*blockCount (inputBits n)+1020 := by
  unfold time LightNatPower.time
  omega

end ThreeSum.EncodedColorSourcesCosts
