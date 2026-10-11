import Submission.ThreeSum.ThreeSumWantedHostData

/-!
# Load the retained color headers and execute the actual wanted scan

All controls passed to the fixed153 scan are read from the initialized
parameter, normalization, encoding and reporting headers. The raw-owner
array is located using the actual three band counts stored by normalization.
-/

namespace ThreeSum.LightThreeSumWantedHost

open Light Scales BandScales ThreeSumReportingSetupData ThreeSumWantedHostData
open BandPartition EncodedColorNormalizedData

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

local instance (n : ℕ) : NeZero (radix n) := ⟨Nat.ne_of_gt (radix_pos n)⟩

/-- n, parameter header, normalized header, encoded result header, counter. -/
def body (pScan : ℕ) : Stmt :=
  .set 5 (v 4 +' k 4) ;;
  .set 6 (M (v 1 +' k 3)) ;;
  .set 7 (M (v 1 +' k 1)) ;;
  .set 8 (v 3 +' k 8) ;;
  .set 9 (M (v 8 +' k 2)) ;;
  .set 10 (v 9 -' k 1) ;;
  .set 11 (M (v 3 +' k 6)) ;;
  .set 12 (M (v 2 +' k 1)) ;;
  .set 13 (M (v 2 +' k 3)) ;;
  .set 14 (M (v 2 +' k 5)) ;;
  .set 15 (M (v 13)) ;;
  .set 16 (M (v 14)) ;;
  .set 17 (M (v 3 +' k 1)) ;;
  .set 18 (M (v 3 +' k 2)) ;;
  .set 19 (M (v 18)) ;;
  .set 20 (M (v 18 +' k 1)) ;;
  .set 21 (M (v 17)) ;;
  .set 22 (M (v 17 +' k 10)) ;;
  .set 23 (M (v 17 +' k 18)) ;;
  .set 24 (M (v 2 +' k 7)) ;;
  .set 25 (M (v 2 +' k 6)) ;;
  .set 26 (M (v 3 +' k 3)) ;;
  .set 27 (v 26 +' k 3) ;;
  .set 28 (M (v 3 +' k 4)) ;;
  .set 29 (M (v 2 +' k 2)) ;;
  .set 30 (M (v 2 +' k 4)) ;;
  .set 31 (M (v 1 +' k 14)) ;;
  .set 32 (M (v 1 +' k 17)) ;;
  .set 33 (M (v 12 +' k 1)) ;;
  .set 34 (M (v 13 +' k 1)) ;;
  .set 35 (M (v 14 +' k 1)) ;;
  .set 36 (v 34 *' v 35 +' v 33 *' v 34 +' v 33 *' v 35) ;;
  .set 37 (v 24 +' v 32 *' v 36) ;;
  .call pScan [v 19,v 5,v 6,v 7,v 10,v 11,v 15,v 16,v 17,v 4,v 20,v 21,v 22,
    v 23,v 24,v 37,v 25,v 27,v 28,v 29,v 30,v 8,v 31] 0

def program : Program := LightReportingWantedScan.program++[body 152]

theorem program_length : program.length=154 := rfl

def word (n : ℕ) : ℕ := n+blockCount (inputBits n)+microHalf (inputBits n)+
  LightSwitchDepth.depth (blockCount (inputBits n))+bandSize n+radix n+
  OutputDecodeRecords.layerCount (microHalf (inputBits n))+
  GlobalEncoding.scheduleSize (microHalf (inputBits n))+
  ColorBandBounds.count n (bandSize n)+bandSize n*ColorBandBounds.count n (bandSize n)+50

end ThreeSum.LightThreeSumWantedHost
