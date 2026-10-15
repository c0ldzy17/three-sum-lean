import Submission.ThreeSum.LightTernarySourceCountHost
import Submission.ThreeSum.LightTernaryTaggedChannel
import Submission.ThreeSum.LightTernaryPairedPotentialBatch
import Submission.ThreeSum.LightTernaryTensorScatter

/-! The actual fourth-channel driver. Its 106-cell immutable host header
holds the concrete SourceCountHost arguments. Slots20/43 point to the two
actual channel-weight arrays; slots104/105 hold wanted count/count output.
The only loops are real radix decoding, weighted source/count calls,
tensor stores, and the checked paired-potential arithmetic. -/
noncomputable section
namespace ThreeSum.LightTernaryTensorDriver
open Light

def countArgs : List Expr := (List.range 106).map (fun i => M (v 0 +' k i))

/-- Arguments: hostConfig, leftTagged,nLeft,rightTagged,nRight,J,
leftWeights,rightWeights,tensor,wantedCount,countOutput,quadScratch,
quadPowers,potentialColumns,potentialPowers. -/
def body (pPowers pRow pStep pPotentialBatch : ℕ) : Stmt :=
  .set 15 (v 5 +' k 2) ;;
  .call pPowers [v 12,k 5,v 15] 17 ;;
  .set 16 (M (v 12 +' k 4)) ;;
  .for 18 (v 16) (
    .call pRow [k 4,v 15,v 18,v 12,k 0,k 1,v 11,k 4] 19 ;;
    .call pStep [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,
      M (v 11),M (v 11 +' k 1),M (v 11 +' k 2),M (v 11 +' k 3),v 18,v 16] 20) ;;
  .call pPotentialBatch [v 8,v 15,v 9,v 13,v 14] 0

def time (K J nLeft nRight wantedCount hostTime : ℕ) : ℕ :=
  powTableTime 5+(J+2)^4*(LightWeightRow.time 4 ((J+2)^4)+
    LightTernaryTaggedChannel.time nLeft+LightTernaryTaggedChannel.time nRight+
    hostTime+LightTernaryTensorScatter.time wantedCount+2000)+
    LightTernaryPairedPotentialBatch.time K (J+2) wantedCount+1000


end ThreeSum.LightTernaryTensorDriver
