import Submission.ThreeSum.LightBlockSourcePreparation
import Submission.ThreeSum.BlockSourceCoverInput

/-!
# Actual terminal endpoint and independent flag arrays

The two complete endpoint-mask arrays are prepared using the actual selected
occurrence, coefficient, and local trimming tables. Their buffers are
allocated by the host. Only the left orientation of the first array and the
right orientation of the second array are needed by the physical leaf scan.
-/

namespace ThreeSum.LightReportingTerminalPreparation

open Light BlockRows BlockIndex BlockEncoding BlockCoefficientRows BlockSourceFlags
open GlobalEncoding LocalCoverBounds

set_option maxHeartbeats 2600000
set_option maxRecDepth 12000

def span (W n : ℕ) : ℕ := 2*W+4*n+2
def second (base W n : ℕ) : ℕ := base+span W n
def leftRaw (base W : ℕ) : ℕ := base+2*W
def leftFlags (base W n : ℕ) : ℕ := base+2*W+2*n
def rightRaw (base W n : ℕ) : ℕ := second base W n+2*W+n
def rightFlags (base W n : ℕ) : ℕ := second base W n+2*W+3*n
def stop (base W n : ℕ) : ℕ := base+2*span W n

/-- J, L, h, local prime and cap; retained control pointers; two full-mask
arrays and their count; output base; bit, row, and arithmetic scratch. -/
def body (pPrepare : ℕ) : Stmt :=
  .set 17 (v 0 *' v 1) ;;
  .set 18 (k 2 *' v 17 +' k 4 *' v 12 +' k 2) ;;
  .set 19 (v 13 +' v 17) ;;
  .set 20 (v 13 +' k 2 *' v 17) ;;
  .set 21 (v 20 +' v 12) ;;
  .set 22 (v 21 +' v 12) ;;
  .set 23 (v 13 +' v 18) ;;
  .set 24 (v 23 +' v 17) ;;
  .set 25 (v 23 +' k 2 *' v 17) ;;
  .set 26 (v 25 +' v 12) ;;
  .set 27 (v 26 +' v 12) ;;
  .call pPrepare [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 12,v 13,v 19,v 20,v 21,v 22,v 14,v 15,v 16] 28 ;;
  .call pPrepare [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 11,v 12,v 23,v 24,v 25,v 26,v 27,v 14,v 15,v 16] 28 ;;
  .set 0 (v 23 +' v 18)

def program : Program := LightSourcePreparation.program ++ [body 0]
def time (h J n : ℕ) : ℕ := 2*LightSourcePreparation.time n J (512*h) (localPrime h)+800

variable {lim : Limits}

theorem program_meets {μ : ℕ→ℤ}
    {h J occ maps candidates histL histR masksL masksR n base bitBase rowOut work d : ℕ}
    (o : Occurrences h J) (setsL setsR : ℕ→Finset (Coord J (512*h)))
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+J*(512*h)+6≤lim.depth)
    (hocc : occ+J≤base) (hmaps : maps+2*(512*h)*scheduleSize h≤base)
    (hcandidates : candidates+scheduleSize h≤base)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h≤base)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h≤base)
    (hmasksL : masksL+n≤base) (hmasksR : masksR+n≤base)
    (hstop : stop base (J*(512*h)) n≤bitBase)
    (hbits : bitBase+J*(512*h)≤rowOut) (hrowOut : rowOut+2≤work)
    (hspace : LightSourcePreparation.space work J (512*h) (localPrime h)≤lim.space)
    (hword : (LightSourcePreparation.word J (512*h) (localPrime h) (localPrime h)
      ((512*h).choose h) (localBucketCap h) : ℤ)≤lim.word)
    (hoccRead : ∀ j<J, μ (occ+j)=(occurrenceIndices o j : ℤ))
    (hcover : BlockSourceCoverInput.Input μ h maps candidates histL histR)
    (hmaskL : ∀ i<n, μ (masksL+i)=(SubsetAddress.subsetMask (indexSet (setsL i)) : ℤ))
    (hmaskR : ∀ i<n, μ (masksR+i)=(SubsetAddress.subsetMask (indexSet (setsR i)) : ℤ)) :
    Meets lim program 17 d
      [J,512*h,h,localPrime h,localBucketCap h,occ,maps,candidates,histL,histR,masksL,masksR,n,base,bitBase,rowOut,work]
      μ (time h J n) (fun r ν => r=(stop base (J*(512*h)) n : ℤ) ∧
        (∀ i<n, ν (leftRaw base (J*(512*h))+i)=endpointLeft o (setsL i)) ∧
        (∀ i<n, ν (rightRaw base (J*(512*h)) n+i)=endpointRight o (setsR i)) ∧
        (∀ i<n, ν (leftFlags base (J*(512*h)) n+i)=(if LeftAllowed o (setsL i) then 1 else 0 : ℕ)) ∧
        (∀ i<n, ν (rightFlags base (J*(512*h)) n+i)=(if RightAllowed o (setsR i) then 1 else 0 : ℕ)) ∧
        Kept μ ν base) := by
  let W := J*(512*h)
  let next := second base W n
  have hstop' : base+2*(2*W+4*n+2)≤bitBase := hstop
  have hwork : work≤lim.space := by
    have hh := (le_max_left _ _).trans hspace
    change work+max (J+1) (J*(512*h)+1)≤lim.space at hh
    omega
  have hW : W≤lim.space := by change bitBase+W≤rowOut at hbits; omega
  have hWZ : (J : ℤ)*(512*(h : ℤ))=(W : ℤ) := by simp [W]
  have hnext : next=base+(2*W+4*n+2) := rfl
  have hspan : span W n≤lim.space := by unfold span; omega
  have hnextBound : next+2*W+4*n+2≤bitBase := by rw [hnext]; omega
  have hprepareL := (LightBlockSourcePreparation.meets (d := d+1) (μ := μ)
    LightSourcePreparation.programProcs
    (occ := occ) (maps := maps) (candidates := candidates) (histL := histL) (histR := histR)
    (masks := masksL) (n := n) (coeff0 := base) (coeff1 := base+W)
    (rawLeft := base+2*W) (rawRight := base+2*W+n) (flags := base+2*W+2*n)
    (bitBase := bitBase) (rowOut := rowOut) (work := work) o setsL
    hw (by omega) hocc hmaps hcandidates hleft hright hmasksL
    (by change base+W≤base+W; omega) (by change base+W+W≤base+2*W; omega)
    (by omega) (by omega) (by omega) hbits hrowOut hspace hword hoccRead
    hcover.candidates hcover.leftRows hcover.rightRows hcover.leftCounts hcover.rightCounts hmaskL).append [body 0]
  apply Meets.of_body (p := 17) (by rfl : program[17]?=some (body 0))
  unfold body time
  light_set (W : ℕ) using hWZ,LightSourcePreparation.time
  light_set (span W n : ℕ) using span,LightSourcePreparation.time
  light_set (base+W : ℕ) using LightSourcePreparation.time
  light_set (base+2*W : ℕ) using LightSourcePreparation.time
  light_set (base+2*W+n : ℕ) using LightSourcePreparation.time
  light_set (base+2*W+2*n : ℕ) using LightSourcePreparation.time
  light_set (next : ℕ) using next,second,span,LightSourcePreparation.time
  light_set (next+W : ℕ) using LightSourcePreparation.time
  light_set (next+2*W : ℕ) using LightSourcePreparation.time
  light_set (next+2*W+n : ℕ) using LightSourcePreparation.time
  light_set (next+2*W+2*n : ℕ) using LightSourcePreparation.time
  light_call hprepareL using LightSourcePreparation.time with unused ν₁ ⟨hrawL,_,hflagsL,_,hkeepL⟩
  have hcoverR := hcover.of_kept hkeepL hmaps hcandidates hleft hright
  have hoccR : ∀ j<J, ν₁ (occ+j)=(occurrenceIndices o j : ℤ) :=
    fun j hj => (hkeepL _ (by omega)).trans (hoccRead j hj)
  have hmaskR' : ∀ i<n, ν₁ (masksR+i)=(SubsetAddress.subsetMask (indexSet (setsR i)) : ℤ) :=
    fun i hi => (hkeepL _ (by omega)).trans (hmaskR i hi)
  have hprepareR := (LightBlockSourcePreparation.meets (d := d+1) (μ := ν₁)
    LightSourcePreparation.programProcs
    (occ := occ) (maps := maps) (candidates := candidates) (histL := histL) (histR := histR)
    (masks := masksR) (n := n) (coeff0 := next) (coeff1 := next+W)
    (rawLeft := next+2*W) (rawRight := next+2*W+n) (flags := next+2*W+2*n)
    (bitBase := bitBase) (rowOut := rowOut) (work := work) o setsR
    hw (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by change next+W≤next+W; omega) (by change next+W+W≤next+2*W; omega)
    (by omega) (by omega) (by omega) hbits hrowOut hspace hword hoccR
    hcoverR.candidates hcoverR.leftRows hcoverR.rightRows hcoverR.leftCounts hcoverR.rightCounts hmaskR').append [body 0]
  light_call hprepareR using LightSourcePreparation.time with unused ν₂ ⟨_,hrawR,_,hflagsR,hkeepR⟩
  have hstopWord : stop base W n≤lim.space := hstop.trans (by omega)
  light_set (stop base W n : ℕ) using stop,next,second,span,LightSourcePreparation.time
  refine ⟨by simp [W],?_,hrawR,?_,?_,?_⟩
  · intro i hi
    exact (hkeepR _ (by unfold leftRaw; omega)).trans (hrawL i hi)
  · intro i hi
    exact (hkeepR _ (by unfold leftFlags; omega)).trans (hflagsL i hi)
  · intro i hi
    simpa only [rightFlags,← hnext,Nat.add_assoc,show 2*n+n=3*n by omega] using hflagsR i hi
  · intro i hi
    exact (hkeepR i (by omega)).trans (hkeepL i hi)

end ThreeSum.LightReportingTerminalPreparation
