import Submission.ThreeSum.LightReportingTerminalPreparation
import Submission.ThreeSum.ReportingHostTerminalBatch
import Submission.ThreeSum.ReportingHostRelocation

/-!
# Executed terminal preparation followed by the exact original-value batch

The closed program constructs both endpoint and independent flag arrays
from the retained selected maps, then scans only their selected physical
bucket products. Every library call is an exact relocation of an already
verified implementation.
-/

namespace ThreeSum.LightReportingTerminalPrepared

open Light Finset BlockRows BlockIndex BlockEncoding BlockCoefficientRows
open GlobalEncoding LocalCoverBounds BlockSourceEncoding LightSourceResidues SourceBuckets
open LightReportingTerminalMasks LightBlockSourceBuild

set_option maxHeartbeats 3000000
set_option maxRecDepth 12000

def body (pPrepare pBatch : ℕ) : Stmt :=
  .call pPrepare [v 10,v 11,v 12,v 13,v 14,v 15,v 16,v 17,v 18,v 19,v 20,v 21,v 22,v 23,v 24,v 25,v 26] 27 ;;
  .set 28 (v 10 *' v 11) ;;
  .set 29 (k 2 *' v 28 +' k 4 *' v 22 +' k 2) ;;
  .set 30 (v 23 +' k 2 *' v 28) ;;
  .set 31 (v 23 +' v 29 +' k 2 *' v 28 +' v 22) ;;
  .set 32 (v 23 +' k 2 *' v 28 +' k 2 *' v 22) ;;
  .set 33 (v 23 +' v 29 +' k 2 *' v 28 +' k 3 *' v 22) ;;
  .call pBatch [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 30,v 31,v 32,v 33,v 22,v 26] 0

def libraries : Program := ReportingHostRelocation.program
  LightReportingTerminalPreparation.program LightReportingLeafBatch.program
def program : Program := libraries ++ [body 17 24]

def space (work h J : ℕ) : ℕ :=
  max (LightSourcePreparation.space work J (512*h) (localPrime h))
    (work+4+(Nat.log 2 (endpointBound h J+1)+2))
def word (h J : ℕ) : ℕ :=
  LightSourcePreparation.word J (512*h) (localPrime h) (localPrime h)
    ((512*h).choose h) (localBucketCap h)+4*endpointBound h J+4*modulus h J+16
def time {h J : ℕ} (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (512*h)))) : ℕ :=
  LightReportingTerminalPreparation.time h J (count h J k)+
    ReportingHostTerminalBatch.time p shift left right NL NR q k pre+700

variable {lim : Limits}

theorem program_meets {μ : ℕ→ℤ}
    {h J k srcL srcR offsetsL offsetsR flatL flatR NL NR occ maps candidates histL histR masksL masksR base bitBase rowOut work d : ℕ}
    (av : ℤ) (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ)
    (q : GlobalOutput h J) (pre : List (Finset (Fin (512*h))))
    (HL : Stored μ (fun i => key p (modulus h J) 0 (left i)) NL (modulus h J) offsetsL flatL)
    (HR : Stored μ (fun i => key p (modulus h J) shift (right i)) NR (modulus h J) offsetsR flatR)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+count h J k+J*(512*h)+8≤lim.depth)
    (hsrcL : srcL+NL≤base) (hsrcR : srcR+NR≤base)
    (hoffsetsL : offsetsL+modulus h J+1≤base) (hoffsetsR : offsetsR+modulus h J+1≤base)
    (hflatL : flatL+NL≤base) (hflatR : flatR+NR≤base)
    (hocc : occ+J≤base) (hmaps : maps+2*(512*h)*scheduleSize h≤base)
    (hcandidates : candidates+scheduleSize h≤base)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h≤base)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h≤base)
    (hmasksL : masksL+count h J k≤base) (hmasksR : masksR+count h J k≤base)
    (hstop : LightReportingTerminalPreparation.stop base (J*(512*h)) (count h J k)≤bitBase)
    (hbits : bitBase+J*(512*h)≤rowOut) (hrowOut : rowOut+2≤work)
    (hspace : space work h J≤lim.space) (hword : (word h J : ℤ)≤lim.word)
    (hoccRead : ∀ j<J, μ (occ+j)=(occurrenceIndices (outputOccurrences q) j : ℤ))
    (hcover : BlockSourceCoverInput.Input μ h maps candidates histL histR)
    (hmaskL : ∀ i<count h J k, μ (masksL+i)=(SubsetAddress.subsetMask (indexSet (leftAt q k pre i)) : ℤ))
    (hmaskR : ∀ i<count h J k, μ (masksR+i)=(SubsetAddress.subsetMask (indexSet (rightAt q k pre i)) : ℤ))
    (hreadL : ∀ i<NL, μ (srcL+i)=left i) (hreadR : ∀ j<NR, μ (srcR+j)=right j)
    (hvaluesL : ∀ i<NL, |left i|≤lim.word) (hvaluesR : ∀ j<NR, |right j|≤lim.word)
    (ha : |av|≤lim.word) (htarget : ∀ i<NL, |av+left i|≤lim.word)
    (hcountWord : ((NL*NR : ℕ) : ℤ)≤lim.word) :
    Meets lim program 25 d
      [av,srcL,srcR,offsetsL,flatL,offsetsR,flatR,NL,NR,modulus h J,J,512*h,h,localPrime h,localBucketCap h,
        occ,maps,candidates,histL,histR,masksL,masksR,count h J k,base,bitBase,rowOut,work]
      μ (time p shift left right NL NR q k pre)
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ ReportingHostTerminalBatch.Hit av p shift left right NL NR q k pre) ∧ Kept μ ν base) := by
  let W := J*(512*h)
  let n := count h J k
  have hsPrep : LightSourcePreparation.space work J (512*h) (localPrime h)≤lim.space :=
    (le_max_left _ _).trans hspace
  have hsBatch : work+4+(Nat.log 2 (endpointBound h J+1)+2)≤lim.space :=
    (le_max_right _ _).trans hspace
  have hwPrep : (LightSourcePreparation.word J (512*h) (localPrime h) (localPrime h)
      ((512*h).choose h) (localBucketCap h) : ℤ)≤lim.word := by
    have hh : LightSourcePreparation.word J (512*h) (localPrime h) (localPrime h)
        ((512*h).choose h) (localBucketCap h)≤word h J := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwBatch : (4*endpointBound h J+4*modulus h J+16 : ℤ)≤lim.word := by
    have hh : 4*endpointBound h J+4*modulus h J+16≤word h J := by unfold word; omega
    exact (by exact_mod_cast hh : (4*endpointBound h J+4*modulus h J+16 : ℤ)≤(word h J : ℤ)).trans hword
  have hstop' : base+2*(2*W+4*n+2)≤bitBase := hstop
  have hW : W≤lim.space := by change bitBase+W≤rowOut at hbits; omega
  have hWZ : (J : ℤ)*(512*(h : ℤ))=(W : ℤ) := by simp [W]
  have hkeyL : ∀ i<NL, key p (modulus h J) 0 (left i)<modulus h J :=
    fun i _ => key_lt (modulus_pos h J) 0 (left i)
  have hkeyR : ∀ i<NR, key p (modulus h J) shift (right i)<modulus h J :=
    fun i _ => key_lt (modulus_pos h J) shift (right i)
  have hprep := (LightReportingTerminalPreparation.program_meets (d := d+1) (μ := μ)
    (occ := occ) (maps := maps) (candidates := candidates) (histL := histL) (histR := histR)
    (masksL := masksL) (masksR := masksR) (n := n) (base := base) (bitBase := bitBase)
    (rowOut := rowOut) (work := work) (outputOccurrences q) (leftAt q k pre) (rightAt q k pre)
    hw (by omega) hocc hmaps hcandidates hleft hright hmasksL hmasksR hstop hbits hrowOut
    hsPrep hwPrep hoccRead hcover hmaskL hmaskR).append
      (LightReportingLeafBatch.program.map (ReportingHostRelocation.relocate 18) ++ [body 17 24])
  change Meets lim program 17 (d+1) _ μ
    (LightReportingTerminalPreparation.time h J (count h J k)) _ at hprep
  apply Meets.of_body (p := 25) (by rfl : program[25]?=some (body 17 24))
  unfold body time
  light_call hprep using LightReportingTerminalPreparation.time,ReportingHostTerminalBatch.time
    with unused ν₁ ⟨_,hrawL,hrawR,hflagL,hflagR,hkeep⟩
  have HL₁ := LightReportingLeaf.stored_of_kept HL hkeyL hoffsetsL hflatL hkeep
  have HR₁ := LightReportingLeaf.stored_of_kept HR hkeyR hoffsetsR hflatR hkeep
  light_set (W : ℕ) using hWZ,LightReportingTerminalPreparation.time,ReportingHostTerminalBatch.time
  light_set (LightReportingTerminalPreparation.span W n : ℕ)
    using LightReportingTerminalPreparation.span,LightReportingTerminalPreparation.time,ReportingHostTerminalBatch.time
  light_set (LightReportingTerminalPreparation.leftRaw base W : ℕ)
    using LightReportingTerminalPreparation.leftRaw,LightReportingTerminalPreparation.time,ReportingHostTerminalBatch.time
  light_set (LightReportingTerminalPreparation.rightRaw base W n : ℕ)
    using LightReportingTerminalPreparation.rightRaw,LightReportingTerminalPreparation.second,LightReportingTerminalPreparation.span,
      LightReportingTerminalPreparation.time,ReportingHostTerminalBatch.time
  light_set (LightReportingTerminalPreparation.leftFlags base W n : ℕ)
    using LightReportingTerminalPreparation.leftFlags,LightReportingTerminalPreparation.time,ReportingHostTerminalBatch.time
  light_set (LightReportingTerminalPreparation.rightFlags base W n : ℕ)
    using LightReportingTerminalPreparation.rightFlags,LightReportingTerminalPreparation.second,LightReportingTerminalPreparation.span,
      LightReportingTerminalPreparation.time,ReportingHostTerminalBatch.time
  have hbatch := LightReportingLeafBatch.program_meets (μ := ν₁) (d := d+1)
    (srcL := srcL) (srcR := srcR) (rawL := LightReportingTerminalPreparation.leftRaw base W)
    (rawR := LightReportingTerminalPreparation.rightRaw base W n)
    (flagsL := LightReportingTerminalPreparation.leftFlags base W n)
    (flagsR := LightReportingTerminalPreparation.rightFlags base W n) (n := n) (work := work)
    av (ReportingHostTerminalBatch.endpointsLeft q k pre) (ReportingHostTerminalBatch.endpointsRight q k pre) left right
    (fun i => key p (modulus h J) 0 (left i)) (fun i => key p (modulus h J) shift (right i))
    (ReportingHostTerminalBatch.flagsLeft q k pre) (ReportingHostTerminalBatch.flagsRight q k pre)
    HL₁ HR₁ hw (by omega) (modulus_pos h J)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by unfold LightReportingTerminalPreparation.leftRaw; omega)
    (by unfold LightReportingTerminalPreparation.rightRaw LightReportingTerminalPreparation.second LightReportingTerminalPreparation.span; omega)
    (by unfold LightReportingTerminalPreparation.leftFlags; omega)
    (by unfold LightReportingTerminalPreparation.rightFlags LightReportingTerminalPreparation.second LightReportingTerminalPreparation.span; omega)
    hsBatch hwBatch hkeyL hkeyR
    (fun i _ => by unfold ReportingHostTerminalBatch.flagsLeft ReportingHostBlockBucketTest.leftFlag; split <;> omega)
    (fun i _ => by unfold ReportingHostTerminalBatch.flagsRight ReportingHostBlockBucketTest.rightFlag; split <;> omega)
    (fun i hi => (hkeep _ (by omega)).trans (hreadL i hi))
    (fun j hj => (hkeep _ (by omega)).trans (hreadR j hj))
    hrawL hrawR hflagL hflagR hvaluesL hvaluesR ha htarget
    (fun i _ => endpointLeft_abs_le (outputOccurrences q) (leftAt q k pre i))
    (fun i _ => endpointRight_abs_le (outputOccurrences q) (rightAt q k pre i)) hcountWord
  have hrun := (ReportingHostRelocation.meets hbatch LightReportingTerminalPreparation.program).append [body 17 24]
  change Meets lim program 24 (d+1) _ ν₁
    (ReportingHostTerminalBatch.time p shift left right NL NR q k pre) _ at hrun
  light_call hrun using LightReportingTerminalPreparation.time,ReportingHostTerminalBatch.time
    with found ν₂ ⟨hbool,hhit,hkeepBatch⟩
  exact ⟨hbool,hhit,fun i hi => (hkeepBatch i (by omega)).trans (hkeep i hi)⟩

end ThreeSum.LightReportingTerminalPrepared
