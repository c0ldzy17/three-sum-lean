import Submission.ThreeSum.LightReportingTerminalPrepared
import Submission.ThreeSum.LightReportingBinomial

/-!
# Complete single-prefix terminal program

The terminal host computes its balanced candidate count with Pascal,
enumerates both full endpoint mask arrays, constructs their exact endpoint
and independent trimming data, and tests their retained original buckets.
No candidate count, endpoint array, or trimming flag is supplied by an oracle.
-/

namespace ThreeSum.LightReportingTerminal

open Light Finset BlockRows BlockIndex BlockEncoding BlockCoefficientRows
open GlobalEncoding LocalCoverBounds BlockSourceEncoding LightSourceResidues SourceBuckets
open BlockIndexedQuery BlockForced StoredReporting LightBlockQuery
open LightReportingTerminalMasks LightBlockSourceBuild

set_option maxHeartbeats 3800000
set_option maxRecDepth 14000

def body (pCount pMasks pPrepared : ℕ) : Stmt :=
  .set 31 (v 10 *' v 11) ;;
  .set 32 ((v 10 -' v 20) *' (k 2 *' v 12)) ;;
  .set 33 ((v 10 -' v 20) *' v 12) ;;
  .call pCount [v 32,v 33,v 30] 34 ;;
  .call pMasks [v 31,v 33,v 21,v 22,v 23,v 21,v 24,v 25,v 26,v 30] 35 ;;
  .call pPrepared [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,v 17,v 18,v 19,
    v 25,v 26,v 34,v 27,v 28,v 29,v 30] 0

def initialLibraries : Program := ReportingHostRelocation.program
  LightReportingTerminalMasks.program LightReportingBinomial.program
def libraries : Program := ReportingHostRelocation.program
  initialLibraries LightReportingTerminalPrepared.program
def program : Program := libraries ++ [body 11 0 37]

def space (work h J : ℕ) : ℕ :=
  max (LightReportingTerminalPrepared.space work h J)
    (max (work+LightPascal.tableSize (J*(512*h))) (work+2*(J*(512*h))+2))
def word (h J : ℕ) : ℕ := LightReportingTerminalPrepared.word h J+2^(J*(512*h)+1)
def time {h J : ℕ} (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (512*h)))) : ℕ :=
  LightReportingBinomial.time ((J-k)*(2*h))+LightReportingTerminalMasks.time h J k+
    LightReportingTerminalPrepared.time p shift left right NL NR q k pre+800

variable {lim : Limits}

theorem program_meets {μ : ℕ→ℤ}
    {h J k srcL srcR offsetsL offsetsR flatL flatR NL NR occ maps candidates histL histR masks masksL masksR base bitBase rowOut work d : ℕ}
    (av : ℤ) (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ)
    (q : GlobalOutput h J) (pre : List (Finset (Fin (512*h)))) (hk : k≤J)
    (HL : Stored μ (fun i => key p (modulus h J) 0 (left i)) NL (modulus h J) offsetsL flatL)
    (HR : Stored μ (fun i => key p (modulus h J) shift (right i)) NR (modulus h J) offsetsR flatR)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+count h J k+J*(512*h)+9≤lim.depth)
    (hsrcL : srcL+NL≤masks) (hsrcR : srcR+NR≤masks)
    (hoffsetsL : offsetsL+modulus h J+1≤masks) (hoffsetsR : offsetsR+modulus h J+1≤masks)
    (hflatL : flatL+NL≤masks) (hflatR : flatR+NR≤masks)
    (hocc : occ+J≤masks) (hmaps : maps+2*(512*h)*scheduleSize h≤masks)
    (hcandidates : candidates+scheduleSize h≤masks)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h≤masks)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h≤masks)
    (hmasks : masks+count h J k≤masksL) (hmasksL : masksL+count h J k≤masksR)
    (hmasksR : masksR+count h J k≤base)
    (hstop : LightReportingTerminalPreparation.stop base (J*(512*h)) (count h J k)≤bitBase)
    (hbits : bitBase+J*(512*h)≤rowOut) (hrowOut : rowOut+2≤work)
    (hspace : space work h J≤lim.space) (hword : (word h J : ℤ)≤lim.word)
    (hoccRead : ∀ j<J, μ (occ+j)=(occurrenceIndices (outputOccurrences q) j : ℤ))
    (hcover : BlockSourceCoverInput.Input μ h maps candidates histL histR)
    (hreadL : ∀ i<NL, μ (srcL+i)=left i) (hreadR : ∀ j<NR, μ (srcR+j)=right j)
    (hvaluesL : ∀ i<NL, |left i|≤lim.word) (hvaluesR : ∀ j<NR, |right j|≤lim.word)
    (ha : |av|≤lim.word) (htarget : ∀ i<NL, |av+left i|≤lim.word)
    (hcountWord : ((NL*NR : ℕ) : ℤ)≤lim.word) :
    Meets lim program 38 d
      [av,srcL,srcR,offsetsL,flatL,offsetsR,flatR,NL,NR,modulus h J,J,512*h,h,localPrime h,localBucketCap h,
        occ,maps,candidates,histL,histR,k,SubsetAddress.subsetMask (querySet k (outputRows q)),
        SubsetAddress.subsetMask (leftPrefix k (prefixRows (J := J) pre)),
        SubsetAddress.subsetMask (rightPrefix k (outputRows q) (prefixRows (J := J) pre)),
        masks,masksL,masksR,base,bitBase,rowOut,work]
      μ (time p shift left right NL NR q k pre)
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ ReportingHostTerminalBatch.Hit av p shift left right NL NR q k pre) ∧ Kept μ ν masks) := by
  let W := J*(512*h)
  let residual := (J-k)*(2*h)
  let half := (J-k)*h
  let n := count h J k
  have hres : residual≤W := Nat.mul_le_mul (Nat.sub_le J k) (by omega)
  have hhalf : half≤residual := Nat.mul_le_mul_left (J-k) (by omega)
  have hstop' : base+2*(2*W+4*n+2)≤bitBase := hstop
  have hsPrepared : LightReportingTerminalPrepared.space work h J≤lim.space :=
    (le_max_left _ _).trans hspace
  have hsOther := (le_max_right _ _).trans hspace
  have hsPascal : work+LightPascal.tableSize W≤lim.space := (le_max_left _ _).trans hsOther
  have hsMasks : work+(2*W+2)≤lim.space := by
    have hh := (le_max_right _ _).trans hsOther
    omega
  have hwPrepared : (LightReportingTerminalPrepared.word h J : ℤ)≤lim.word := by
    have hh : LightReportingTerminalPrepared.word h J≤word h J := Nat.le_add_right _ _
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwMasks : ((2^(W+1) : ℕ) : ℤ)≤lim.word := by
    have hh : 2^(W+1)≤word h J := Nat.le_add_left _ _
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwPascal : ((2^(residual+1) : ℕ) : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) (by omega))).trans hwMasks
  have hsCount : work+LightPascal.tableSize residual≤lim.space := by
    have hh : LightPascal.tableSize residual≤LightPascal.tableSize W := by
      unfold LightPascal.tableSize
      exact Nat.pow_le_pow_left (show residual+1≤W+1 by omega) 2
    omega
  have hWZ : (J : ℤ)*(512*(h : ℤ))=(W : ℤ) := by simp [W]
  have hresZ : ((J : ℤ)-(k : ℤ))*(2*(h : ℤ))=(residual : ℤ) := by
    simp only [residual,Nat.cast_mul,Nat.cast_sub hk,Nat.cast_ofNat]
  have hhalfZ : ((J : ℤ)-(k : ℤ))*(h : ℤ)=(half : ℤ) := by
    simp only [half,Nat.cast_mul,Nat.cast_sub hk]
  have hkeyL : ∀ i<NL, key p (modulus h J) 0 (left i)<modulus h J :=
    fun i _ => key_lt (modulus_pos h J) 0 (left i)
  have hkeyR : ∀ i<NR, key p (modulus h J) shift (right i)<modulus h J :=
    fun i _ => key_lt (modulus_pos h J) shift (right i)
  have hschedule : 0<scheduleSize h := by
    unfold scheduleSize LocalHashMoments.scheduleLength
    positivity
  have hmapSize := Nat.le_mul_of_pos_right (2*(512*h)) hschedule
  have hlocalSpace : 512*h≤lim.space := by omega
  apply Meets.of_body (p := 38) (by rfl : program[38]?=some (body 11 0 37))
  unfold body time
  light_set (W : ℕ) using hWZ,LightReportingBinomial.time,LightReportingTerminalMasks.time,LightReportingTerminalPrepared.time
  light_set (residual : ℕ) using hresZ,LightReportingBinomial.time,LightReportingTerminalMasks.time,LightReportingTerminalPrepared.time
  light_set (half : ℕ) using hhalfZ,LightReportingBinomial.time,LightReportingTerminalMasks.time,LightReportingTerminalPrepared.time
  have hbin := LightReportingBinomial.program_meets (d := d+1) (μ := μ) hhalf hw hsCount hwPascal (by omega)
  have hbinRun := (ReportingHostRelocation.meets hbin LightReportingTerminalMasks.program).append
    (LightReportingTerminalPrepared.program.map (ReportingHostRelocation.relocate 12) ++ [body 11 0 37])
  change Meets lim program 11 (d+1) _ μ (LightReportingBinomial.time ((J-k)*(2*h))) _ at hbinRun
  light_call hbinRun using LightReportingBinomial.time,LightReportingTerminalMasks.time,LightReportingTerminalPrepared.time
    with countRet ν₁ ⟨hcount,hkeepCount⟩
  change countRet=(n : ℤ) at hcount
  have hcountKeep : Kept μ ν₁ masks := fun i hi => hkeepCount i (Or.inl (by omega))
  have hmaskRun := (LightReportingTerminalMasks.program_meets (d := d+1) (μ := ν₁)
    (masks := masks) (dstL := masksL) (dstR := masksR) (work := work) q pre hk hw
    hmasks hmasksL (by omega) hsMasks hwMasks (by omega)).append
      (LightReportingBinomial.program.map (ReportingHostRelocation.relocate 7) ++
        LightReportingTerminalPrepared.program.map (ReportingHostRelocation.relocate 12) ++ [body 11 0 37])
  change Meets lim program 0 (d+1) _ ν₁ (LightReportingTerminalMasks.time h J k) _ at hmaskRun
  light_call hmaskRun using LightReportingBinomial.time,LightReportingTerminalMasks.time,LightReportingTerminalPrepared.time
    with unused ν₂ ⟨_,hmL,hmR,hkeepMasks⟩
  have hkeep : Kept μ ν₂ masks := fun i hi => (hkeepMasks i hi).trans (hcountKeep i hi)
  have HL₂ := LightReportingLeaf.stored_of_kept HL hkeyL hoffsetsL hflatL hkeep
  have HR₂ := LightReportingLeaf.stored_of_kept HR hkeyR hoffsetsR hflatR hkeep
  have hcover₂ := hcover.of_kept hkeep hmaps hcandidates hleft hright
  have hocc₂ : ∀ j<J, ν₂ (occ+j)=(occurrenceIndices (outputOccurrences q) j : ℤ) :=
    fun j hj => (hkeep _ (by omega)).trans (hoccRead j hj)
  have hprep := LightReportingTerminalPrepared.program_meets (d := d+1) (μ := ν₂)
    (srcL := srcL) (srcR := srcR) (occ := occ) (maps := maps) (candidates := candidates) (histL := histL) (histR := histR)
    (masksL := masksL) (masksR := masksR) (base := base) (bitBase := bitBase) (rowOut := rowOut) (work := work)
    av p shift left right q pre HL₂ HR₂ hw (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hmasksR hstop hbits hrowOut
    hsPrepared hwPrepared hocc₂ hcover₂ hmL hmR
    (fun i hi => (hkeep _ (by omega)).trans (hreadL i hi))
    (fun j hj => (hkeep _ (by omega)).trans (hreadR j hj)) hvaluesL hvaluesR ha htarget hcountWord
  have hprepRun := (ReportingHostRelocation.meets hprep initialLibraries).append [body 11 0 37]
  change Meets lim program 37 (d+1) _ ν₂
    (LightReportingTerminalPrepared.time p shift left right NL NR q k pre) _ at hprepRun
  light_call hprepRun using hcount,LightReportingBinomial.time,LightReportingTerminalMasks.time,LightReportingTerminalPrepared.time
    with found ν₃ ⟨hbool,hhit,hkeepPrep⟩
  exact ⟨hbool,hhit,fun i hi => (hkeepPrep i (by omega)).trans (hkeep i hi)⟩

end ThreeSum.LightReportingTerminal
