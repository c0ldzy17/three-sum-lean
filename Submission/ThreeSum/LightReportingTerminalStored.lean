import Submission.ThreeSum.LightReportingTerminalFrontier
import Submission.ThreeSum.ReportingHostFrontierLayout

/-!
# Terminal scanning from the actual frontier header

This adapter reads the capacity produced by root initialization and the
terminal level's retained count, query mask, and two prefix-array pointers.
It then executes the complete terminal scan in the unchanged frontier order.
-/

namespace ThreeSum.LightReportingTerminalStored

open Light Finset BlockRows BlockIndex BlockEncoding BlockCoefficientRows
open GlobalEncoding LocalCoverBounds BlockSourceEncoding LightSourceResidues SourceBuckets
open BlockIndexedQuery BlockForced StoredReporting LightBlockQuery
open LightReportingTerminalMasks LightBlockSourceBuild ReportingHostTerminalFrontier
open RawIncidences RawReporting ReportingHostFrontierLayout

set_option maxHeartbeats 3800000
set_option maxRecDepth 14000
set_option linter.unusedSectionVars false

/-- The 20 original-source/encoding controls, depth and root pointer, then
the seven terminal scratch pointers. All frontier metadata is loaded. -/
def body (pScan : ℕ) : Stmt :=
  .set 29 (M (v 21 +' k 3)) ;;
  .set 30 (v 21 +' v 20 *' (k 4 +' k 2 *' v 29)) ;;
  .set 31 (M (v 30)) ;;
  .set 32 (M (v 30 +' k 1)) ;;
  .set 33 (v 30 +' k 4) ;;
  .set 34 (v 33 +' v 29) ;;
  .call pScan [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,v 17,v 18,v 19,
    v 20,v 32,v 33,v 34,v 22,v 23,v 24,v 25,v 26,v 27,v 28,v 31] 0

def program : Program := LightReportingTerminalFrontier.program ++ [body 39]

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def time {h J : ℕ} (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) (k : ℕ) : ℕ :=
  ReportingHostTerminalFrontier.time p shift left right NL NR w.2.2 k
    (ReportingHostFrontier.frontier I w k) (ReportingHostFrontier.frontier I w k).length+600

theorem program_meets {μ : ℕ→ℤ}
    {h J k srcL srcR offsetsL offsetsR flatL flatR NL NR occ maps candidates histL histR root
      masks masksL masksR base bitBase rowOut work d : ℕ}
    (av : ℤ) (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ)
    (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) (hk : k≤J)
    (HF : At μ I w root (capacity I w) k) (hcap : μ (root+3)=(capacity I w : ℤ))
    (HL : Stored μ (fun i => key p (modulus h J) 0 (left i)) NL (modulus h J) offsetsL flatL)
    (HR : Stored μ (fun i => key p (modulus h J) shift (right i)) NR (modulus h J) offsetsR flatR)
    (hw : (lim.space : ℤ)≤lim.word)
    (hd : d+(ReportingHostFrontier.frontier I w k).length+count h J k+J*(512*h)+11≤lim.depth)
    (hsrcL : srcL+NL≤masks) (hsrcR : srcR+NR≤masks)
    (hoffsetsL : offsetsL+modulus h J+1≤masks) (hoffsetsR : offsetsR+modulus h J+1≤masks)
    (hflatL : flatL+NL≤masks) (hflatR : flatR+NR≤masks)
    (hocc : occ+J≤masks) (hmaps : maps+2*(512*h)*scheduleSize h≤masks)
    (hcandidates : candidates+scheduleSize h≤masks)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h≤masks)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h≤masks)
    (hslot : slot root (capacity I w) (k+1)≤masks)
    (hmasks : masks+count h J k≤masksL) (hmasksL : masksL+count h J k≤masksR)
    (hmasksR : masksR+count h J k≤base)
    (hstop : LightReportingTerminalPreparation.stop base (J*(512*h)) (count h J k)≤bitBase)
    (hbits : bitBase+J*(512*h)≤rowOut) (hrowOut : rowOut+2≤work)
    (hspace : LightReportingTerminal.space work h J≤lim.space)
    (hword : (LightReportingTerminal.word h J : ℤ)≤lim.word)
    (hoccRead : ∀ j<J, μ (occ+j)=(occurrenceIndices (outputOccurrences w.2.2) j : ℤ))
    (hcover : BlockSourceCoverInput.Input μ h maps candidates histL histR)
    (hreadL : ∀ i<NL, μ (srcL+i)=left i) (hreadR : ∀ j<NR, μ (srcR+j)=right j)
    (hvaluesL : ∀ i<NL, |left i|≤lim.word) (hvaluesR : ∀ j<NR, |right j|≤lim.word)
    (ha : |av|≤lim.word) (htarget : ∀ i<NL, |av+left i|≤lim.word)
    (hcountWord : ((NL*NR : ℕ) : ℤ)≤lim.word) :
    Meets lim program 40 d
      [av,srcL,srcR,offsetsL,flatL,offsetsR,flatR,NL,NR,modulus h J,J,512*h,h,localPrime h,localBucketCap h,
        occ,maps,candidates,histL,histR,k,root,masks,masksL,masksR,base,bitBase,rowOut,work]
      μ (time p shift left right NL NR I w k)
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ ∃ pre∈ReportingHostFrontier.frontier I w k,
          ReportingHostTerminalBatch.Hit av p shift left right NL NR w.2.2 k pre) ∧ Kept μ ν masks) := by
  let cap := capacity I w
  let pres := ReportingHostFrontier.frontier I w k
  have hscanDepth : d+1+pres.length+count h J k+J*(512*h)+10≤lim.depth := by
    dsimp only [pres]
    omega
  have hn : pres.length≤cap := frontier_capacity I w hk
  have hsOther := (le_max_right _ _).trans hspace
  have hsWork : work≤lim.space := by have hh := (le_max_right _ _).trans hsOther; omega
  have hstop' : base+2*(2*(J*(512*h))+4*count h J k+2)≤bitBase := hstop
  have hmaskSpace : masks≤lim.space := by omega
  have hslot' : slot root cap k+4+2*cap≤masks := by simpa only [slot_succ] using hslot
  have hroot : root≤slot root cap k := Nat.le_add_right _ _
  have hleftEnd : ReportingHostFrontierLayout.left root cap k+pres.length≤masks := by
    unfold ReportingHostFrontierLayout.left
    omega
  have hrightEnd : ReportingHostFrontierLayout.right root cap k+pres.length≤masks := by
    unfold ReportingHostFrontierLayout.right ReportingHostFrontierLayout.left
    omega
  have hreadInL (i : ℕ) (hi : i<pres.length) :
      μ (ReportingHostFrontierLayout.left root cap k+i)=
        (SubsetAddress.subsetMask (leftPrefix k (prefixRows (J := J) (prefixAt pres i))) : ℤ) := by
    have hh := HF.left.getElem (i := i) (by simpa only [leftMasks_length] using hi)
    simpa only [leftMasks,List.getElem_map,prefixAt_eq_get pres hi] using hh
  have hreadInR (i : ℕ) (hi : i<pres.length) :
      μ (ReportingHostFrontierLayout.right root cap k+i)=
        (SubsetAddress.subsetMask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) (prefixAt pres i))) : ℤ) := by
    have hh := HF.right.getElem (i := i) (by simpa only [rightMasks_length] using hi)
    simpa only [rightMasks,List.getElem_map,prefixAt_eq_get pres hi] using hh
  have hQword : |(SubsetAddress.subsetMask (querySet k (outputRows w.2.2)) : ℤ)|≤lim.word := by
    rw [Int.abs_natCast]
    have hpWord : ((2^(J*(512*h)+1) : ℕ) : ℤ)≤lim.word :=
      (Int.ofNat_le.mpr (Nat.le_add_left _ _)).trans hword
    exact (Int.ofNat_le.mpr ((SubsetAddress.subsetMask_isMask _).1.le.trans
      (Nat.pow_le_pow_right (by decide) (by omega)))).trans hpWord
  have hQbounds := abs_le.mp hQword
  have hslotZ : (root : ℤ)+(k : ℤ)*(4+2*(cap : ℤ))=(slot root cap k : ℤ) := by
    simp only [slot,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  have hcount : μ (slot root cap k)=(pres.length : ℤ) := HF.count
  have hquery : μ (slot root cap k+1)=
      (SubsetAddress.subsetMask (querySet k (outputRows w.2.2)) : ℤ) := HF.query
  have hcapZ : μ (((root : ℤ)+3).toNat)=(cap : ℤ) := by
    rw [show ((root : ℤ)+3).toNat=root+3 by omega]
    exact hcap
  apply Meets.of_body (p := 40) (by rfl : program[40]?=some (body 39))
  unfold body time
  light_set (cap : ℕ) using hcap,hcapZ
  light_set (slot root cap k : ℕ) using hslotZ
  light_set (pres.length : ℕ) using hcount
  light_set (SubsetAddress.subsetMask (querySet k (outputRows w.2.2)) : ℕ) using hquery
  light_set (ReportingHostFrontierLayout.left root cap k : ℕ) using ReportingHostFrontierLayout.left
  light_set (ReportingHostFrontierLayout.right root cap k : ℕ)
    using ReportingHostFrontierLayout.left,ReportingHostFrontierLayout.right
  have hrun := (LightReportingTerminalFrontier.program_meets (μ := μ) (d := d+1)
    (srcL := srcL) (srcR := srcR) (occ := occ) (maps := maps) (candidates := candidates)
    (histL := histL) (histR := histR) (inL := ReportingHostFrontierLayout.left root cap k)
    (inR := ReportingHostFrontierLayout.right root cap k) (masks := masks) (masksL := masksL) (masksR := masksR)
    (base := base) (bitBase := bitBase) (rowOut := rowOut) (work := work)
    av p shift left right w.2.2 pres hk le_rfl HL HR hw hscanDepth
    hsrcL hsrcR hoffsetsL hoffsetsR hflatL hflatR hocc hmaps hcandidates hleft hright hleftEnd hrightEnd
    hmasks hmasksL hmasksR hstop hbits hrowOut hspace hword hoccRead hcover hreadL hreadR hreadInL hreadInR
    hvaluesL hvaluesR ha htarget hcountWord).append [body 39]
  change Meets lim program 39 (d+1) _ μ
    (ReportingHostTerminalFrontier.time p shift left right NL NR w.2.2 k
      (ReportingHostFrontier.frontier I w k) (ReportingHostFrontier.frontier I w k).length) _ at hrun
  light_call hrun with found ν ⟨hbool,hhit,hkeep⟩
  exact ⟨hbool,hhit.trans (hit_all av p shift left right NL NR w.2.2 k pres),hkeep⟩

end ThreeSum.LightReportingTerminalStored
