import Submission.ThreeSum.LightReportingLevels
import Submission.ThreeSum.LightReportingTerminalStored

/-!
# Executed partial-depth traversal followed by terminal reporting

This is the expensive branch of a wanted-record query. Its caller executes
the cumulative root-mass guard first. Catalogs and sources remain persistent;
the branch walks the prescribed levels, reads the retained terminal slot,
and tests its exact original physical bucket products.
-/

namespace ThreeSum.LightReportingWantedSearch

open Light Finset BlockRows BlockIndex BlockMaskLayout BlockEncoding BlockCoefficientRows
open GlobalEncoding LocalCoverBounds BlockSourceEncoding LightSourceResidues
open BlockIndexedQuery BlockForced StoredReporting LightBlockQuery
open LightReportingTerminalMasks LightBlockSourceBuild ReportingHostLevelData ReportingHostFrontierLayout
open RawIncidences RawReporting

set_option maxHeartbeats 4400000
set_option maxRecDepth 16000
set_option linter.unusedSectionVars false

/-- Original terminal controls (20), requested depth and root, the shared
catalog/packed-row/source pointers, level scratch, group and cut, terminal
scratch, and work. -/
def body (pLevels pTerminal : ℕ) : Stmt :=
  .set 41 (v 10 *' v 11) ;;
  .call pLevels [v 41,v 12,v 10,v 20,v 24,v 25,v 22,v 23,v 21,v 26,v 27,v 28,v 29,v 30,v 31,v 32,v 33,v 34,v 11] 42 ;;
  .call pTerminal [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,v 17,v 18,v 19,
    v 20,v 21,v 35,v 36,v 37,v 38,v 39,v 40,v 32] 0

def libraries : Program := ReportingHostRelocation.program
  LightReportingLevels.program LightReportingTerminalStored.program
def program : Program := libraries ++ [body 52 93]

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def time {h J : ℕ} (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) (D : ℕ→Catalog) (K : ℕ) : ℕ :=
  LightReportingLevels.time I w D K+LightReportingTerminalStored.time p shift left right NL NR I w K+500

theorem program_meets {μ : ℕ→ℤ}
    {h J K srcL srcR offsetsL offsetsR flatL flatR NL NR occ maps candidates histL histR root catalogs rows
      baseL baseR masks childL childR counts selected maskBase work terminalMasks masksL masksR base bitBase rowOut d : ℕ}
    (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (w : Wanted h J α) (D : ℕ→Catalog) (hK : K≤J)
    (hkey : w.1∈A ∧ globalModulus h J ∣ (a w.1%(p : ℤ)+lift w.2.1*(p : ℤ)+shift)-globalKey w.2.2)
    (hw : (lim.space : ℤ)≤lim.word)
    (HS : Sources μ (p : ℤ) shift B C b c w.2.2 baseL baseR)
    (HC : ∀ (j : ℕ) (hj : j≤K), Stored μ (D j) (hj.trans hK) (p : ℤ) shift B C b c w.2.2)
    (HB : ∀ j≤K, Bounds h J j (D j) baseL baseR root)
    (HW : ∀ j≤K, Scratch lim h J j (D j) B.card C.card maskBase work)
    (hmeta : ∀ j≤K, SegN μ (catalogs+5*j) ((D j).record h j))
    (hmetaEnd : catalogs+5*(K+1)≤root) (hrows : rows+J≤root)
    (hrow : ∀ (j : ℕ) (hj : j<J), μ (rows+j)=(rowMask (outputRows w.2.2) ⟨j,hj⟩ : ℤ))
    (hcap : μ (root+3)=(capacity (rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w : ℤ))
    (HA : At μ (rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w root
      (capacity (rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w) 0)
    (hout : slot root (capacity (rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w) (K+1)≤masks)
    (hmasks : masks+groupSize h≤childL) (hchildL : childL+groupSize h≤childR)
    (hchildR : childR+groupSize h≤counts) (hcounts : counts+groupSize h≤selected)
    (hselected : selected+groupSize h≤maskBase)
    (hparams : J+512*h+groupSize h+sourceCut h J≤lim.space)
    (HL : SourceBuckets.Stored μ (fun i => key p (modulus h J) 0 (left i)) NL (modulus h J) offsetsL flatL)
    (HR : SourceBuckets.Stored μ (fun i => key p (modulus h J) shift (right i)) NR (modulus h J) offsetsR flatR)
    (hsrcL : srcL+NL≤root) (hsrcR : srcR+NR≤root)
    (hoffsetsL : offsetsL+modulus h J+1≤root) (hoffsetsR : offsetsR+modulus h J+1≤root)
    (hflatL : flatL+NL≤root) (hflatR : flatR+NR≤root)
    (hocc : occ+J≤root) (hmaps : maps+2*(512*h)*scheduleSize h≤root)
    (hcandidates : candidates+scheduleSize h≤root)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h≤root)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h≤root)
    (hterminalSlot : slot root (capacity (rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w) (K+1)≤terminalMasks)
    (hterminalMasks : terminalMasks+count h J K≤masksL) (hmasksL : masksL+count h J K≤masksR)
    (hmasksR : masksR+count h J K≤base)
    (hstop : LightReportingTerminalPreparation.stop base (J*(512*h)) (count h J K)≤bitBase)
    (hbits : bitBase+J*(512*h)≤rowOut) (hrowOut : rowOut+2≤work)
    (hspace : LightReportingTerminal.space work h J≤lim.space)
    (hword : (LightReportingTerminal.word h J : ℤ)≤lim.word)
    (hoccRead : ∀ j<J, μ (occ+j)=(occurrenceIndices (outputOccurrences w.2.2) j : ℤ))
    (hcover : BlockSourceCoverInput.Input μ h maps candidates histL histR)
    (hreadL : ∀ i<NL, μ (srcL+i)=left i) (hreadR : ∀ j<NR, μ (srcR+j)=right j)
    (hvaluesL : ∀ i<NL, |left i|≤lim.word) (hvaluesR : ∀ j<NR, |right j|≤lim.word)
    (ha : |a w.1|≤lim.word) (htarget : ∀ i<NL, |a w.1+left i|≤lim.word)
    (hcountWord : ((NL*NR : ℕ) : ℤ)≤lim.word)
    (hd : d+K+2*width h J+
      (ReportingHostFrontier.frontier (rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w K).length+
      count h J K+25≤lim.depth) :
    Meets lim program 94 d
      [a w.1,srcL,srcR,offsetsL,flatL,offsetsR,flatR,NL,NR,modulus h J,J,512*h,h,localPrime h,localBucketCap h,
        occ,maps,candidates,histL,histR,K,root,catalogs,rows,baseL,baseR,masks,childL,childR,counts,selected,
        maskBase,work,groupSize h,sourceCut h J,terminalMasks,masksL,masksR,base,bitBase,rowOut]
      μ (time p shift left right NL NR (rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w D K)
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ ∃ pre∈ReportingHostFrontier.frontier (rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w K,
          ReportingHostTerminalBatch.Hit (a w.1) p shift left right NL NR w.2.2 K pre) ∧ Kept μ ν root) := by
  let I := rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
  let W := width h J
  have hterminalDepth : d+1+(ReportingHostFrontier.frontier I w K).length+count h J K+J*(512*h)+11≤lim.depth := by
    dsimp only [I]
    simp only [width] at hd
    omega
  have hrootTerminal : root≤terminalMasks :=
    (show root≤slot root (capacity I w) (K+1) from Nat.le_add_right _ _).trans hterminalSlot
  have hwidth : width h J≤lim.space := by have hh:=(HW 0 (by omega)).space; omega
  have hWZ : (J : ℤ)*(512*(h : ℤ))=(W : ℤ) := by simp [W,width]
  have hkeyL : ∀ i<NL, key p (modulus h J) 0 (left i)<modulus h J :=
    fun i _ => key_lt (modulus_pos h J) 0 (left i)
  have hkeyR : ∀ i<NR, key p (modulus h J) shift (right i)<modulus h J :=
    fun i _ => key_lt (modulus_pos h J) shift (right i)
  apply Meets.of_body (p := 94) (by rfl : program[94]?=some (body 52 93))
  unfold body time
  light_set (W : ℕ) using hWZ
  have hlevels := (LightReportingLevels.program_meets (depth := d+1) D le_rfl hK (p : ℤ) shift A B C a b c w
    hkey hw HS HC HB HW hmeta hmetaEnd hrows hrow hcap HA hout hmasks hchildL hchildR hcounts hselected hparams (by omega)).append
      (LightReportingTerminalStored.program.map (ReportingHostRelocation.relocate 53) ++ [body 52 93])
  change Meets lim program 52 (d+1) _ μ
    (LightReportingLevels.time (rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w D K) _ at hlevels
  light_call hlevels with unused ν ⟨_,hfrontier,hcapν,hkeep⟩
  have HLν := LightReportingLeaf.stored_of_kept HL hkeyL hoffsetsL hflatL hkeep
  have HRν := LightReportingLeaf.stored_of_kept HR hkeyR hoffsetsR hflatR hkeep
  have hcoverν := hcover.of_kept hkeep hmaps hcandidates hleft hright
  have hterminal := LightReportingTerminalStored.program_meets (μ := ν) (d := d+1)
    (srcL := srcL) (srcR := srcR) (occ := occ) (maps := maps) (candidates := candidates)
    (histL := histL) (histR := histR) (root := root) (masks := terminalMasks) (masksL := masksL) (masksR := masksR)
    (base := base) (bitBase := bitBase) (rowOut := rowOut) (work := work)
    (a w.1) p shift left right I w hK (hfrontier K le_rfl) hcapν HLν HRν hw hterminalDepth
    (hsrcL.trans hrootTerminal) (hsrcR.trans hrootTerminal)
    (hoffsetsL.trans hrootTerminal) (hoffsetsR.trans hrootTerminal)
    (hflatL.trans hrootTerminal) (hflatR.trans hrootTerminal)
    (hocc.trans hrootTerminal) (hmaps.trans hrootTerminal) (hcandidates.trans hrootTerminal)
    (hleft.trans hrootTerminal) (hright.trans hrootTerminal)
    hterminalSlot hterminalMasks hmasksL hmasksR hstop hbits hrowOut hspace hword
    (fun j hj => (hkeep _ (by omega)).trans (hoccRead j hj)) hcoverν
    (fun i hi => (hkeep _ (by omega)).trans (hreadL i hi))
    (fun j hj => (hkeep _ (by omega)).trans (hreadR j hj)) hvaluesL hvaluesR ha htarget hcountWord
  have hterminalRun := (ReportingHostRelocation.meets hterminal LightReportingLevels.program).append [body 52 93]
  change Meets lim program 93 (d+1) _ ν
    (LightReportingTerminalStored.time p shift left right NL NR
      (rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w K) _ at hterminalRun
  light_call hterminalRun with found ν₂ ⟨hbool,hhit,hkeepTerminal⟩
  exact ⟨hbool,hhit,fun i hi => (hkeepTerminal i (hi.trans_le hrootTerminal)).trans (hkeep i hi)⟩

end ThreeSum.LightReportingWantedSearch
