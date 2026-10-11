import Submission.ThreeSum.LightReportingWantedInitializeSeparated
import Submission.ThreeSum.LightReportingWantedSearch

/-!
# Complete guarded reporting for one actual wanted record

Decoded query masks are packed, the root mass is queried and added to the
running counter, and the actual comparison controls the expensive branch.
Only a zero guard result executes partial-depth traversal and terminal
original-value testing. Every source and catalog is retained and reused.
-/

namespace ThreeSum.LightReportingWanted

open Light Finset BlockRows BlockIndex BlockMaskLayout BlockEncoding BlockCoefficientRows
open GlobalEncoding LocalCoverBounds BlockSourceEncoding LightSourceResidues
open BlockIndexedQuery BlockForced StoredReporting LightBlockQuery
open LightReportingTerminalMasks LightBlockSourceBuild ReportingHostLevelData ReportingHostFrontierLayout
open RawIncidences RawReporting

set_option maxHeartbeats 5000000
set_option maxRecDepth 18000
set_option linter.unusedSectionVars false

/-- The search controls, with a zero placeholder for the group count, then
decoded raw Q rows, retained cover, and the dense counter/header. -/
def body (pInit pSearch : ℕ) : Stmt :=
  .set 44 (v 10 *' v 11) ;;
  .set 33 (M (v 42 +' k 3)) ;;
  .call pInit [v 44,v 34,v 10,v 11,v 24,v 25,v 22,v 41,v 23,v 42,v 43,v 21,v 31,v 32] 45 ;;
  .ite (k 0 <' v 45)
    (.set 0 (k 1))
    (.call pSearch [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,v 17,v 18,v 19,
      v 20,v 21,v 22,v 23,v 24,v 25,v 26,v 27,v 28,v 29,v 30,v 31,v 32,v 33,v 34,v 35,v 36,v 37,v 38,v 39,v 40] 0)

def libraries : Program := ReportingHostRelocation.program
  LightReportingWantedInitialize.program LightReportingWantedSearch.program
def program : Program := libraries ++ [body 41 136]

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def time {h J : ℕ} (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR old threshold : ℕ)
    (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) (D : ℕ→Catalog) (K : ℕ) : ℕ :=
  LightReportingWantedInitialize.time h J (D 0).t+
    (if threshold<old+rootMass I w then 0 else LightReportingWantedSearch.time p shift left right NL NR I w D K)+700

theorem program_meets {μ : ℕ→ℤ}
    {h J K srcL srcR offsetsL offsetsR flatL flatR NL NR occ maps candidates histL histR root catalogs rawRows rows cover counter
      baseL baseR masks childL childR counts selected maskBase work terminalMasks masksL masksR base bitBase rowOut old threshold d : ℕ}
    (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (w : Wanted h J α) (D : ℕ→Catalog) (hK : K≤J)
    (hkey : w.1∈A ∧ globalModulus h J ∣ (a w.1%(p : ℤ)+lift w.2.1*(p : ℤ)+shift)-globalKey w.2.2)
    (hw : (lim.space : ℤ)≤lim.word)
    (HS : Sources μ (p : ℤ) shift B C b c w.2.2 baseL baseR)
    (HC : ∀ (j : ℕ) (hj : j≤K), Stored μ (D j) (hj.trans hK) (p : ℤ) shift B C b c w.2.2)
    (HB : ∀ j≤K, Bounds h J j (D j) baseL baseR counter)
    (HW : ∀ j≤K, Scratch lim h J j (D j) B.card C.card maskBase work)
    (hmeta : ∀ j≤K, SegN μ (catalogs+5*j) ((D j).record h j))
    (hmetaEnd : catalogs+5*(K+1)≤counter)
    (hraw : rawRows+J≤rows) (hrows : rows+J≤root) (hcounter : counter+2≤rawRows)
    (hgroup : μ (cover+3)=(groupSize h : ℤ)) (hcoverEnd : cover+4≤counter)
    (hreadRaw : SegN μ rawRows (rawMasks (outputRows w.2.2)))
    (hcounterRead : μ counter=(old : ℤ)) (hthreshold : μ (counter+1)=(threshold : ℤ))
    (hguardWord : ((old+rootMass (rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w+threshold+2 : ℕ) : ℤ)≤lim.word)
    (hout : slot root (capacity (rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w) (K+1)≤masks)
    (hmasks : masks+groupSize h≤childL) (hchildL : childL+groupSize h≤childR)
    (hchildR : childR+groupSize h≤counts) (hcounts : counts+groupSize h≤selected)
    (hselected : selected+groupSize h≤maskBase)
    (hparams : J+512*h+groupSize h+sourceCut h J≤lim.space)
    (hpackSpace : work+(512*h+1)≤lim.space)
    (HL : SourceBuckets.Stored μ (fun i => key p (modulus h J) 0 (left i)) NL (modulus h J) offsetsL flatL)
    (HR : SourceBuckets.Stored μ (fun i => key p (modulus h J) shift (right i)) NR (modulus h J) offsetsR flatR)
    (hsrcL : srcL+NL≤counter) (hsrcR : srcR+NR≤counter)
    (hoffsetsL : offsetsL+modulus h J+1≤counter) (hoffsetsR : offsetsR+modulus h J+1≤counter)
    (hflatL : flatL+NL≤counter) (hflatR : flatR+NR≤counter)
    (hocc : occ+J≤rows) (hoccApart : Apart counter 1 occ J)
    (hmaps : maps+2*(512*h)*scheduleSize h≤counter)
    (hcandidates : candidates+scheduleSize h≤counter)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h≤counter)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h≤counter)
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
      count h J K+27≤lim.depth) :
    Meets lim program 137 d
      [a w.1,srcL,srcR,offsetsL,flatL,offsetsR,flatR,NL,NR,modulus h J,J,512*h,h,localPrime h,localBucketCap h,
        occ,maps,candidates,histL,histR,K,root,catalogs,rows,baseL,baseR,masks,childL,childR,counts,selected,
        maskBase,work,0,sourceCut h J,terminalMasks,masksL,masksR,base,bitBase,rowOut,rawRows,cover,counter]
      μ (time p shift left right NL NR old threshold (rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w D K)
      (fun r ν =>
        let I := rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
        (r=0 ∨ r=1) ∧
        (r=1 ↔ threshold<old+rootMass I w ∨
          ∃ pre∈ReportingHostFrontier.frontier I w K,
            ReportingHostTerminalBatch.Hit (a w.1) p shift left right NL NR w.2.2 K pre) ∧
        ν counter=((old+rootMass I w : ℕ) : ℤ) ∧ KeptBut μ ν rows counter 1) := by
  let I := rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
  let W := width h J
  have hinitDepth : d+1+2*width h J+16≤lim.depth := by omega
  have hsearchDepth : d+1+K+2*width h J+(ReportingHostFrontier.frontier I w K).length+count h J K+25≤lim.depth := by
    dsimp only [I]
    omega
  change Meets lim program 137 d _ μ (time p shift left right NL NR old threshold I w D K)
    (fun r ν => (r=0 ∨ r=1) ∧
      (r=1 ↔ threshold<old+rootMass I w ∨ ∃ pre∈ReportingHostFrontier.frontier I w K,
        ReportingHostTerminalBatch.Hit (a w.1) p shift left right NL NR w.2.2 K pre) ∧
      ν counter=((old+rootMass I w : ℕ) : ℤ) ∧ KeptBut μ ν rows counter 1)
  have hcounterRoot : counter≤root := by omega
  have hcounterRows : counter≤rows := by omega
  have hwidth : W≤lim.space := by have hh:=(HW 0 (by omega)).space; change width h J≤lim.space; omega
  have hWZ : (J : ℤ)*(512*(h : ℤ))=(W : ℤ) := by simp [W,width]
  have hgroupZ : μ (((cover : ℤ)+3).toNat)=(groupSize h : ℤ) := by
    rw [show ((cover : ℤ)+3).toNat=cover+3 by omega]
    exact hgroup
  have hrootOut : slot root (capacity I w) 1≤maskBase :=
    ((slot_mono (by omega)).trans hout).trans (by omega)
  have hrootMask : root≤maskBase :=
    (show root≤slot root (capacity I w) 1 from Nat.le_add_right _ _).trans hrootOut
  have hmaskWork := (HW 0 (by omega)).masks
  have hmeta0 : SegN μ catalogs ((D 0).record h 0) := by simpa only [Nat.mul_zero,Nat.add_zero] using hmeta 0 (by omega)
  have hkeyL : ∀ i<NL, key p (modulus h J) 0 (left i)<modulus h J :=
    fun i _ => key_lt (modulus_pos h J) 0 (left i)
  have hkeyR : ∀ i<NR, key p (modulus h J) shift (right i)<modulus h J :=
    fun i _ => key_lt (modulus_pos h J) shift (right i)
  apply Meets.of_body (p := 137) (by rfl : program[137]?=some (body 41 136))
  unfold body time
  light_set (W : ℕ) using hWZ,LightReportingWantedInitialize.time
  light_set (groupSize h : ℕ) using hgroup,hgroupZ,LightReportingWantedInitialize.time
  have hinit := (LightReportingWantedInitializeSeparated.program_meets (μ := μ) (d := d+1)
    (baseL := baseL) (baseR := baseR) (catalogs := catalogs) (cover := cover) (rawRows := rawRows)
    (rows := rows) (counter := counter) (root := root) (maskBase := maskBase) (work := work)
    (p : ℤ) shift A B C a b c w hkey hw HS (HC 0 (by omega)) ((HB 0 (by omega)).mono hcounterRows)
    (HW 0 (by omega)) hmeta0 (by omega) hgroup (by omega) hraw hrows hcounter hrootOut hpackSpace hguardWord
    hreadRaw hcounterRead hthreshold hinitDepth).append
      (LightReportingWantedSearch.program.map (ReportingHostRelocation.relocate 42) ++ [body 41 136])
  change Meets lim program 41 (d+1) _ μ (LightReportingWantedInitialize.time h J (D 0).t) _ at hinit
  light_call hinit using LightReportingWantedInitialize.time with guard ν ⟨hguard,hcounterν,hfrontier,_,hcapν,hpacked,hkeep⟩
  change guard=(if threshold<old+rootMass I w then 1 else 0 : ℤ) at hguard
  change ν counter=((old+rootMass I w : ℕ) : ℤ) at hcounterν
  have hcomparison : (0 : ℤ)<guard ↔ threshold<old+rootMass I w := by
    rw [hguard]
    by_cases hh : threshold<old+rootMass I w <;> simp [hh]
  light_if hyes hno : (0 : ℤ)<guard using LightReportingWantedInitialize.time
  · have hh := hcomparison.mp hyes
    simp only [if_pos hh]
    light_set (1 : ℕ) using LightReportingWantedInitialize.time
    exact ⟨by simp,by simp [hh],hcounterν,hkeep⟩
  · have hh : ¬threshold<old+rootMass I w := fun ht => hno (hcomparison.mpr ht)
    simp only [if_neg hh]
    have hkeepCounter : Kept μ ν counter := fun i hi => hkeep i ⟨hi.trans_le hcounterRows,Or.inl hi⟩
    have HSν := HS.of_kept (HB 0 (by omega)) hkeepCounter
    have HCν : ∀ (j : ℕ) (hj : j≤K), Stored ν (D j) (hj.trans hK) (p : ℤ) shift B C b c w.2.2 :=
      fun j hj => (HC j hj).of_kept (HB j hj) hkeepCounter
    have hmetaν : ∀ j≤K, SegN ν (catalogs+5*j) ((D j).record h j) := by
      intro j hj i hi
      have hi' : i<5 := by simpa only [Catalog.record,List.length_map,List.length_cons,List.length_nil] using hi
      have hm := Nat.mul_le_mul_left 5 (show j+1≤K+1 by omega)
      exact (hkeepCounter _ (by omega)).trans (hmeta j hj i hi)
    have hrowν (j : ℕ) (hj : j<J) : ν (rows+j)=(rowMask (outputRows w.2.2) ⟨j,hj⟩ : ℤ) := by
      have hp := hpacked.getElem (i := j) (by simpa only [packedMasks_length] using hj)
      simpa only [packedMasks,List.getElem_ofFn] using hp
    have HLν := LightReportingLeaf.stored_of_kept HL hkeyL hoffsetsL hflatL hkeepCounter
    have HRν := LightReportingLeaf.stored_of_kept HR hkeyR hoffsetsR hflatR hkeepCounter
    have hcoverν := hcover.of_kept hkeepCounter hmaps hcandidates hleft hright
    have hoccν (j : ℕ) (hj : j<J) : ν (occ+j)=(occurrenceIndices (outputOccurrences w.2.2) j : ℤ) := by
      refine (hkeep _ ⟨by omega,?_⟩).trans (hoccRead j hj)
      rcases hoccApart with hb | hb
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
    have hsearch := LightReportingWantedSearch.program_meets (μ := ν) (d := d+1)
      (srcL := srcL) (srcR := srcR) (occ := occ) (maps := maps) (candidates := candidates)
      (histL := histL) (histR := histR) (root := root) (catalogs := catalogs) (rows := rows)
      (baseL := baseL) (baseR := baseR) (masks := masks) (childL := childL) (childR := childR)
      (counts := counts) (selected := selected) (maskBase := maskBase) (work := work)
      (terminalMasks := terminalMasks) (masksL := masksL) (masksR := masksR)
      (base := base) (bitBase := bitBase) (rowOut := rowOut)
      p shift left right A B C a b c w D hK hkey hw HSν HCν (fun j hj => (HB j hj).mono hcounterRoot) HW
      hmetaν (by omega) hrows hrowν hcapν hfrontier hout hmasks hchildL hchildR hcounts hselected hparams HLν HRν
      (hsrcL.trans hcounterRoot) (hsrcR.trans hcounterRoot)
      (hoffsetsL.trans hcounterRoot) (hoffsetsR.trans hcounterRoot) (hflatL.trans hcounterRoot) (hflatR.trans hcounterRoot)
      (by omega) (hmaps.trans hcounterRoot) (hcandidates.trans hcounterRoot) (hleft.trans hcounterRoot) (hright.trans hcounterRoot)
      hterminalSlot hterminalMasks hmasksL hmasksR hstop hbits hrowOut hspace hword hoccν hcoverν
      (fun i hi => (hkeepCounter _ (by omega)).trans (hreadL i hi))
      (fun j hj => (hkeepCounter _ (by omega)).trans (hreadR j hj)) hvaluesL hvaluesR ha htarget hcountWord hsearchDepth
    have hsearchRun := (ReportingHostRelocation.meets hsearch LightReportingWantedInitialize.program).append [body 41 136]
    change Meets lim program 136 (d+1) _ ν (LightReportingWantedSearch.time p shift left right NL NR I w D K) _ at hsearchRun
    light_call hsearchRun with found ν₂ ⟨hbool,hhit,hkeepSearch⟩
    refine ⟨hbool,?_,(hkeepSearch _ (by omega)).trans hcounterν,?_⟩
    · change found=1 ↔ threshold<old+rootMass I w ∨
        ∃ pre∈ReportingHostFrontier.frontier I w K,
          ReportingHostTerminalBatch.Hit (a w.1) p shift left right NL NR w.2.2 K pre
      simpa only [hh,false_or] using hhit
    · intro i hi
      exact (hkeepSearch _ (by omega)).trans (hkeep i hi)

end ThreeSum.LightReportingWanted
