import Submission.ThreeSum.ReportingHostSourceSelection

/-!
# Actual constant-time selection of both independent source bands

The procedure reads the retained band, stage-bank and cover headers. It
materializes the fifteen controls consumed by wanted reporting, including
physical bucket pointers and the shared occurrence row, without scanning
any source or reconstructing a transform. All reads precede all writes.
-/

namespace ThreeSum.LightReportingSourceSelect

open Light ReportingHostSourceSelection

set_option maxHeartbeats 2600000
set_option maxRecDepth 14000

/-- Pair header, source-bank header, cover, original B/C bases, independent
B/C band indices, decoded occurrence code, J, and the fifteen-cell output. -/
def body : Stmt :=
  .set 10 (M (v 0)) ;;
  .set 11 (M (v 0 +' k 2)) ;;
  .set 12 (M (v 1)) ;;
  .set 13 (M (v 1 +' k 2)) ;;
  .set 14 (M (v 1 +' k 4)) ;;
  .set 15 (v 10 +' k 6 *' v 5) ;;
  .set 16 (v 11 +' k 6 *' v 6) ;;
  .set 17 (M (v 15)) ;;
  .set 18 (M (v 15 +' k 1)) ;;
  .set 19 (M (v 15 +' k 4)) ;;
  .set 20 (M (v 15 +' k 5)) ;;
  .set 21 (M (v 16)) ;;
  .set 22 (M (v 16 +' k 1)) ;;
  .set 23 (M (v 16 +' k 4)) ;;
  .set 24 (M (v 16 +' k 5)) ;;
  .set 25 (v 3 +' v 17) ;;
  .set 26 (v 4 +' v 21) ;;
  .set 27 (v 12 +' v 5 *' v 13 +' k 2 *' v 7) ;;
  .set 28 (v 12 +' v 6 *' v 13 +' k 2 *' v 7 +' k 1) ;;
  .set 29 (M (v 27)) ;;
  .set 30 (M (v 28)) ;;
  .set 31 (v 14 +' v 7 *' v 8) ;;
  .set 32 (M (v 2 +' k 12)) ;;
  .set 33 (M (v 2 +' k 13)) ;;
  .set 34 (M (v 2 +' k 14)) ;;
  .set 35 (M (v 2 +' k 15)) ;;
  .store (v 9) (v 25) ;;
  .store (v 9 +' k 1) (v 26) ;;
  .store (v 9 +' k 2) (v 19) ;;
  .store (v 9 +' k 3) (v 20) ;;
  .store (v 9 +' k 4) (v 23) ;;
  .store (v 9 +' k 5) (v 24) ;;
  .store (v 9 +' k 6) (v 18) ;;
  .store (v 9 +' k 7) (v 22) ;;
  .store (v 9 +' k 8) (v 29) ;;
  .store (v 9 +' k 9) (v 30) ;;
  .store (v 9 +' k 10) (v 31) ;;
  .store (v 9 +' k 11) (v 32) ;;
  .store (v 9 +' k 12) (v 33) ;;
  .store (v 9 +' k 13) (v 34) ;;
  .store (v 9 +' k 14) (v 35) ;;
  .set 0 (v 9)

def program : Program := [body]

theorem program_meets_fits {lim : Limits} {μ : ℕ→ℤ} {d pair bank cover srcB srcC i j code J dst : ℕ}
    (X : Pointers) (H : HeaderReads μ X pair bank cover i j code)
    (hw : (lim.space : ℤ)≤lim.word)
    (hs : Fits X pair bank cover srcB srcC i j code J dst lim.space) :
    Meets lim program 0 d [pair,bank,cover,srcB,srcC,i,j,code,J,dst] μ 6000
      (fun result ν => result=(dst : ℤ) ∧ SegN ν dst (values X srcB srcC code J) ∧
        SameOutside μ ν dst 15) := by
  obtain ⟨hL,hR,hfirst,hspan,hocc,hstartL,hsizeL,hoffL,hflatL,hstartR,hsizeR,hoffR,hflatR,
    hstagesL,hstagesR,hmaps,hcandidates,hhistL,hhistR⟩ := H
  have hpairBound := hs.pair
  have hbankBound := hs.bank
  have hcoverBound := hs.cover
  have houtputBound := hs.output
  have hleftBound := hs.leftHead
  have hrightBound := hs.rightHead
  have hleftStageBound := hs.leftStage
  have hrightStageBound := hs.rightStage
  have hoccBound := hs.occurrence
  have hscalarBound := hs.scalars
  dsimp only [leftHead,rightHead,leftStageCell,rightStageCell,occurrenceRow] at hleftBound hrightBound hleftStageBound hrightStageBound hoccBound
  have hv0 : srcB+X.startL≤lim.space := hs.values _ (by simp only [values,List.mem_cons,List.not_mem_nil,or_false]; tauto)
  have hv1 : srcC+X.startR≤lim.space := hs.values _ (by simp only [values,List.mem_cons,List.not_mem_nil,or_false]; tauto)
  have hv2 : X.offsetsL≤lim.space := hs.values _ (by simp only [values,List.mem_cons,List.not_mem_nil,or_false]; tauto)
  have hv3 : X.flatL≤lim.space := hs.values _ (by simp only [values,List.mem_cons,List.not_mem_nil,or_false]; tauto)
  have hv4 : X.offsetsR≤lim.space := hs.values _ (by simp only [values,List.mem_cons,List.not_mem_nil,or_false]; tauto)
  have hv5 : X.flatR≤lim.space := hs.values _ (by simp only [values,List.mem_cons,List.not_mem_nil,or_false]; tauto)
  have hv6 : X.sizeL≤lim.space := hs.values _ (by simp only [values,List.mem_cons,List.not_mem_nil,or_false]; tauto)
  have hv7 : X.sizeR≤lim.space := hs.values _ (by simp only [values,List.mem_cons,List.not_mem_nil,or_false]; tauto)
  have hv8 : X.stagesL≤lim.space := hs.values _ (by simp only [values,List.mem_cons,List.not_mem_nil,or_false]; tauto)
  have hv9 : X.stagesR≤lim.space := hs.values _ (by simp only [values,List.mem_cons,List.not_mem_nil,or_false]; tauto)
  have hv10 : occurrenceRow X code J≤lim.space := hs.values _ (by simp only [values,List.mem_cons,List.not_mem_nil,or_false]; tauto)
  have hv11 : X.maps≤lim.space := hs.values _ (by simp only [values,List.mem_cons,List.not_mem_nil,or_false]; tauto)
  have hv12 : X.candidates≤lim.space := hs.values _ (by simp only [values,List.mem_cons,List.not_mem_nil,or_false]; tauto)
  have hv13 : X.histL≤lim.space := hs.values _ (by simp only [values,List.mem_cons,List.not_mem_nil,or_false]; tauto)
  have hv14 : X.histR≤lim.space := hs.values _ (by simp only [values,List.mem_cons,List.not_mem_nil,or_false]; tauto)
  have hpair2 : μ (((pair : ℤ)+2).toNat)=(X.rightHeaders : ℤ) := by
    rw [show ((pair : ℤ)+2).toNat=pair+2 by omega]; exact hR
  have hbank2 : μ (((bank : ℤ)+2).toNat)=(X.bankSpan : ℤ) := by
    rw [show ((bank : ℤ)+2).toNat=bank+2 by omega]; exact hspan
  have hbank4 : μ (((bank : ℤ)+4).toNat)=(X.occurrenceBase : ℤ) := by
    rw [show ((bank : ℤ)+4).toNat=bank+4 by omega]; exact hocc
  have hleft1 : μ (((leftHead X i : ℕ) : ℤ)+1).toNat=(X.sizeL : ℤ) := by
    rw [show (((leftHead X i : ℕ) : ℤ)+1).toNat=leftHead X i+1 by omega]; exact hsizeL
  have hleft4 : μ (((leftHead X i : ℕ) : ℤ)+4).toNat=(X.offsetsL : ℤ) := by
    rw [show (((leftHead X i : ℕ) : ℤ)+4).toNat=leftHead X i+4 by omega]; exact hoffL
  have hleft5 : μ (((leftHead X i : ℕ) : ℤ)+5).toNat=(X.flatL : ℤ) := by
    rw [show (((leftHead X i : ℕ) : ℤ)+5).toNat=leftHead X i+5 by omega]; exact hflatL
  have hright1 : μ (((rightHead X j : ℕ) : ℤ)+1).toNat=(X.sizeR : ℤ) := by
    rw [show (((rightHead X j : ℕ) : ℤ)+1).toNat=rightHead X j+1 by omega]; exact hsizeR
  have hright4 : μ (((rightHead X j : ℕ) : ℤ)+4).toNat=(X.offsetsR : ℤ) := by
    rw [show (((rightHead X j : ℕ) : ℤ)+4).toNat=rightHead X j+4 by omega]; exact hoffR
  have hright5 : μ (((rightHead X j : ℕ) : ℤ)+5).toNat=(X.flatR : ℤ) := by
    rw [show (((rightHead X j : ℕ) : ℤ)+5).toNat=rightHead X j+5 by omega]; exact hflatR
  have hcover12 : μ (((cover : ℤ)+12).toNat)=(X.maps : ℤ) := by
    rw [show ((cover : ℤ)+12).toNat=cover+12 by omega]; exact hmaps
  have hcover13 : μ (((cover : ℤ)+13).toNat)=(X.candidates : ℤ) := by
    rw [show ((cover : ℤ)+13).toNat=cover+13 by omega]; exact hcandidates
  have hcover14 : μ (((cover : ℤ)+14).toNat)=(X.histL : ℤ) := by
    rw [show ((cover : ℤ)+14).toNat=cover+14 by omega]; exact hhistL
  have hcover15 : μ (((cover : ℤ)+15).toNat)=(X.histR : ℤ) := by
    rw [show ((cover : ℤ)+15).toNat=cover+15 by omega]; exact hhistR
  have hleftHead : leftHead X i+6≤lim.space := by unfold leftHead; omega
  have hrightHead : rightHead X j+6≤lim.space := by unfold rightHead; omega
  have hleftStage : leftStageCell X i code+1≤lim.space := by unfold leftStageCell; omega
  have hrightStage : rightStageCell X j code+1≤lim.space := by unfold rightStageCell; omega
  have hoccRow : occurrenceRow X code J≤lim.space := by unfold occurrenceRow; omega
  have hmulL : (0 : ℤ)≤(i : ℤ)*X.bankSpan := by positivity
  have hmulR : (0 : ℤ)≤(j : ℤ)*X.bankSpan := by positivity
  have hmulOcc : (0 : ℤ)≤(code : ℤ)*J := by positivity
  have hleftWord : (X.firstBank : ℤ)+(i : ℤ)*X.bankSpan+2*(code : ℤ)≤lim.word := by
    have hh : X.firstBank+i*X.bankSpan+2*code≤lim.space := by omega
    exact_mod_cast (Int.ofNat_le.mpr hh).trans hw
  have hrightWord : (X.firstBank : ℤ)+(j : ℤ)*X.bankSpan+2*(code : ℤ)+1≤lim.word := by
    have hh : X.firstBank+j*X.bankSpan+2*code+1≤lim.space := by omega
    exact_mod_cast (Int.ofNat_le.mpr hh).trans hw
  have hoccWord : (X.occurrenceBase : ℤ)+(code : ℤ)*J≤lim.word := by
    have hh : X.occurrenceBase+code*J≤lim.space := by omega
    exact_mod_cast (Int.ofNat_le.mpr hh).trans hw
  apply Meets.of_body (p := 0) (by rfl : program[0]?=some body)
  unfold body
  light_set (X.leftHeaders : ℕ) using hL
  light_set (X.rightHeaders : ℕ) using hR,hpair2
  light_set (X.firstBank : ℕ) using hfirst
  light_set (X.bankSpan : ℕ) using hspan,hbank2
  light_set (X.occurrenceBase : ℕ) using hocc,hbank4
  light_set (leftHead X i : ℕ) using leftHead
  light_set (rightHead X j : ℕ) using rightHead
  light_set (X.startL : ℕ) using hstartL
  light_set (X.sizeL : ℕ) using hsizeL,hleft1
  light_set (X.offsetsL : ℕ) using hoffL,hleft4
  light_set (X.flatL : ℕ) using hflatL,hleft5
  light_set (X.startR : ℕ) using hstartR
  light_set (X.sizeR : ℕ) using hsizeR,hright1
  light_set (X.offsetsR : ℕ) using hoffR,hright4
  light_set (X.flatR : ℕ) using hflatR,hright5
  light_set (srcB+X.startL : ℕ)
  light_set (srcC+X.startR : ℕ)
  light_set (leftStageCell X i code : ℕ) using leftStageCell
  light_set (rightStageCell X j code : ℕ) using rightStageCell
  light_set (X.stagesL : ℕ) using hstagesL
  light_set (X.stagesR : ℕ) using hstagesR
  light_set (occurrenceRow X code J : ℕ) using occurrenceRow
  light_set (X.maps : ℕ) using hmaps,hcover12
  light_set (X.candidates : ℕ) using hcandidates,hcover13
  light_set (X.histL : ℕ) using hhistL,hcover14
  light_set (X.histR : ℕ) using hhistR,hcover15
  light_store dst (srcB+X.startL : ℕ)
  light_store (dst+1) (srcC+X.startR : ℕ)
  light_store (dst+2) (X.offsetsL : ℕ)
  light_store (dst+3) (X.flatL : ℕ)
  light_store (dst+4) (X.offsetsR : ℕ)
  light_store (dst+5) (X.flatR : ℕ)
  light_store (dst+6) (X.sizeL : ℕ)
  light_store (dst+7) (X.sizeR : ℕ)
  light_store (dst+8) (X.stagesL : ℕ)
  light_store (dst+9) (X.stagesR : ℕ)
  light_store (dst+10) (occurrenceRow X code J : ℕ) using occurrenceRow
  light_store (dst+11) (X.maps : ℕ)
  light_store (dst+12) (X.candidates : ℕ)
  light_store (dst+13) (X.histL : ℕ)
  light_store (dst+14) (X.histR : ℕ)
  light_set (dst : ℕ)
  refine ⟨rfl,?_,?_⟩
  · intro t ht
    have ht' : t<15 := by simpa only [values,List.length_map,List.length_cons,List.length_nil] using ht
    interval_cases t <;> simp [values]
  · intro a ha
    dsimp only
    repeat rw [Function.update_of_ne (by omega)]

theorem program_meets {lim : Limits} {μ : ℕ→ℤ} {d pair bank cover srcB srcC i j code J dst : ℕ}
    (X : Pointers) (H : HeaderReads μ X pair bank cover i j code)
    (hw : (lim.space : ℤ)≤lim.word)
    (hs : space X pair bank cover srcB srcC i j code J dst≤lim.space) :
    Meets lim program 0 d [pair,bank,cover,srcB,srcC,i,j,code,J,dst] μ 6000
      (fun result ν => result=(dst : ℤ) ∧ SegN ν dst (values X srcB srcC code J) ∧
        SameOutside μ ν dst 15) :=
  program_meets_fits X H hw (fits_of_space X pair bank cover srcB srcC i j code J dst lim.space hs)

end ThreeSum.LightReportingSourceSelect
