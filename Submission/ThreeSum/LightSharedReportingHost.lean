import Submission.ThreeSum.LightSharedReportingBank
import Submission.ThreeSum.LightSharedReportingCounts
import Submission.ThreeSum.SharedReportingBankHeader
import Submission.ThreeSum.SourceControlLayout

/-!
# Execute the shared reporting bank from retained source headers

The inclusive terminal level count and both local combinatorial counts
are computed by actual programs. Occurrence count, band counts, and the
source-bank first pointer and stride are loaded from their retained
headers. The nine-cell result header precedes all five-cell level records
and compact catalog payloads.
-/

namespace ThreeSum.LightSharedReportingHost

open Light GlobalEncoding SharedReportingBankLayout SharedReportingBankRows
open SharedReportingBankHeader

set_option maxHeartbeats 3900000
set_option maxRecDepth 16000

/-- h,J,source controls header,source pair header,source bank header,free. -/
def body (pDepth pCounts pBank : ℕ) : Stmt :=
  .set 7 (M (v 2 +' k 1)) ;;
  .set 8 (M (v 3 +' k 1)) ;;
  .set 9 (M (v 3 +' k 3)) ;;
  .set 10 (M (v 4)) ;;
  .set 11 (M (v 4 +' k 2)) ;;
  .call pDepth [v 1] 6 ;;
  .set 6 (v 6 +' k 1) ;;
  .set 12 (v 5 +' k 9) ;;
  .call pCounts [v 0,v 5 +' k 7,v 12] 13 ;;
  .set 14 (M (v 5 +' k 7)) ;;
  .set 15 (v 7 *' v 8 *' v 9) ;;
  .set 16 (v 12 +' k 5 *' v 6 *' v 15) ;;
  .call pBank [v 0,v 1,v 6,v 10,v 11,v 7,v 8,v 9,v 14,v 13,v 12,v 16] 17 ;;
  .set 17 (v 17) ;;
  .store (v 5) (v 12) ;;
  .store (v 5 +' k 1) (v 16) ;;
  .store (v 5 +' k 2) (v 6) ;;
  .store (v 5 +' k 3) (v 7) ;;
  .store (v 5 +' k 4) (v 8) ;;
  .store (v 5 +' k 5) (v 9) ;;
  .store (v 5 +' k 6) (v 17) ;;
  .set 0 (v 17)

def depthPrefix : Program := LightSharedReportingBank.program ++
  LightSwitchDepth.program.map (ReportingHostRelocation.relocate LightSharedReportingBank.program.length)
def countMap : Program :=
  LightSharedReportingCounts.program.map (ReportingHostRelocation.relocate depthPrefix.length)
def program : Program := depthPrefix ++ countMap ++ [body 67 69 66]
theorem program_length : program.length=75 := rfl

def time (h J NB NC g : ℕ) : ℕ :=
  LightSwitchDepth.time J+LightSharedReportingCounts.time h+
    LightSharedReportingBank.time h J (levels J) NB NC g+3000
def space (free h J NB NC g : ℕ) : ℕ :=
  max (records free+LightPascal.tableSize (512*h)) (finish free h J NB NC g)

structure Resources (lim : Limits) (free h J NB NC g d : ℕ) : Prop where
  space : space free h J NB NC g ≤ lim.space
  control : (LightSharedReportingBank.controlWord h J (levels J) NB NC g : ℤ) ≤ lim.word
  span : (SourceBandBankLayout.span h J (2*h*J) : ℤ) ≤ lim.word
  powers : ((2^(512*h+1) : ℕ) : ℤ) ≤ lim.word
  pairs : (localPairs h : ℤ) ≤ lim.word
  depthWord : (LightSwitchDepth.word J : ℤ) ≤ lim.word
  depth : d+512*h+4 ≤ lim.depth
  bank : ∀ q < total h J NB NC g,
    LightSharedReportingLevels.Resources lim
      (rowBase (payload free h J NB NC g) h J (levels J) q) h J (levels J) g g (d+3)

theorem program_meets {lim : Limits} {μ : ℕ → ℤ} {fB fC : ℕ → ℤ}
    {controls pairHeader bankHeader free NB NC g h J occ p m d : ℕ} {shift : ℤ}
    (Hcontrol : Seg μ controls (SourceControlLayout.values h J (2*h*J)))
    (Hpair : SourceBandPairData.Stored μ fB fC pairHeader NB NC g p m shift)
    (Hbank : SourceBandBankData.Stored μ fB fC bankHeader NB NC g h J (2*h*J) occ (p : ℤ) shift)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hcontrol : controls+3 ≤ free) (hpair : pairHeader+8 ≤ free)
    (hocc : occ+LightBlockSourceCatalog.count h J*J ≤ bankHeader)
    (hsource : SourceBandBankData.finish bankHeader NB NC g h J (2*h*J) ≤ free)
    (R : Resources lim free h J NB NC g d) :
    Meets lim program 74 d [h,J,controls,pairHeader,bankHeader,free] μ (time h J NB NC g)
      (fun result ν => result=(finish free h J NB NC g : ℤ) ∧
        Stored ν free h J NB NC g fB fC (p : ℤ) shift ∧ Kept μ ν free) := by
  have hfinish : finish free h J NB NC g ≤ lim.space := (le_max_right _ _).trans R.space
  have hpascal : records free+LightPascal.tableSize (512*h) ≤ lim.space :=
    (le_max_left _ _).trans R.space
  have hpayload : payload free h J NB NC g ≤ lim.space := (payload_le_finish _ _ _ _ _ _).trans hfinish
  have hrecords : records free ≤ lim.space := (records_le_payload _ _ _ _ _ _).trans hpayload
  have hfree : free+9 ≤ lim.space := hrecords
  have hsourceStart : bankHeader+5 ≤ SourceBandBankData.finish bankHeader NB NC g h J (2*h*J) :=
    Nat.le_add_right _ _
  have hctl := R.control
  unfold LightSharedReportingBank.controlWord at hctl
  have hconstants : (512 : ℤ) ≤ lim.word := by exact_mod_cast (show (512 : ℤ) ≤ lim.word by omega)
  have hchoose : localChoose h ≤ 2^(512*h+1) :=
    (Nat.choose_le_two_pow (512*h) h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hdepth := R.depth
  have hdepthJ : LightSwitchDepth.depth J ≤ J := SharedReportingBankLevels.level_le le_rfl
  have hspan := R.span
  have hpairs := R.pairs
  have hpow := R.powers
  have hdword := R.depthWord
  have hKword : ((5*levels J : ℕ) : ℤ) ≤ lim.word := by
    apply (Int.ofNat_le.mpr (show 5*levels J ≤ LightSwitchDepth.word J by
      unfold levels LightSwitchDepth.depth LightSwitchDepth.word
      omega)).trans R.depthWord
  have hPword : (total h J NB NC g : ℤ) ≤ lim.word := by
    have hh := Nat.le_mul_of_pos_left (total h J NB NC g) (show 0 < 5*levels J by
      have hk := levels_pos J
      omega)
    exact (Int.ofNat_le.mpr (show total h J NB NC g ≤ lim.space by unfold payload at hpayload; omega)).trans hw
  have hpOne : (LightBlockSourceCatalog.count h J : ℤ)*(BandPartition.size NB g : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (show LightBlockSourceCatalog.count h J*BandPartition.size NB g ≤
      LightSharedReportingBank.controlWord h J (levels J) NB NC g by
      unfold LightSharedReportingBank.controlWord; omega)).trans R.control
  have hpOneNZ : (0 : ℤ) ≤ (LightBlockSourceCatalog.count h J : ℤ)*(BandPartition.size NB g : ℤ) := by positivity
  have hpTwo : (LightBlockSourceCatalog.count h J : ℤ)*(BandPartition.size NB g : ℤ)*
      (BandPartition.size NC g : ℤ) ≤ lim.word := by
    simpa only [total,SharedReportingBankRows.pairs,Nat.cast_mul] using hPword
  have hpTwoNZ : (0 : ℤ) ≤ (LightBlockSourceCatalog.count h J : ℤ)*(BandPartition.size NB g : ℤ)*
      (BandPartition.size NC g : ℤ) := by positivity
  have hmetaNZ : (0 : ℤ) ≤ 5*(levels J : ℤ)*(total h J NB NC g : ℤ) := by positivity
  have hmetaWord : 5*(levels J : ℤ)*(total h J NB NC g : ℤ) ≤ lim.word := by
    exact_mod_cast (show ((5*levels J*total h J NB NC g : ℕ) : ℤ) ≤ lim.word from
      (Int.ofNat_le.mpr (show 5*levels J*total h J NB NC g ≤ lim.space by unfold payload at hpayload; omega)).trans hw)
  have hpayloadWord : (records free : ℤ)+5*(levels J : ℤ)*(total h J NB NC g : ℤ) ≤ lim.word := by
    simpa only [payload,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using
      (Int.ofNat_le.mpr hpayload).trans hw
  have hreadS : μ (controls+1)=(LightBlockSourceCatalog.count h J : ℤ) := by
    simpa [SourceControlLayout.values] using Hcontrol.getD (i := 1) (by simp [SourceControlLayout.values]) 0
  obtain ⟨_,hreadNB,_,hreadNC,_⟩ := SourceBandPairSlices.heads_read Hpair
  obtain ⟨hreadFirst,_,hreadSpan,_⟩ := Hbank.heads_read
  have haS : ((controls : ℤ)+1).toNat=controls+1 := by omega
  have haB : ((pairHeader : ℤ)+1).toNat=pairHeader+1 := by omega
  have haC : ((pairHeader : ℤ)+3).toNat=pairHeader+3 := by omega
  have haSpan : ((bankHeader : ℤ)+2).toNat=bankHeader+2 := by omega
  have haH : ((free : ℤ)+7).toNat=free+7 := by omega
  apply Meets.of_body (p := 74) (by rfl : program[74]?=some (body 67 69 66))
  unfold body time
  light_set (LightBlockSourceCatalog.count h J : ℕ) using hreadS,haS,records
  light_set (BandPartition.size NB g : ℕ) using hreadNB,haB,records
  light_set (BandPartition.size NC g : ℕ) using hreadNC,haC,records
  light_set (SourceBandBankData.first bankHeader : ℕ) using hreadFirst,SourceBandBankData.first,records
  light_set (SourceBandBankLayout.span h J (2*h*J) : ℕ) using hreadSpan,haSpan,records
  have hdepthCall := ((ReportingHostRelocation.meets
    (LightSwitchDepth.program_meets (μ := μ) (d := d+1) R.depthWord (by omega))
    LightSharedReportingBank.program).append countMap).append [body 67 69 66]
  light_call hdepthCall with resultDepth νt ⟨hresultDepth,hmem⟩
  subst νt
  light_set (levels J : ℕ) using hresultDepth,levels
  light_set (records free : ℕ) using records
  have hcountCall := (ReportingHostRelocation.meets
    (LightSharedReportingCounts.program_meets (μ := μ) (d := d+1) (h := h) (dst := free+7)
      (work := records free) hw (by unfold records; omega) hconstants hpascal R.powers R.pairs (by omega))
    depthPrefix).append [body 67 69 66]
  light_call hcountCall using records with resultPairs ν₁ ⟨hresultPairs,hcounts,hkeepCounts⟩
  have hreadH : ν₁ (free+7)=(localChoose h : ℤ) := by
    simpa [SegN] using hcounts.getD (i := 0) (by simp [SegN]) 0
  have hreadE : ν₁ (free+8)=(localPairs h : ℤ) := by
    simpa [SegN,Nat.add_assoc] using hcounts.getD (i := 1) (by simp [SegN]) 0
  light_set (localChoose h : ℕ) using hreadH,haH,records
  light_set (total h J NB NC g : ℕ) using total,SharedReportingBankRows.pairs
  light_set (payload free h J NB NC g : ℕ) using payload
  have hkeptFree : Kept μ ν₁ free := fun a ha => hkeepCounts a (by omega)
  have hbankNow := Hbank.of_kept hkeptFree hocc hsource
  have hbankCall := (((LightSharedReportingBank.program_meets (μ := ν₁) (d := d+1)
    (record := records free) (base := payload free h J NB NC g) hbankNow hw (levels_pos J)
    (by rfl) hocc (hsource.trans (by unfold records; omega)) le_rfl hfinish R.control R.bank).append
      (LightSwitchDepth.program.map (ReportingHostRelocation.relocate LightSharedReportingBank.program.length))).append
      countMap).append [body 67 69 66]
  light_call hbankCall using hresultPairs with result ν₂ ⟨hresult,hrows,hkeepBank,_⟩
  have hresultFinish : result=(finish free h J NB NC g : ℤ) := hresult
  have hreadH₂ : ν₂ (free+7)=(localChoose h : ℤ) :=
    (hkeepBank _ (by unfold records; omega)).trans hreadH
  have hreadE₂ : ν₂ (free+8)=(localPairs h : ℤ) :=
    (hkeepBank _ (by unfold records; omega)).trans hreadE
  light_set (finish free h J NB NC g : ℕ) using hresultFinish
  light_store free (records free : ℕ) using records
  light_store (free+1) (payload free h J NB NC g : ℕ) using records
  light_store (free+2) (levels J : ℕ) using records
  light_store (free+3) (LightBlockSourceCatalog.count h J : ℕ) using records
  light_store (free+4) (BandPartition.size NB g : ℕ) using records
  light_store (free+5) (BandPartition.size NC g : ℕ) using records
  light_store (free+6) (finish free h J NB NC g : ℕ) using records
  light_set (finish free h J NB NC g : ℕ)
  refine ⟨rfl,⟨?_,?_⟩,?_⟩
  · intro i hi
    have hi' : i < 9 := by simpa [SegN,header] using hi
    interval_cases i <;> simp [SegN,header,hreadH₂,hreadE₂]
  · apply done_of_after hrows ?_ le_rfl (records_le_payload _ _ _ _ _ _)
    intro a ha
    have h0 : a ≠ free := by unfold records at ha; omega
    have h1 : a ≠ free+1 := by unfold records at ha; omega
    have h2 : a ≠ free+2 := by unfold records at ha; omega
    have h3 : a ≠ free+3 := by unfold records at ha; omega
    have h4 : a ≠ free+4 := by unfold records at ha; omega
    have h5 : a ≠ free+5 := by unfold records at ha; omega
    have h6 : a ≠ free+6 := by unfold records at ha; omega
    simp [Function.update_of_ne,h0,h1,h2,h3,h4,h5,h6]
  · intro a ha
    have h0 : a ≠ free := by omega
    have h1 : a ≠ free+1 := by omega
    have h2 : a ≠ free+2 := by omega
    have h3 : a ≠ free+3 := by omega
    have h4 : a ≠ free+4 := by omega
    have h5 : a ≠ free+5 := by omega
    have h6 : a ≠ free+6 := by omega
    simp only [Function.update_of_ne h6,Function.update_of_ne h5,Function.update_of_ne h4,
      Function.update_of_ne h3,Function.update_of_ne h2,Function.update_of_ne h1,Function.update_of_ne h0]
    exact (hkeepBank _ (by unfold records; omega)).trans (hkeptFree a ha)

end ThreeSum.LightSharedReportingHost
