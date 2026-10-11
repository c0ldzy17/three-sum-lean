import Submission.ThreeSum.LightEncodedColorPrimeHost
import Submission.ThreeSum.EncodedColorStageCosts
import Submission.ThreeSum.EncodedColorPipelineData
import Submission.ThreeSum.LightEncodedColorWantedHeader

/-! # Execute one original color through the retained shared source bank -/

namespace ThreeSum.LightEncodedColorPipeline

open Light Scales BandScales ArithmeticStageBounds ColorClassLists EncodedColorLayout
open EncodedColorNormalizedData

set_option maxHeartbeats 4200000
set_option maxRecDepth 17000

local instance (n : ℕ) : NeZero (radix n) := ⟨Nat.ne_of_gt (radix_pos n)⟩

/-- Original array, length, parameter header, selected color row, free address. -/
def body (pPrime pSources pHeader pResult : ℕ) : Stmt :=
  .call pPrime [v 0,v 1,v 2,v 3,v 4] 5 ;;
  .set 6 (M (v 5)) ;;
  .set 7 (M (v 5 +' k 2)) ;;
  .set 8 (M (v 5 -' k 1)) ;;
  .set 9 (M (v 4 +' k 7)) ;;
  .set 10 (M (v 4 +' k 2)) ;;
  .set 11 (M (v 4 +' k 3)) ;;
  .set 12 (M (v 4 +' k 4)) ;;
  .set 13 (M (v 4 +' k 5)) ;;
  .set 14 (M (v 2 +' k 1)) ;;
  .set 15 (M (v 2 +' k 3)) ;;
  .set 16 (M (v 2 +' k 4)) ;;
  .set 17 (M (v 2 +' k 14)) ;;
  .set 18 (M (v 2 +' k 17)) ;;
  .call pSources [v 14,v 15,v 16,v 9,v 8,v 6,v 17,v 7,v 10,v 11,v 12,v 13,v 18] 19 ;;
  .call pHeader [v 7,v 15,v 8] 20 ;;
  .set 21 (M (v 20 +' k 2)) ;;
  .set 22 (M (v 21 +' k 8)) ;;
  .set 23 (M (v 21 +' k 1)) ;;
  .set 24 (v 22 +' v 23 *' v 15) ;;
  .call pResult [v 5,v 7,v 20,v 21,v 24,v 19,v 8,v 6] 0

def joined : Program := ReportingHostRelocation.program
  LightEncodedColorPrimeHost.program LightEncodedColorWantedSources.program

def program : Program := joined ++
  [LightEncodedColorWantedHeader.body,LightEncodedColorResult.body,body 71 252 253 254]

theorem program_length : program.length=256 := rfl

def sourceBound (free n : ℕ) : ℕ := EncodedColorStageCosts.sourceBase
  (EncodedColorPipelineData.coverBase free n) n (radix n) (EncodedColorStageCosts.incidenceCap n)

def finishBound (free n : ℕ) : ℕ := SourceFiniteCosts.finish (sourceBound free n) n

def time (n U : ℕ) : ℕ := LightEncodedColorPrimeHost.inputTime n U+
  EncodedColorStageCosts.time n (maxMod n) (radix n) U (EncodedColorStageCosts.incidenceCap n)+
  LightEncodedColorWantedHeader.time (blockCount (inputBits n))+1600

def space (free n U : ℕ) : ℕ := max (LightEncodedColorPrimeHost.inputSpace free n U)
  (max (EncodedColorStageCosts.space (EncodedColorPipelineData.coverBase free n) n (maxMod n)
    (radix n) U (EncodedColorStageCosts.incidenceCap n)) (finishBound free n+8))

def word (n U : ℕ) : ℕ := max (LightEncodedColorPrimeHost.inputWord n U)
  (EncodedColorStageCosts.word n (maxMod n) (radix n) U (EncodedColorStageCosts.incidenceCap n))+
    EncodedColorStageCosts.incidenceCap n+maxMod n+radix n+bandSize n+
    microHalf (inputBits n)+blockCount (inputBits n)+mu n+
    LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n))+100

def depth (n : ℕ) : ℕ := max (LightEncodedColorPrimeHost.depth n)
  (EncodedColorStageCosts.depth n (radix n) (EncodedColorStageCosts.incidenceCap n))+1

variable {lim : Limits} {d : ℕ}

theorem program_meets {μ : ℕ → ℤ} {src n params row free U : ℕ}
    (color : Coloring.Parameter (inputBits n+1)) (x : Fin n → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : 0 < n) (hR : 4 ≤ radix n)
    (hsrc : src+n ≤ free) (hparams : params+19 ≤ free) (hrow : row+6 ≤ free)
    (hspace : space free n U ≤ lim.space) (hword : (word n U : ℤ) ≤ lim.word)
    (hd : d+depth n ≤ lim.depth)
    (hread : Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i| ≤ (U : ℤ))
    (hparameters : Seg μ params (LightParameterInit.values n))
    (hcolor : Seg μ row (ColorParameters.fields color)) :
    Meets lim program 255 d [src,n,params,row,free] μ (time n U)
      (fun r ν => EncodedColorPipelineData.Output ν free n color x r ∧ Kept μ ν free) := by
  have hsPrime : LightEncodedColorPrimeHost.inputSpace free n U ≤ lim.space := (le_max_left _ _).trans hspace
  have hsStage : EncodedColorStageCosts.space (EncodedColorPipelineData.coverBase free n) n (maxMod n)
      (radix n) U (EncodedColorStageCosts.incidenceCap n) ≤ lim.space :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hspace)
  have hsFinish : finishBound free n+8 ≤ lim.space := (le_max_right _ _).trans ((le_max_right _ _).trans hspace)
  have hsmall (a : ℕ) (ha : a ≤ word n U) : (a : ℤ) ≤ lim.word := (Int.ofNat_le.mpr ha).trans hword
  have hwPrime := hsmall (LightEncodedColorPrimeHost.inputWord n U) (by unfold word; omega)
  have hwStage := hsmall (EncodedColorStageCosts.word n (maxMod n) (radix n) U
    (EncodedColorStageCosts.incidenceCap n)) (by unfold word; omega)
  have hCapWord := hsmall (EncodedColorStageCosts.incidenceCap n) (by unfold word; omega)
  have hPWord := hsmall (maxMod n) (by unfold word; omega)
  have hMWord := hsmall (radix n) (by unfold word; omega)
  have hGWord := hsmall (bandSize n) (by unfold word; omega)
  have hHWord := hsmall (microHalf (inputBits n)) (by unfold word; omega)
  have hJWord := hsmall (blockCount (inputBits n)) (by unfold word; omega)
  have hCutWord := hsmall (mu n) (by unfold word; omega)
  have hSWord := hsmall (LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n)))
    (by unfold word; omega)
  have hdPrime : d+1+LightEncodedColorPrimeHost.depth n ≤ lim.depth := by unfold depth at hd; omega
  have hdStage : d+1+EncodedColorStageCosts.depth n (radix n) (EncodedColorStageCosts.incidenceCap n) ≤
      lim.depth := by unfold depth at hd; omega
  have add2 : ((free : ℤ)+2).toNat=free+2 := by omega
  have add3 : ((free : ℤ)+3).toNat=free+3 := by omega
  have add4 : ((free : ℤ)+4).toNat=free+4 := by omega
  have add5 : ((free : ℤ)+5).toNat=free+5 := by omega
  have add7 : ((free : ℤ)+7).toNat=free+7 := by omega
  have par1 : ((params : ℤ)+1).toNat=params+1 := by omega
  have par3 : ((params : ℤ)+3).toNat=params+3 := by omega
  have par4 : ((params : ℤ)+4).toNat=params+4 := by omega
  have par14 : ((params : ℤ)+14).toNat=params+14 := by omega
  have par17 : ((params : ℤ)+17).toNat=params+17 := by omega
  have prime2 : ((prime free n (bandSize n) : ℤ)+2).toNat=prime free n (bandSize n)+2 := by omega
  have primePrev : ((prime free n (bandSize n) : ℤ)-1).toNat=normalizedEnd free n (bandSize n) := by
    unfold prime
    omega
  apply Meets.of_body (p := 255) (by rfl : program[255]?=some (body 71 252 253 254))
  unfold body time
  have hPrime := ((LightEncodedColorPrimeHost.program_meets_input (d := d+1) (μ := μ)
    (src := src) (params := params) (row := row) (free := free)
    color x hw hn hR hsrc hparams hrow hsPrime hwPrime hdPrime hread hbound hparameters hcolor).append
      (LightEncodedColorWantedSources.program.map (ReportingHostRelocation.relocate 72))).append
      [LightEncodedColorWantedHeader.body,LightEncodedColorResult.body,body 71 252 253 254]
  light_call hPrime with ptr μ₁ ⟨hptr,⟨heads,A,hsA,B,hsB,C,hsC,hcount,normalized,primes⟩,keptPrime⟩
  let xs := incidences n A B C hsA hsB hsC
  let p := EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC
  let cover := EncodedColorPipelineData.coverBase free n
  let wanted := EncodedColorPipelineData.wantedHeader free n xs.length
  let base := EncodedColorPipelineData.controls free n A B C hsA hsB hsC
  let bank := EncodedColorPipelineData.bankHeader free n A B C hsA hsB hsC
  let finish := EncodedColorPipelineData.finish free n A B C hsA hsB hsC
  let occ := LightSourceBandHost.occurrenceBase (LightSourceControlsHost.sourceBase base)
    B.length C.length (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n))
  have ha := length_classList_le color x 0 1
  have hb := length_classList_le color x 1 1
  have hc := length_classList_le color x 2 (-1)
  have hnA := normalized.2.1.2.1.trans ha
  have hnB := normalized.2.2.1.2.1.trans hb
  have hnC := normalized.2.2.2.1.2.1.trans hc
  have hlen : xs.length ≤ EncodedColorStageCosts.incidenceCap n := incidences_length_le hnA hnB hnC
  have hp : 0 < p := EncodedColorPrimeReadyData.selected_pos
  have hmax : p ≤ maxMod n := EncodedColorStageCosts.selected_le_maxMod hR
  have hbaseBound : base ≤ sourceBound free n := EncodedColorStageCosts.base_le hlen
  have hfinishBound : finish ≤ finishBound free n := EncodedColorStageCosts.finish_le hn hbaseBound hnB hnC
  have hfinishSpace : finish+8 ≤ lim.space := by omega
  obtain ⟨hmeta,hfree,hcover,hwanted,hcontrol,hbank⟩ := EncodedColorPipelineData.ordered free n A B C hsA hsB hsC
  change prime free n (bandSize n)+6 ≤ cover at hmeta
  change free+8 ≤ cover at hfree
  change cover ≤ base at hcover
  change wanted+4 ≤ base at hwanted
  change base+3 ≤ finish at hcontrol
  change bank+5 ≤ finish at hbank
  obtain ⟨hav,hae,hbv,hbe,hcv,hce,htables,hrecords,hcatalog⟩ :=
    normalized_ends_cover free n (bandSize n) (radix n) (primeWindow n)
  change av free n+n ≤ cover at hav
  change ae free n+2+2*n ≤ cover at hae
  change bv free n+n ≤ cover at hbv
  change be free n+2+2*n ≤ cover at hbe
  change cv free n+n ≤ cover at hcv
  change ce free n+2+2*n ≤ cover at hce
  change tables free n+ColorBandBounds.count n (bandSize n) ≤ cover at htables
  change rec free n (bandSize n)+4*ColorBandBounds.count n (bandSize n) ≤ cover at hrecords
  change normalizedEnd free n (bandSize n) ≤ cover at hcatalog
  have hvals : vals free n (bandSize n)+xs.length ≤ cover := by
    have hle : vals free n (bandSize n)+xs.length ≤ normalizedEnd free n (bandSize n) := by
      unfold EncodedColorStageCosts.incidenceCap at hlen
      unfold normalizedEnd LightBandRawA.space LightBandRawA.positionBase LightBandRawA.ownerBase LightBandRawA.capacity
      omega
    exact hle.trans hcatalog
  have hActualSpace := (EncodedColorStageCosts.space_le (free := cover) (U := U) hmax hlen).trans hsStage
  have hActualWord := (Int.ofNat_le.mpr (EncodedColorStageCosts.word_le (U := U) hmax hlen)).trans hwStage
  have hActualDepth : d+1+LightEncodedColorWantedSources.depth n (radix n) xs.length ≤ lim.depth :=
    (Nat.add_le_add_left (EncodedColorStageCosts.depth_le hlen) (d+1)).trans hdStage
  obtain ⟨readP,_,readCover,_,_,_⟩ := primes.heads_read
  change μ₁ (prime free n (bandSize n))=(p : ℤ) at readP
  change μ₁ (prime free n (bandSize n)+2)=(cover : ℤ) at readCover
  obtain ⟨_,_,readB,readBE,readC,readCE,_,readVals⟩ := EncodedColorNormalizedData.heads_read heads
  have params₁ := hparameters.of_kept keptPrime (by
    simpa [LightParameterInit.values,LightScales.values,LightLocalParameters.values,LightLocalCounts.values,
      LightGlobalSizes.values] using hparams)
  obtain ⟨_,readH,readJ,readCut,readM,readG,_⟩ := EncodedColorParameterData.reads params₁
  have hlenWord : (xs.length : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hlen).trans hCapWord
  have hpWord : (p : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hmax).trans hPWord
  have hPrevEq : (prime free n (bandSize n) : ℤ)-1=(normalizedEnd free n (bandSize n) : ℤ) := by
    unfold prime
    omega
  have hPrevWord : (normalizedEnd free n (bandSize n) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show normalizedEnd free n (bandSize n) ≤ lim.space by omega)).trans hw
  change μ₁ (normalizedEnd free n (bandSize n))=(xs.length : ℤ) at hcount
  light_set (p : ℕ) using hptr,readP
  light_set (cover : ℕ) using hptr,prime2,readCover
  light_set (xs.length : ℕ) using hptr,hPrevEq,hcount
  light_set (vals free n (bandSize n) : ℕ) using readVals,add7
  light_set (bv free n : ℕ) using readB,add2
  light_set (be free n : ℕ) using readBE,add3
  light_set (cv free n : ℕ) using readC,add4
  light_set (ce free n : ℕ) using readCE,add5
  light_set (microHalf (inputBits n) : ℕ) using readH,par1
  light_set (blockCount (inputBits n) : ℕ) using readJ,par3
  light_set (mu n : ℕ) using readCut,par4
  light_set (radix n : ℕ) using readM,par14
  light_set (bandSize n : ℕ) using readG,par17
  have hxs : Seg μ₁ (vals free n (bandSize n)) xs := normalized.2.2.2.2.2.2.valueRows
  have hclassA := LightColorBands.class_bounded color x 0 1 (by norm_num) hbound
  have hclassB := LightColorBands.class_bounded color x 1 1 (by norm_num) hbound
  have hclassC := LightColorBands.class_bounded color x 2 (-1) (by norm_num) hbound
  have hxsBound : ∀ z ∈ xs, |z| ≤ (U : ℤ) :=
    incidences_bounded (SourceFiniteInputs.prepared_bound normalized.2.1 hclassA)
  have hSources := (ReportingHostRelocation.meets
    (LightEncodedColorWantedSources.program_meets (d := d+1) (μ := μ₁) (a := vals free n (bandSize n))
      (free := cover) (p := p) (M := radix n) (U := U) (xs := xs) hw hActualDepth hn hp ha hb hc hvals
      hav hae hbv hbe hcv hce htables hrecords hcatalog hActualSpace hActualWord hxs hxsBound
      hclassB hclassC normalized) LightEncodedColorPrimeHost.program).append
      [LightEncodedColorWantedHeader.body,LightEncodedColorResult.body,body 71 252 253 254]
  have hSourcesBound := hSources.mono_time (EncodedColorStageCosts.time_le hmax hlen)
  light_call hSourcesBound using LightEncodedColorWantedSources.args
    with last μ₂ ⟨normalized₂,sources,cover₂,wanted₂,countBound,lifts,keptSources⟩
  have hlast : last=(finish : ℤ) := sources.returned
  have hnext : μ₂ (wanted+2)=(base : ℤ) := wanted₂.2.2.1
  have readOcc : μ₂ (base+8)=(occ : ℤ) := by
    simpa [LightSourceControlsHost.sourceBase,Nat.add_assoc,occ,LightSourceBandHost.occurrenceBase,
      base,EncodedColorPipelineData.controls,cover,p,xs]
      using (SourceBandPairSlices.heads_read sources.buckets).2.2.2.2.2.1
  have readS : μ₂ (base+1)=(LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n)) : ℤ) := by
    simpa [SourceControlLayout.values,base,EncodedColorPipelineData.controls,cover,p,xs]
      using sources.controls.getD (i := 1) (by simp [SourceControlLayout.values]) 0
  have hbankEq : bank=occ+LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n))*
      blockCount (inputBits n) := rfl
  have hHeader := LightEncodedColorWantedHeader.meets (d := d+1) (μ := μ₂)
    (by rfl : program[253]?=some LightEncodedColorWantedHeader.body) hw (by change wanted ≤ lim.space; omega) cover₂
  light_call hHeader with out μ₃ ⟨hout,hmem⟩
  subst μ₃
  have hout' : out=(wanted : ℤ) := hout
  have wanted2 : ((wanted : ℤ)+2).toNat=wanted+2 := by omega
  have base1 : ((base : ℤ)+1).toNat=base+1 := by omega
  have base8 : ((base : ℤ)+8).toNat=base+8 := by omega
  light_set (base : ℕ) using hout',wanted2,hnext
  light_set (occ : ℕ) using base8,readOcc
  light_set (LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n)) : ℕ) using base1,readS
  light_set (bank : ℕ) using hbankEq
  have hResult := LightEncodedColorResult.meets (d := d+1) (μ := μ₂)
    (prime := prime free n (bandSize n)) (cover := cover) (wanted := wanted) (controls := base) (bank := bank)
    (out := finish) (len := xs.length) (p := p)
    (by rfl : program[254]?=some LightEncodedColorResult.body) hw (by omega) (by omega) (by omega)
    (by omega) (by omega) hfinishSpace hlenWord hpWord
  light_call hResult using hptr,hout',hlast with r ν ⟨hr,finalHeads,keptResult⟩
  have primes₂ := primes.of_kept keptSources le_rfl
  have heads₂ := heads.of_kept keptSources (by simpa [normalizedHeads] using hfree)
  have count₂ : μ₂ (normalizedEnd free n (bandSize n))=(xs.length : ℤ) :=
    (keptSources _ (by unfold prime at hmeta; omega)).trans hcount
  have hkeyEnd : LightCoverKeyData.keyEnd cover (microHalf (inputBits n)) (blockCount (inputBits n)) ≤ finish := by
    have hh : wanted=LightCoverKeyData.keyEnd cover (microHalf (inputBits n)) (blockCount (inputBits n))+3*xs.length := rfl
    omega
  refine ⟨⟨A,hsA,B,hsB,C,hsC,hr,⟨finalHeads,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩,?_⟩
  · exact heads₂.of_kept keptResult (by simpa [normalizedHeads] using (show free+8 ≤ finish by omega))
  · exact (keptResult _ (by unfold prime at hmeta; omega)).trans count₂
  · exact normalized₂.keep keptResult ha hb hc (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
      (by change normalizedEnd free n (bandSize n) ≤ finish; omega)
  · exact primes₂.of_kept keptResult (by change cover ≤ finish; omega)
  · exact cover₂.of_kept (fun i hi => keptResult i (hi.trans_le hkeyEnd))
  · exact EncodedColorWantedData.of_kept wanted₂ keptResult (by change base ≤ finish; omega)
  · simpa only [hlast,base,EncodedColorPipelineData.controls,cover,p,xs,finish,
      EncodedColorPipelineData.finish] using sources.of_kept keptResult le_rfl
  · dsimp only
    rw [keptResult _ (by change wanted < finish; omega)]
    exact countBound
  · apply lifts.of_kept keptResult
    rw [RawAKeyLists.keys_length]
    change wanted ≤ finish
    omega
  · intro i hi
    exact (keptResult i (by omega)).trans ((keptSources i (by omega)).trans (keptPrime i hi))

end ThreeSum.LightEncodedColorPipeline
