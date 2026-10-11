import Submission.ThreeSum.ThreeSumWantedHostReads

namespace ThreeSum.LightThreeSumWantedHost

open Light Scales BandScales ThreeSumReportingSetupData ThreeSumWantedHostData
open BandPartition EncodedColorNormalizedData

set_option maxHeartbeats 5000000
set_option maxRecDepth 20000

local instance (n : ℕ) : NeZero (radix n) := ⟨Nat.ne_of_gt (radix_pos n)⟩

private theorem natAddToNat (a b : ℕ) : ((a : ℤ)+(b : ℤ)).toNat=a+b := by omega

/- The execution lemma deliberately has only numeric controls.  Keeping the
   normalized arrays and source-bank definitions out of this proof avoids
   repeatedly reducing them while checking every individual header read. -/
private theorem header_meets {lim : Limits} {d T : ℕ} {μ : ℕ→ℤ}
    {n params free out ctr report cover controls bank ae bv be cv ce vals recs : ℕ}
    {h J K g R N wanted cnt pairs layers schedule masks owners M NB NC gA gB gC : ℕ}
    {Q : ℤ→(ℕ→ℤ)→Prop}
    (hparams : params+19≤free) (hw : (lim.space : ℤ)≤lim.word)
    (hd : d<lim.depth) (hspace : ctr+50≤lim.space)
    (hreport : report+9≤ctr) (hout : out+8=report) (hfree : free+8≤report)
    (hcover : cover≤report) (hwanted : wanted+4≤controls)
    (hcontrols : controls+3≤out) (hbank : bank+5≤out)
    (hcover20 : cover+20≤masks) (hmasks : masks≤report)
    (hpairs : pairs+2*cnt=controls)
    (hae : ae+2≤cover) (hbv : bv+NB≤cover) (hbe : be+2≤cover)
    (hcv : cv+NC≤cover) (hce : ce+2≤cover) (hrec : recs≤cover)
    (howner : owners≤cover) (hval : vals≤cover)
    (hnB : NB≤n) (hnC : NC≤n) (hGA : gA≤n) (hGB : gB≤n) (hGC : gC≤n)
    (hnword : (n : ℤ)≤lim.word) (hJword : (J : ℤ)≤lim.word)
    (hhword : (h : ℤ)≤lim.word) (hKword : ((K+1 : ℕ) : ℤ)≤lim.word)
    (hgword : (g : ℤ)≤lim.word) (hMword : (M : ℤ)≤lim.word)
    (hlword : (layers : ℤ)≤lim.word) (hsword : (schedule : ℤ)≤lim.word)
    (hRword : (R : ℤ)≤lim.word) (hNword : (N : ℤ)≤lim.word)
    (hReq : R=gB*gC+gA*gB+gA*gC)
    (hownerZ : (vals : ℤ)+(g : ℤ)*(R : ℤ)=(owners : ℤ))
    (readCover : μ (out+1)=(cover : ℤ)) (readWanted : μ (out+2)=(wanted : ℤ))
    (readControls : μ (out+3)=(controls : ℤ)) (readBank : μ (out+4)=(bank : ℤ))
    (readN : μ (out+6)=(N : ℤ)) (readAE : μ (free+1)=(ae : ℤ))
    (readB : μ (free+2)=(bv : ℤ)) (readBE : μ (free+3)=(be : ℤ))
    (readC : μ (free+4)=(cv : ℤ)) (readCE : μ (free+5)=(ce : ℤ))
    (readRecs : μ (free+6)=(recs : ℤ)) (readVals : μ (free+7)=(vals : ℤ))
    (readH : μ (params+1)=(h : ℤ)) (readJ : μ (params+3)=(J : ℤ))
    (readM : μ (params+14)=(M : ℤ)) (readG : μ (params+17)=(g : ℤ))
    (readGA : μ (ae+1)=(gA : ℤ)) (readGB : μ (be+1)=(gB : ℤ))
    (readGC : μ (ce+1)=(gC : ℤ)) (readNB : μ be=(NB : ℤ))
    (readNC : μ ce=(NC : ℤ)) (readCount : μ wanted=(cnt : ℤ))
    (readPairs : μ (wanted+1)=(pairs : ℤ))
    (readLevels : μ (report+2)=((K+1 : ℕ) : ℤ))
    (readLayers : μ cover=(layers : ℤ)) (readSchedule : μ (cover+10)=(schedule : ℤ))
    (readMasks : μ (cover+18)=(masks : ℤ))
    (hscan : Meets lim LightReportingWantedScan.program 152 (d+1)
      [cnt,(ctr+4 : ℕ),J,h,K,N,NB,NC,cover,ctr,pairs,layers,schedule,masks,vals,owners,recs,
        (controls+3 : ℕ),bank,bv,cv,report,M] μ T Q) :
    Meets lim program 153 d [n,params,free,out,ctr] μ (T+4000) Q := by
  have hRsum : (gB : ℤ)*(gC : ℤ)+(gA : ℤ)*(gB : ℤ)+(gA : ℤ)*(gC : ℤ)≤lim.word := by
    simpa only [hReq,Nat.cast_add,Nat.cast_mul] using hRword
  have hBC0 : (0 : ℤ)≤(gB : ℤ)*(gC : ℤ) := by positivity
  have hAB0 : (0 : ℤ)≤(gA : ℤ)*(gB : ℤ) := by positivity
  have hAC0 : (0 : ℤ)≤(gA : ℤ)*(gC : ℤ) := by positivity
  have out1 : ((out : ℤ)+1).toNat=out+1 := natAddToNat out 1
  have out2 : ((out : ℤ)+2).toNat=out+2 := natAddToNat out 2
  have out3 : ((out : ℤ)+3).toNat=out+3 := natAddToNat out 3
  have out4 : ((out : ℤ)+4).toNat=out+4 := natAddToNat out 4
  have out6 : ((out : ℤ)+6).toNat=out+6 := natAddToNat out 6
  have free1 : ((free : ℤ)+1).toNat=free+1 := natAddToNat free 1
  have free2 : ((free : ℤ)+2).toNat=free+2 := natAddToNat free 2
  have free3 : ((free : ℤ)+3).toNat=free+3 := natAddToNat free 3
  have free4 : ((free : ℤ)+4).toNat=free+4 := natAddToNat free 4
  have free5 : ((free : ℤ)+5).toNat=free+5 := natAddToNat free 5
  have free6 : ((free : ℤ)+6).toNat=free+6 := natAddToNat free 6
  have free7 : ((free : ℤ)+7).toNat=free+7 := natAddToNat free 7
  have par1 : ((params : ℤ)+1).toNat=params+1 := natAddToNat params 1
  have par3 : ((params : ℤ)+3).toNat=params+3 := natAddToNat params 3
  have par14 : ((params : ℤ)+14).toNat=params+14 := natAddToNat params 14
  have par17 : ((params : ℤ)+17).toNat=params+17 := natAddToNat params 17
  have report2 : ((report : ℤ)+2).toNat=report+2 := natAddToNat report 2
  have wanted1 : ((wanted : ℤ)+1).toNat=wanted+1 := natAddToNat wanted 1
  have cover10 : ((cover : ℤ)+10).toNat=cover+10 := natAddToNat cover 10
  have cover18 : ((cover : ℤ)+18).toNat=cover+18 := natAddToNat cover 18
  have ae1 : ((ae : ℤ)+1).toNat=ae+1 := natAddToNat ae 1
  have be1 : ((be : ℤ)+1).toNat=be+1 := natAddToNat be 1
  have ce1 : ((ce : ℤ)+1).toNat=ce+1 := natAddToNat ce 1
  apply Meets.of_body (p := 153) (by rfl : program[153]?=some (body 152))
  unfold body
  light_set (ctr+4 : ℕ)
  light_set (J : ℕ) using readJ,par3
  light_set (h : ℕ) using readH,par1
  light_set (report : ℕ) using hout
  light_set (K+1 : ℕ) using readLevels,report2
  light_set (K : ℕ)
  light_set (N : ℕ) using readN,out6
  light_set (ae : ℕ) using readAE,free1
  light_set (be : ℕ) using readBE,free3
  light_set (ce : ℕ) using readCE,free5
  light_set (NB : ℕ) using readNB
  light_set (NC : ℕ) using readNC
  light_set (cover : ℕ) using readCover,out1
  light_set (wanted : ℕ) using readWanted,out2
  light_set (cnt : ℕ) using readCount
  light_set (pairs : ℕ) using readPairs,wanted1
  light_set (layers : ℕ) using readLayers
  light_set (schedule : ℕ) using readSchedule,cover10
  light_set (masks : ℕ) using readMasks,cover18
  light_set (vals : ℕ) using readVals,free7
  light_set (recs : ℕ) using readRecs,free6
  light_set (controls : ℕ) using readControls,out3
  light_set (controls+3 : ℕ)
  light_set (bank : ℕ) using readBank,out4
  light_set (bv : ℕ) using readB,free2
  light_set (cv : ℕ) using readC,free4
  light_set (M : ℕ) using readM,par14
  light_set (g : ℕ) using readG,par17
  light_set (gA : ℕ) using readGA,ae1
  light_set (gB : ℕ) using readGB,be1
  light_set (gC : ℕ) using readGC,ce1
  light_set (R : ℕ) using hReq
  light_set (owners : ℕ) using hownerZ
  have hrun := hscan.append [body 152]
  light_call hrun with result ν hQ
  exact hQ

theorem program_meets {lim : Limits} {d T : ℕ} {μ : ℕ→ℤ} {free n params : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    {Q : ℤ→(ℕ→ℤ)→Prop}
    (H : ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
    (Hparams : Seg μ params (LightParameterInit.values n)) (hparams : params+19≤free)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d<lim.depth)
    (hspace : counter free n A B C hsA hsB hsC+50+2*blockCount (inputBits n)≤lim.space)
    (hword : (word n : ℤ)≤lim.word)
    (hscan : Meets lim LightReportingWantedScan.program 152 (d+1)
      (LightReportingWantedDispatch.arguments (config free n A B C hsA hsB hsC)
        (ThreeSumWantedHostData.count n A B C hsA hsB hsC)) μ T Q) :
    Meets lim program 153 d
      [n,params,free,EncodedColorPipelineData.finish free n A B C hsA hsB hsC,
        counter free n A B C hsA hsB hsC] μ (T+4000) Q := by
  let out := EncodedColorPipelineData.finish free n A B C hsA hsB hsC
  let ctr := counter free n A B C hsA hsB hsC
  let report := reportBase free n A B C hsA hsB hsC
  let cover := EncodedColorPipelineData.coverBase free n
  let controls := EncodedColorPipelineData.controls free n A B C hsA hsB hsC
  let bank := EncodedColorPipelineData.bankHeader free n A B C hsA hsB hsC
  let ae := EncodedColorLayout.ae free n
  let bv := EncodedColorLayout.bv free n
  let be := EncodedColorLayout.be free n
  let cv := EncodedColorLayout.cv free n
  let ce := EncodedColorLayout.ce free n
  let vals := EncodedColorLayout.vals free n (bandSize n)
  let recs := EncodedColorLayout.rec free n (bandSize n)
  let h := microHalf (inputBits n)
  let J := blockCount (inputBits n)
  let K := LightSwitchDepth.depth J
  let g := bandSize n
  let R := recordCount n A B C hsA hsB hsC
  let N := (incidences n A B C hsA hsB hsC).length
  let wanted := EncodedColorPipelineData.wantedHeader free n N
  let cnt := ThreeSumWantedHostData.count n A B C hsA hsB hsC
  let pairs := LightWantedSetup.pairBase wanted (3*N) (LightGuardedWanted.totalKeys h J) (radix n)
  let layers := OutputDecodeRecords.layerCount h
  let schedule := GlobalEncoding.scheduleSize h
  let masks := LightCoverKeys.afterCover cover h
  let owners := LightBandRawA.ownerBase vals R g
  have hreport := report_le_counter free n A B C hsA hsB hsC
  change report+9≤ctr at hreport
  have hout : out+8=report := rfl
  obtain ⟨hfree,hcover⟩ := prefix_le_report free n A B C hsA hsB hsC
  change free+8≤report at hfree
  change cover≤report at hcover
  obtain ⟨_,_,_,hwanted,hcontrols,hbank⟩ := EncodedColorPipelineData.ordered free n A B C hsA hsB hsC
  change wanted+4≤controls at hwanted
  change controls+3≤out at hcontrols
  change bank+5≤out at hbank
  have hcover20 : cover+20≤masks := by
    exact LightLocalCoverRetention.base_le_nextFree (LightLocalCoverInit.base cover) h
  have hmasks := (LightCoverKeyData.afterCover_le_keyEnd cover h J).trans
    (cover_end_le_report free n A B C hsA hsB hsC)
  change masks≤report at hmasks
  have hpairs : pairs+2*cnt=controls := rfl
  obtain ⟨hnA,hnB,hnC⟩ := ThreeSumColorBudgets.normalized_lengths H.encoded
  have hR := EncodedColorNormalizedData.records_length_le (g := g) (hg := bandSize_pos n)
    (hsA := hsA) (hsB := hsB) (hsC := hsC) hnA hnB hnC
  change R≤ColorBandBounds.count n g at hR
  have hN : N≤g*ColorBandBounds.count n g := by
    unfold N incidences
    rw [BandRawA.values_length]
    exact (BandRawA.items_length_le ..).trans (Nat.mul_le_mul_left _ hR)
  obtain ⟨_,hae,hbv,hbe,hcv,hce,_,hrec,hvals⟩ :=
    EncodedColorLayout.normalized_ends_cover free n g (radix n) (primeWindow n)
  change ae+2+2*n≤cover at hae
  change bv+n≤cover at hbv
  change be+2+2*n≤cover at hbe
  change cv+n≤cover at hcv
  change ce+2+2*n≤cover at hce
  change recs+4*ColorBandBounds.count n g≤cover at hrec
  change LightBandRawA.space vals (ColorBandBounds.count n g) g≤cover at hvals
  have howner : owners≤cover := by
    have hh := Nat.mul_le_mul_left g hR
    unfold owners LightBandRawA.ownerBase LightBandRawA.capacity
    unfold LightBandRawA.space LightBandRawA.positionBase LightBandRawA.ownerBase
      LightBandRawA.capacity at hvals
    omega
  have hval : vals≤cover := by
    unfold owners LightBandRawA.ownerBase LightBandRawA.capacity at howner
    omega
  have hbound (z : ℕ) (hz : z≤word n) : (z : ℤ)≤lim.word := (Int.ofNat_le.mpr hz).trans hword
  obtain ⟨wn,wJ,wh,wK,wg,wM,wl,ws,wR,wN⟩ := word_bounds n
  have hnword := hbound n wn
  have hJword := hbound J wJ
  have hhword := hbound h wh
  have hKword := hbound (K+1) wK
  have hgword := hbound g wg
  have hMword := hbound (radix n) wM
  have hlword := hbound layers wl
  have hsword := hbound schedule ws
  have hRword := hbound R (hR.trans wR)
  have hNword := hbound N (hN.trans wN)
  have hGA := size_le A.length g
  have hGB := size_le B.length g
  have hGC := size_le C.length g
  have hReq : R=size B.length g*size C.length g+size A.length g*size B.length g+
      size A.length g*size C.length g := recordCount_eq ..
  have hRsum : (size B.length g : ℤ)*(size C.length g : ℤ)+
      (size A.length g : ℤ)*(size B.length g : ℤ)+(size A.length g : ℤ)*(size C.length g : ℤ)≤lim.word := by
    simpa only [hReq,Nat.cast_add,Nat.cast_mul] using hRword
  have hBC0 : (0 : ℤ)≤(size B.length g : ℤ)*(size C.length g : ℤ) := by positivity
  have hAB0 : (0 : ℤ)≤(size A.length g : ℤ)*(size B.length g : ℤ) := by positivity
  have hAC0 : (0 : ℤ)≤(size A.length g : ℤ)*(size C.length g : ℤ) := by positivity
  have hownerZ : (vals : ℤ)+(g : ℤ)*(R : ℤ)=(owners : ℤ) := by
    simp only [owners,LightBandRawA.ownerBase,LightBandRawA.capacity,Nat.cast_add,Nat.cast_mul]
  obtain ⟨_,readCover,readWanted,readControls,readBank,_,readN,_⟩ := H.encoded.heads_read
  change μ (out+1)=(cover : ℤ) at readCover
  change μ (out+2)=(wanted : ℤ) at readWanted
  change μ (out+3)=(controls : ℤ) at readControls
  change μ (out+4)=(bank : ℤ) at readBank
  change μ (out+6)=(N : ℤ) at readN
  obtain ⟨_,readAE,readB,readBE,readC,readCE,readRecs,readVals⟩ :=
    EncodedColorNormalizedData.heads_read H.encoded.normalizedHeads
  change μ (free+1)=(ae : ℤ) at readAE
  change μ (free+2)=(bv : ℤ) at readB
  change μ (free+3)=(be : ℤ) at readBE
  change μ (free+4)=(cv : ℤ) at readC
  change μ (free+5)=(ce : ℤ) at readCE
  change μ (free+6)=(recs : ℤ) at readRecs
  change μ (free+7)=(vals : ℤ) at readVals
  obtain ⟨_,readH,readJ,_,readM,readG,_⟩ := EncodedColorParameterData.reads Hparams
  change μ (params+1)=(h : ℤ) at readH
  change μ (params+3)=(J : ℤ) at readJ
  change μ (params+17)=(g : ℤ) at readG
  obtain ⟨_,readGA⟩ := SourceFiniteInputs.prepared_headers H.encoded.normalized.2.1
  obtain ⟨readNB,readGB⟩ := SourceFiniteInputs.prepared_headers H.encoded.normalized.2.2.1
  obtain ⟨readNC,readGC⟩ := SourceFiniteInputs.prepared_headers H.encoded.normalized.2.2.2.1
  change μ (ae+1)=(size A.length g : ℤ) at readGA
  change μ (be+1)=(size B.length g : ℤ) at readGB
  change μ (ce+1)=(size C.length g : ℤ) at readGC
  change μ be=(B.length : ℤ) at readNB
  change μ ce=(C.length : ℤ) at readNC
  have readCount : μ wanted=(cnt : ℤ) := count_read H.encoded
  have readPairs : μ (wanted+1)=(pairs : ℤ) := pairs_read H.encoded
  have readLevels : μ (report+2)=((K+1 : ℕ) : ℤ) := report_level_read H.catalog
  obtain ⟨readLayers,readSchedule,readMasks⟩ := cover_header_reads H.encoded.cover
  change μ cover=(layers : ℤ) at readLayers
  change μ (cover+10)=(schedule : ℤ) at readSchedule
  change μ (cover+18)=(masks : ℤ) at readMasks
  change Meets lim LightReportingWantedScan.program 152 (d+1)
    [cnt,(ctr+4 : ℕ),J,h,K,N,B.length,C.length,cover,ctr,pairs,layers,schedule,masks,
      vals,owners,recs,(controls+3 : ℕ),bank,bv,cv,report,radix n] μ T Q at hscan
  exact header_meets hparams hw hd
    ((Nat.le_add_right (ctr+50) (2*J)).trans hspace)
    hreport hout hfree hcover hwanted hcontrols hbank hcover20 hmasks hpairs
    ((Nat.le_add_right (ae+2) (2*n)).trans hae)
    ((Nat.add_le_add_left hnB bv).trans hbv)
    ((Nat.le_add_right (be+2) (2*n)).trans hbe)
    ((Nat.add_le_add_left hnC cv).trans hcv)
    ((Nat.le_add_right (ce+2) (2*n)).trans hce)
    ((Nat.le_add_right recs (4*ColorBandBounds.count n g)).trans hrec)
    howner hval hnB hnC (hGA.trans hnA) (hGB.trans hnB) (hGC.trans hnC)
    hnword hJword hhword hKword hgword hMword hlword hsword hRword hNword hReq hownerZ
    readCover readWanted readControls readBank readN readAE readB readBE readC readCE
    readRecs readVals readH readJ readM readG readGA readGB readGC readNB readNC
    readCount readPairs readLevels readLayers readSchedule readMasks hscan

end ThreeSum.LightThreeSumWantedHost
