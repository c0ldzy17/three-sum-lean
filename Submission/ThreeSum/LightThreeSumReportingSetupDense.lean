import Submission.ThreeSum.ThreeSumReportingSetupData
import Submission.ThreeSum.LightDenseSetupCosts
import Submission.ThreeSum.EncodedColorStageCosts

/-! # Initialize the actual dense counter using the retained original arrays -/

namespace ThreeSum.LightThreeSumReportingSetupDense

open Light Scales BandScales CostLedger ArithmeticStageBounds ThreeSumReportingSetupData
open BandPartition BandCandidateRows BandRawA

set_option maxHeartbeats 2600000
set_option maxRecDepth 16000

local instance (n : ℕ) : NeZero (radix n) := ⟨Nat.ne_of_gt (radix_pos n)⟩

/-- n, parameter header, normalized header, encoded result header, counter. -/
def body (pDense : ℕ) : Stmt :=
  .set 5 (M (v 3)) ;;
  .set 6 (M (v 3 +' k 1)) ;;
  .set 7 (M (v 3 +' k 7)) ;;
  .set 8 (M (v 2)) ;;
  .set 9 (M (v 2 +' k 1)) ;;
  .set 10 (M (v 2 +' k 2)) ;;
  .set 11 (M (v 2 +' k 3)) ;;
  .set 12 (M (v 2 +' k 4)) ;;
  .set 13 (M (v 2 +' k 5)) ;;
  .set 14 (M (v 2 +' k 6)) ;;
  .set 15 (M (v 9)) ;;
  .set 16 (M (v 11)) ;;
  .set 17 (M (v 13)) ;;
  .set 18 (M (v 9 +' k 1)) ;;
  .set 19 (M (v 11 +' k 1)) ;;
  .set 20 (M (v 13 +' k 1)) ;;
  .set 21 (v 19 *' v 20 +' v 18 *' v 19 +' v 18 *' v 20) ;;
  .set 22 (M (v 1 +' k 17)) ;;
  .set 23 (M (v 1 +' k 3)) ;;
  .set 24 (M (v 5 +' k 3)) ;;
  .set 25 (M (v 5 +' k 4)) ;;
  .call pDense [v 8,v 10,v 12,v 15,v 16,v 17,v 22,v 14,v 21,v 7,v 24,v 25,v 6,v 23,v 4] 0

def program : Program := LightDenseSetup.program++[body 19]

theorem program_length : program.length=21 := rfl

def time (n U R : ℕ) : ℕ :=
  LightDenseSetup.time (maxMod n) (bandSize n) R (LightPrimePool.size (primeWindow n))
    U (blockCount (inputBits n))+1600

def word (n U : ℕ) : ℕ :=
  LightDenseSetup.word (maxMod n) n n n (bandSize n) (ColorBandBounds.count n (bandSize n))
    (LightPrimePool.size (primeWindow n)) U (microHalf (inputBits n)) (blockCount (inputBits n))+
    n+bandSize n+blockCount (inputBits n)+ColorBandBounds.count n (bandSize n)+maxMod n+
    LightPrimePool.size (primeWindow n)+20

theorem dense_word_le {n nA nB nC R U : ℕ}
    (hA : nA ≤ n) (hB : nB ≤ n) (hC : nC ≤ n) (hR : R ≤ ColorBandBounds.count n (bandSize n)) :
    LightDenseSetup.word (maxMod n) nA nB nC (bandSize n) R
      (LightPrimePool.size (primeWindow n)) U (microHalf (inputBits n)) (blockCount (inputBits n)) ≤ word n U := by
  apply le_trans (b := LightDenseSetup.word (maxMod n) n n n (bandSize n)
    (ColorBandBounds.count n (bandSize n)) (LightPrimePool.size (primeWindow n)) U
    (microHalf (inputBits n)) (blockCount (inputBits n)))
  · unfold LightDenseSetup.word LightBandWeightedScore.word LightBandWeightedScoreCell.word
    gcongr
  · unfold word
    omega

theorem program_meets {lim : Limits} {d : ℕ} {μ : ℕ → ℤ} {free n params U dst : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (Hparams : Seg μ params (LightParameterInit.values n)) (hparams : params+19 ≤ free)
    (hw : (lim.space : ℤ) ≤ lim.word) (hR : 4 ≤ radix n)
    (hprior : reportBase free n A B C hsA hsB hsC ≤ dst)
    (hspace : LightWeightedScore.space (dst+4) (maxMod n) (bandSize n) U ≤ lim.space)
    (hword : (word n U : ℤ) ≤ lim.word)
    (hdepth : d+Nat.clog 2 (maxMod n)+8 ≤ lim.depth)
    (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    Meets lim program 20 d
      [n,params,free,EncodedColorPipelineData.finish free n A B C hsA hsB hsC,dst] μ
      (time n U (sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC).length)
      (fun r ν => r=(dst : ℤ) ∧
        LightDenseSetup.Stored ν dst
          (GlobalEncoding.representationCap (microHalf (inputBits n)) (blockCount (inputBits n)))
          (ThreeSumColorBudgets.falseScore n A B C hsA hsB hsC) ∧
        EncodedColorPipelineData.Stored ν free n color x A B C hsA hsB hsC ∧ Kept μ ν dst) := by
  let out := EncodedColorPipelineData.finish free n A B C hsA hsB hsC
  let primeHeader := EncodedColorLayout.prime free n (bandSize n)
  let cover := EncodedColorPipelineData.coverBase free n
  let p := EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC
  let av := EncodedColorLayout.av free n
  let ae := EncodedColorLayout.ae free n
  let bv := EncodedColorLayout.bv free n
  let be := EncodedColorLayout.be free n
  let cv := EncodedColorLayout.cv free n
  let ce := EncodedColorLayout.ce free n
  let recs := EncodedColorLayout.rec free n (bandSize n)
  let rs := sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC
  let g := bandSize n
  let J := blockCount (inputBits n)
  let aux := EncodedColorPrimeData.poolBase primeHeader
  let s := LightPrimePool.size (primeWindow n)
  have hdst : dst+4 ≤ lim.space := by
    have hh := (le_max_right _ _).trans hspace
    change dst+4+(Nat.log 2 (maxMod n+1)+2) ≤ lim.space at hh
    omega
  obtain ⟨hnA,hnB,hnC⟩ := ThreeSumColorBudgets.normalized_lengths H
  have hrecords := EncodedColorNormalizedData.records_length_le (g := g) (hg := bandSize_pos n)
    (hsA := hsA) (hsB := hsB) (hsC := hsC) hnA hnB hnC
  change rs.length ≤ ColorBandBounds.count n g at hrecords
  have hrs : rs.length=LightEncodedColorPrime.count A.length B.length C.length g := by
    simp only [rs,sortedRecords,records_length]
    rfl
  have hbound (z : ℕ) (hz : z ≤ word n U) : (z : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hz).trans hword
  have hnWord := hbound n (by unfold word; omega)
  have hgWord := hbound g (by unfold word; omega)
  have hJWord := hbound J (by unfold word; omega)
  have hPWord := hbound (maxMod n) (by unfold word; omega)
  have hsWord := hbound s (by unfold word; omega)
  have hcountWord := hbound rs.length (hrecords.trans (by
    change ColorBandBounds.count n (bandSize n) ≤ word n U
    unfold word
    omega))
  have hDenseWord := hbound _ (dense_word_le hnA hnB hnC hrecords)
  have hpmax : p ≤ maxMod n := EncodedColorStageCosts.selected_le_maxMod hR
  have hpWord : (p : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hpmax).trans hPWord
  have hGA := size_le A.length g
  have hGB := size_le B.length g
  have hGC := size_le C.length g
  have hcountZ : (size B.length g : ℤ)*(size C.length g : ℤ)+
      (size A.length g : ℤ)*(size B.length g : ℤ)+(size A.length g : ℤ)*(size C.length g : ℤ) ≤ lim.word := by
    simpa only [hrs,LightEncodedColorPrime.count,Nat.cast_add,Nat.cast_mul] using hcountWord
  have hBC0 : (0 : ℤ) ≤ (size B.length g : ℤ)*(size C.length g : ℤ) := by positivity
  have hAB0 : (0 : ℤ) ≤ (size A.length g : ℤ)*(size B.length g : ℤ) := by positivity
  have hAC0 : (0 : ℤ) ≤ (size A.length g : ℤ)*(size C.length g : ℤ) := by positivity
  have hprefix := prefix_le_report free n A B C hsA hsB hsC
  obtain ⟨hmeta,_,_,_,_,_⟩ := EncodedColorPipelineData.ordered free n A B C hsA hsB hsC
  change primeHeader+6 ≤ cover at hmeta
  have hcover : cover ≤ dst := hprefix.2.trans hprior
  have hfree : free+8 ≤ dst := hprefix.1.trans hprior
  have hout : out+8 ≤ dst := hprior
  have hkey := (cover_end_le_report free n A B C hsA hsB hsC).trans hprior
  have haux := (pool_end_le_report free n A B C hsA hsB hsC).trans hprior
  obtain ⟨hav,hae,hbv,hbe,hcv,hce,_,hrec,_⟩ :=
    EncodedColorLayout.normalized_ends_cover free n g (radix n) (primeWindow n)
  change av+n ≤ cover at hav
  change ae+2+2*n ≤ cover at hae
  change bv+n ≤ cover at hbv
  change be+2+2*n ≤ cover at hbe
  change cv+n ≤ cover at hcv
  change ce+2+2*n ≤ cover at hce
  change recs+4*ColorBandBounds.count n g ≤ cover at hrec
  obtain ⟨readMeta,readCover,_,_,_,_,_,readP⟩ := H.heads_read
  change μ out=(primeHeader : ℤ) at readMeta
  change μ (out+1)=(cover : ℤ) at readCover
  change μ (out+7)=(p : ℤ) at readP
  obtain ⟨readA,readAE,readB,readBE,readC,readCE,readRecs,_⟩ :=
    EncodedColorNormalizedData.heads_read H.normalizedHeads
  change μ free=(av : ℤ) at readA
  change μ (free+1)=(ae : ℤ) at readAE
  change μ (free+2)=(bv : ℤ) at readB
  change μ (free+3)=(be : ℤ) at readBE
  change μ (free+4)=(cv : ℤ) at readC
  change μ (free+5)=(ce : ℤ) at readCE
  change μ (free+6)=(recs : ℤ) at readRecs
  obtain ⟨_,_,_,readAux,readS,_⟩ := H.primes.heads_read
  change μ (primeHeader+3)=(aux : ℤ) at readAux
  change μ (primeHeader+4)=(s : ℤ) at readS
  obtain ⟨_,_,readJ,_,_,readG,_⟩ := EncodedColorParameterData.reads Hparams
  change μ (params+3)=(J : ℤ) at readJ
  change μ (params+17)=(g : ℤ) at readG
  obtain ⟨readNA,readGA⟩ := SourceFiniteInputs.prepared_headers H.normalized.2.1
  obtain ⟨readNB,readGB⟩ := SourceFiniteInputs.prepared_headers H.normalized.2.2.1
  obtain ⟨readNC,readGC⟩ := SourceFiniteInputs.prepared_headers H.normalized.2.2.2.1
  change μ ae=(A.length : ℤ) at readNA
  change μ be=(B.length : ℤ) at readNB
  change μ ce=(C.length : ℤ) at readNC
  change μ (ae+1)=(size A.length g : ℤ) at readGA
  change μ (be+1)=(size B.length g : ℤ) at readGB
  change μ (ce+1)=(size C.length g : ℤ) at readGC
  have hvalueA := SourceFiniteInputs.prepared_read H.normalized.2.1
  have hvalueB := SourceFiniteInputs.prepared_read H.normalized.2.2.1
  have hvalueC := SourceFiniteInputs.prepared_read H.normalized.2.2.2.1
  obtain ⟨hA,hB,hC⟩ := ThreeSumColorBudgets.normalized_values H hx
  have hproduct : ∀ i < s, p*LightPrimePool.prime (primeWindow n) i ≤ maxMod n := by
    intro i hi
    have hp := (BandPrimeScales.modulus_bounds n A.length B.length C.length
      (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0) rs).2
    change p ≤ (4*primeWindow n)^primeDepth radix n at hp
    exact (Nat.mul_le_mul hp (LightPrimePool.prime_spec hi).2.2).trans
      (by simpa only [← pow_succ] using BandPrimeScales.resource_modulus_bound hR)
  have hread : ∀ i < s, μ (aux+i)=(LightPrimePool.prime (primeWindow n) i : ℤ) :=
    fun i hi => H.primes.pool.read hi
  have hflags : ∀ r ∈ rs, r.flag=0 ∨ r.flag=1 := fun _ hr => records_flag hr
  have hvalid : ∀ r ∈ rs, r.flag=1 → r.a*g ≤ A.length ∧ r.b*g ≤ B.length ∧ r.c*g ≤ C.length :=
    LightBandPrimeStage.records_valid rfl rfl rfl (bandSize_pos n)
  have out1 : ((out : ℤ)+1).toNat=out+1 := by omega
  have out7 : ((out : ℤ)+7).toNat=out+7 := by omega
  have free1 : ((free : ℤ)+1).toNat=free+1 := by omega
  have free2 : ((free : ℤ)+2).toNat=free+2 := by omega
  have free3 : ((free : ℤ)+3).toNat=free+3 := by omega
  have free4 : ((free : ℤ)+4).toNat=free+4 := by omega
  have free5 : ((free : ℤ)+5).toNat=free+5 := by omega
  have free6 : ((free : ℤ)+6).toNat=free+6 := by omega
  have ae1 : ((ae : ℤ)+1).toNat=ae+1 := by omega
  have be1 : ((be : ℤ)+1).toNat=be+1 := by omega
  have ce1 : ((ce : ℤ)+1).toNat=ce+1 := by omega
  have par3 : ((params : ℤ)+3).toNat=params+3 := by omega
  have par17 : ((params : ℤ)+17).toNat=params+17 := by omega
  have prime3 : ((primeHeader : ℤ)+3).toNat=primeHeader+3 := by omega
  have prime4 : ((primeHeader : ℤ)+4).toNat=primeHeader+4 := by omega
  change Meets lim program 20 d [n,params,free,out,dst] μ (time n U rs.length) _
  apply Meets.of_body (p := 20) (by rfl : program[20]?=some (body 19))
  unfold body time
  light_set (primeHeader : ℕ) using readMeta
  light_set (cover : ℕ) using readCover,out1
  light_set (p : ℕ) using readP,out7
  light_set (av : ℕ) using readA
  light_set (ae : ℕ) using readAE,free1
  light_set (bv : ℕ) using readB,free2
  light_set (be : ℕ) using readBE,free3
  light_set (cv : ℕ) using readC,free4
  light_set (ce : ℕ) using readCE,free5
  light_set (recs : ℕ) using readRecs,free6
  light_set (A.length : ℕ) using readNA
  light_set (B.length : ℕ) using readNB
  light_set (C.length : ℕ) using readNC
  light_set (size A.length g : ℕ) using readGA,ae1
  light_set (size B.length g : ℕ) using readGB,be1
  light_set (size C.length g : ℕ) using readGC,ce1
  light_set (rs.length : ℕ) using hrs,LightEncodedColorPrime.count
  light_set (g : ℕ) using readG,par17
  light_set (J : ℕ) using readJ,par3
  light_set (aux : ℕ) using readAux,prime3
  light_set (s : ℕ) using readS,prime4
  have hcall := (LightDenseSetup.program_meets (d := d+1) (μ := μ)
    (a := av) (b := bv) (c := cv) (nA := A.length) (nB := B.length) (nC := C.length)
    (g := g) (recs := recs) (q := p) (aux := aux) (s := s) (cover := cover) (free := dst)
    (maxMod := maxMod n) (U := U) (h := microHalf (inputBits n)) (J := J)
    (LightPrimePool.prime (primeWindow n)) rs hw (by omega) (bandSize_pos n)
    EncodedColorPrimeReadyData.selected_pos hpmax (by omega) (by omega) (by omega)
    (by omega) haux hkey hspace hDenseWord H.cover H.normalized.2.2.2.2.2.1 hflags hvalid
    (fun i hi => by rw [hvalueA i hi]; exact hA i hi)
    (fun i hi => by rw [hvalueB i hi]; exact hB i hi)
    (fun i hi => by rw [hvalueC i hi]; exact hC i hi)
    hread (fun _ hi => (LightPrimePool.prime_spec hi).1)
    (fun _ hi _ hj he => LightPrimePool.prime_injective hi hj he) hproduct).append [body 19]
  light_call hcall using g,J,s with result ν ⟨hresult,hdense,_,hkeep⟩
  have hscore : LightDenseSetup.falseScore (LightPrimePool.prime (primeWindow n)) s p
      A.length B.length C.length g (fun i => μ (av+i)) (fun i => μ (bv+i)) (fun i => μ (cv+i)) rs=
      ThreeSumColorBudgets.falseScore n A B C hsA hsB hsC := by
    unfold ThreeSumColorBudgets.falseScore
    rw [LightDenseSetup.falseScore_eq,LightDenseSetup.falseScore_eq]
    exact BandWeightedScore.score_congr rs hvalueA hvalueB hvalueC
  rw [hscore] at hdense
  exact ⟨hresult,hdense,H.of_kept hkeep hprior,hkeep⟩

theorem time_le_budget {n R : ℕ} (k : ℕ) (hn : 0 < n) (hR : R ≤ 3*bandCount n^2) :
    time n (n^k) R ≤ LightDenseSetupCosts.timeBudget k n+1600 :=
  Nat.add_le_add_right (LightDenseSetupCosts.time_le_budget k hn hR) 1600

end ThreeSum.LightThreeSumReportingSetupDense
