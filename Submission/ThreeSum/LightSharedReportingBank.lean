import Submission.ThreeSum.LightSharedReportingPair
import Submission.ThreeSum.SharedReportingBankRows

/-!
# One actual shared catalog bank in occurrence, B-band, C-band order

One flat loop has exactly S*nb*nc rounds. Three scalar carry counters give
the occurrence and two independent bands, with C varying fastest. No
quotient, output-subset, lift, or A-incidence loop is used to enumerate
these shared rows. All earlier metadata and payloads remain retained.
-/

namespace ThreeSum.LightSharedReportingBank

open Light GlobalEncoding SharedReportingBankLayout SharedReportingBankLevels
open SharedReportingBankRows

set_option maxHeartbeats 3800000
set_option maxRecDepth 16000

/-- h,J,K,source first/span,S,nb,nc,H,E,metadata base,payload base. -/
def body (pPair : ℕ) : Stmt :=
  .set 17 (v 5 *' v 6 *' v 7) ;;
  .set 12 (k 0) ;;
  .set 13 (k 0) ;;
  .set 14 (k 0) ;;
  .set 15 (v 10) ;;
  .set 16 (v 11) ;;
  .for 18 (v 17) (
    .call pPair [v 0,v 1,v 2,v 3,v 4,v 12,v 13,v 14,v 8,v 9,v 15,v 16] 16 ;;
    .set 16 (v 16) ;;
    .set 15 (v 15 +' k 5 *' v 2) ;;
    .ite (v 14 +' k 1 <' v 7)
      (.set 14 (v 14 +' k 1))
      (.set 14 (k 0) ;;
        .ite (v 13 +' k 1 <' v 6)
          (.set 13 (v 13 +' k 1))
          (.set 13 (k 0) ;; .set 12 (v 12 +' k 1)))) ;;
  .set 0 (v 16)

def time (h J K NB NC g : ℕ) : ℕ :=
  total h J NB NC g*(LightSharedReportingPair.time h J K+1000)+300

def controlWord (h J K NB NC g : ℕ) : ℕ :=
  LightBlockSourceCatalog.count h J*BandPartition.size NB g+
  LightBlockSourceCatalog.count h J+BandPartition.size NB g+BandPartition.size NC g+J+K+512

def program : Program := LightSharedReportingPair.program ++ [body 65]
theorem program_length : program.length=67 := rfl

def Inv (μ : ℕ → ℤ) (fB fC : ℕ → ℤ) (p shift : ℤ)
    (header record base h J K NB NC g q : ℕ) (σ : State) : Prop :=
  ∃ (s i j : ℕ) (ν : ℕ → ℤ),
    σ=⟨frame [h,J,K,SourceBandBankData.first header,SourceBandBankLayout.span h J (2*h*J),
      LightBlockSourceCatalog.count h J,BandPartition.size NB g,BandPartition.size NC g,
      localChoose h,localPairs h,record,base,s,i,j,rowRecord record K q,rowBase base h J K q,
      total h J NB NC g,q],ν⟩ ∧
    q=rank (BandPartition.size NB g) (BandPartition.size NC g) s i j ∧
    s ≤ LightBlockSourceCatalog.count h J ∧ i ≤ BandPartition.size NB g ∧ j ≤ BandPartition.size NC g ∧
    (0 < total h J NB NC g → i < BandPartition.size NB g ∧ j < BandPartition.size NC g) ∧
    Done ν record base h J K NB NC g q fB fC p shift ∧ Kept μ ν record ∧
    KeptBut μ ν base record (5*K*total h J NB NC g)

theorem program_meets {lim : Limits} {μ : ℕ → ℤ} {fB fC : ℕ → ℤ}
    {header record base NB NC g h J K occ d : ℕ} {p shift : ℤ}
    (H : SourceBandBankData.Stored μ fB fC header NB NC g h J (2*h*J) occ p shift)
    (hw : (lim.space : ℤ) ≤ lim.word) (hKpos : 0 < K)
    (hK : K ≤ LightSwitchDepth.depth J+1)
    (hocc : occ+LightBlockSourceCatalog.count h J*J ≤ header)
    (hsource : SourceBandBankData.finish header NB NC g h J (2*h*J) ≤ record)
    (hslab : record+5*K*total h J NB NC g ≤ base)
    (hspace : rowBase base h J K (total h J NB NC g) ≤ lim.space)
    (hword : (controlWord h J K NB NC g : ℤ) ≤ lim.word)
    (R : ∀ q < total h J NB NC g,
      LightSharedReportingLevels.Resources lim (rowBase base h J K q) h J K g g (d+2)) :
    Meets lim program 66 d
      [h,J,K,SourceBandBankData.first header,SourceBandBankLayout.span h J (2*h*J),
        LightBlockSourceCatalog.count h J,BandPartition.size NB g,BandPartition.size NC g,
        localChoose h,localPairs h,record,base] μ (time h J K NB NC g)
      (fun result ν => result=(rowBase base h J K (total h J NB NC g) : ℤ) ∧
        Done ν record base h J K NB NC g (total h J NB NC g) fB fC p shift ∧
        Kept μ ν record ∧ KeptBut μ ν base record (5*K*total h J NB NC g)) := by
  have hbase : base ≤ lim.space := (Nat.le_add_right _ _).trans hspace
  have hP : total h J NB NC g ≤ lim.space := by
    have hh := Nat.le_mul_of_pos_left (total h J NB NC g) (show 0 < 5*K by omega)
    omega
  have hPWord : (total h J NB NC g : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hP).trans hw
  have hcontrol := hword
  unfold controlWord at hcontrol
  have hpOne : (LightBlockSourceCatalog.count h J : ℤ)*(BandPartition.size NB g : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (show LightBlockSourceCatalog.count h J*BandPartition.size NB g ≤ controlWord h J K NB NC g by
      unfold controlWord; omega)).trans hword
  have hpOneNZ : (0 : ℤ) ≤ (LightBlockSourceCatalog.count h J : ℤ)*(BandPartition.size NB g : ℤ) := by positivity
  have hpTwo : (LightBlockSourceCatalog.count h J : ℤ)*(BandPartition.size NB g : ℤ)*
      (BandPartition.size NC g : ℤ) ≤ lim.word := by
    simpa only [total,pairs,Nat.cast_mul] using hPWord
  have hpTwoNZ : (0 : ℤ) ≤ (LightBlockSourceCatalog.count h J : ℤ)*(BandPartition.size NB g : ℤ)*
      (BandPartition.size NC g : ℤ) := by positivity
  apply Meets.of_body (p := 66) (by rfl : program[66]?=some (body 65))
  unfold body time
  light_set (total h J NB NC g : ℕ) using total,pairs
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  light_set (record : ℕ)
  light_set (base : ℕ)
  refine Ends.pieceThen (Ends.for
    (T := total h J NB NC g*(LightSharedReportingPair.time h J K+1000)+6)
    (Q := Inv μ fB fC p shift header record base h J K NB NC g (total h J NB NC g))
    (Inv μ fB fC p shift header record base h J K NB NC g)
    (total h J NB NC g) (LightSharedReportingPair.time h J K+992)
    ?start ?round ?done ?bound) ?finish
  case start =>
    refine ⟨0,0,0,μ,?_,by simp [rank],by omega,by omega,by omega,?_,Done.empty _ _ _ _ _ _ _ _ _ _ _ _ _,
      SameOn.refl,fun _ _ => rfl⟩
    · simp [update_frame_setLocal,rowRecord,rowBase]
    · intro hp
      constructor
      · by_contra hz
        have he : BandPartition.size NB g=0 := by omega
        simp [total,pairs,he] at hp
      · by_contra hz
        have he : BandPartition.size NC g=0 := by omega
        simp [total,pairs,he] at hp
  case round =>
    rintro q _ hq _ ⟨s,i,j,ν,rfl,hrank,hs,hi,hj,hstrict,built,kept,keptBlock⟩
    obtain ⟨hi',hj'⟩ := hstrict (by omega)
    have hs' : s < LightBlockSourceCatalog.count h J :=
      occurrence_lt (by rw [← hrank]; exact hq)
    have hsourceNow := H.of_kept kept hocc hsource
    have hR := R q hq
    have hdepth := hR.widthDepth
    have hsource' : SourceBandBankData.finish header NB NC g h J (2*h*J) ≤ rowRecord record K q :=
      hsource.trans (Nat.le_add_right _ _)
    have hmeta := Nat.mul_le_mul_left (5*K) (show q+1 ≤ total h J NB NC g by omega)
    have hrecordNext : rowRecord record K q+5*K ≤ base := by unfold rowRecord; nlinarith
    have hrecordRow : rowRecord record K q+5*K ≤ rowBase base h J K q :=
      hrecordNext.trans (Nat.le_add_right _ _)
    have hnextSpace := (rowBase_mono base h J K (show q+1 ≤ total h J NB NC g by omega)).trans hspace
    have hcurrent : rowBase base h J K q ≤ lim.space :=
      (rowBase_mono base h J K (show q ≤ total h J NB NC g by omega)).trans hspace
    have hrecEq := rowRecord_succ record K q
    have hc := (LightSharedReportingPair.program_meets (d := d+1) (record := rowRecord record K q)
      (base := rowBase base h J K q) hsourceNow hs'
      (hi'.trans_le (le_max_left _ _)) (hj'.trans_le (le_max_right _ _))
      hw hK hsource' hrecordRow hR).append [body 65]
    light_call hc with result ν₁ ⟨hresult,hrow,hkeepRow,hkeepRowBlock⟩
    light_set (rowBase base h J K (q+1) : ℕ) using hresult,rowBase_next
    light_set (rowRecord record K (q+1) : ℕ) using rowRecord_succ
    have hdone := built.append hs' hi' hj' hrank hrow hkeepRowBlock hslab
    have hkeep : Kept μ ν₁ record := by
      intro a ha
      exact (hkeepRow a (ha.trans_le (Nat.le_add_right _ _))).trans (kept a ha)
    have hkeepBlock : KeptBut μ ν₁ base record (5*K*total h J NB NC g) := by
      intro a ⟨ha,hout⟩
      have hb : base ≤ rowBase base h J K q := Nat.le_add_right _ _
      have hr : record ≤ rowRecord record K q := Nat.le_add_right _ _
      have hrecTotal : rowRecord record K q+5*K ≤ record+5*K*total h J NB NC g := by
        unfold rowRecord
        nlinarith
      exact (hkeepRowBlock a ⟨by omega,by rcases hout with h | h <;> omega⟩).trans
        (keptBlock a ⟨ha,hout⟩)
    have hfinal (s' i' j' : ℕ) (hS : s' ≤ LightBlockSourceCatalog.count h J)
        (hI : i' < BandPartition.size NB g) (hJ : j' < BandPartition.size NC g)
        (he : q+1=rank (BandPartition.size NB g) (BandPartition.size NC g) s' i' j') :
        let σ : State := ⟨frame [h,J,K,SourceBandBankData.first header,SourceBandBankLayout.span h J (2*h*J),
          LightBlockSourceCatalog.count h J,BandPartition.size NB g,BandPartition.size NC g,
          localChoose h,localPairs h,record,base,s',i',j',rowRecord record K (q+1),
          rowBase base h J K (q+1),total h J NB NC g,q],ν₁⟩
        σ.loc 18=(q : ℤ) ∧ Inv μ fB fC p shift header record base h J K NB NC g (q+1)
          {σ with loc := Function.update σ.loc 18 ((q : ℤ)+1)} := by
      refine ⟨by simp,s',i',j',ν₁,by simp [update_frame_setLocal],he,hS,hI.le,hJ.le,
        fun _ => ⟨hI,hJ⟩,hdone,hkeep,hkeepBlock⟩
    light_if hjNext hjNext : (j : ℤ)+1 < (BandPartition.size NC g : ℤ)
    · have hjn : j+1 < BandPartition.size NC g := by exact_mod_cast hjNext
      light_set (j+1 : ℕ)
      simpa [update_frame_setLocal] using hfinal s i (j+1) hs hi' hjn
        (by rw [rank_next_c,← hrank])
    · have hjLast : j+1=BandPartition.size NC g := by omega
      light_set (0 : ℕ)
      light_if hiNext hiNext : (i : ℤ)+1 < (BandPartition.size NB g : ℤ)
      · have hin : i+1 < BandPartition.size NB g := by exact_mod_cast hiNext
        light_set (i+1 : ℕ)
        simpa [update_frame_setLocal] using hfinal s (i+1) 0 hs hin (by omega)
          (by rw [rank_next_b hjLast,← hrank])
      · have hiLast : i+1=BandPartition.size NB g := by omega
        light_set (0 : ℕ)
        light_set (s+1 : ℕ)
        simpa [update_frame_setLocal] using hfinal (s+1) 0 0 (by omega) (by omega) (by omega)
          (by rw [rank_next_s hiLast hjLast,← hrank])
  case done =>
    rintro _ _ ⟨s,i,j,ν,rfl,hrank,hs,hi,hj,hstrict,built,kept,keptBlock⟩
    exact ⟨s,i,j,ν,rfl,hrank,hs,hi,hj,hstrict,built,kept,keptBlock⟩
  case bound =>
    rintro q _ _ _ ⟨s,i,j,ν,rfl,_,_,_,_,_,_,_,_⟩
    light_side
  case finish =>
    rintro _ ⟨s,i,j,ν,rfl,_,_,_,_,_,built,kept,keptBlock⟩
    light_set (rowBase base h J K (total h J NB NC g) : ℕ)
    exact ⟨rfl,built,kept,keptBlock⟩

end ThreeSum.LightSharedReportingBank
