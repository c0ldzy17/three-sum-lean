import Submission.ThreeSum.LightSourceBandBankBatch
import Submission.ThreeSum.SourceBandBankData
import Submission.ThreeSum.LightSourceOccurrenceArray

/-!
# One occurrence catalog reused across all original source bands

The physical B/C band counts determine the loop length. A single radix
decoder loop constructs the occurrence rows. The bank loop then selects
retained histograms and builds exactly two families per common band and
occurrence. The result header stores the first bank base, band count, band
stride, next free address, and occurrence-row pointer.
-/

namespace ThreeSum.LightSourceBandBanks

open Light GlobalEncoding BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds SubsetAddress BlockSourceOccurrenceOrder SourceBandBankLayout SourceBandBankData

set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

def afterCountBody (pRows pBanks : ℕ) : Stmt :=
  .set 19 (v 13 +' k 5) ;;
  .set 20 (v 19 +' v 18 *' v 17) ;;
  .call pRows [v 15,v 0,v 16,v 7,v 20] 21 ;;
  .store (v 13) (v 19) ;;
  .store (v 13 +' k 1) (v 18) ;;
  .store (v 13 +' k 2) (v 17) ;;
  .store (v 13 +' k 3) (v 20) ;;
  .store (v 13 +' k 4) (v 7) ;;
  .call pBanks [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,
    v 19,v 14,v 15,v 18,v 17] 21 ;;
  .set 0 (v 20)

def body (pRows pBanks : ℕ) : Stmt :=
  .set 18 (M (v 12 +' k 1)) ;;
  .ite (v 18 <' M (v 12 +' k 3)) (.set 18 (M (v 12 +' k 3))) .skip ;;
  afterCountBody pRows pBanks

def afterTime (NL NR g h J cut : ℕ) : ℕ :=
  LightSourceOccurrenceArray.time (LightBlockSourceCatalog.count h J) J+
    LightSourceBandBankBatch.time NL NR g h J cut+1000

def time (NL NR g h J cut : ℕ) : ℕ :=
  LightSourceOccurrenceArray.time (LightBlockSourceCatalog.count h J) J+
    LightSourceBandBankBatch.time NL NR g h J cut+1200

def space (base NL NR g h J cut : ℕ) : ℕ :=
  max (LightOutputDecodeDigits.space (finish base NL NR g h J cut) (LightBlockSourceCatalog.count h J))
    (span h J cut)

def word (NL NR h J : ℕ) : ℕ :=
  max (LightSourceBandBankStep.word NL NR h J)
    (LightOutputDecodeDigits.word (LightBlockSourceCatalog.count h J) (scheduleSize h) J)

structure Procs (P : Program) (pMain : ℕ) where
  pRows : ℕ
  pDigits : ℕ
  pDivide : ℕ
  pBanks : ℕ
  rows : P[pRows]?=some (LightSourceOccurrenceArray.body pDigits)
  digits : P[pDigits]?=some (LightOutputDecodeDigits.body pDivide)
  divide : P[pDivide]?=some LightOutputDecodeDivide.body
  banks : LightSourceBandBankBatch.Procs P pBanks
  main : P[pMain]?=some (body pRows pBanks)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem afterCount_ends {pRows pDigits pDivide pBanks : ℕ}
    (hrows : P[pRows]?=some (LightSourceOccurrenceArray.body pDigits))
    (hdigits : P[pDigits]?=some (LightOutputDecodeDigits.body pDivide))
    (hdivide : P[pDivide]?=some LightOutputDecodeDivide.body)
    (C : LightSourceBandBankBatch.Procs P pBanks)
    {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {pair NL NR g p h J cut occ maps candidates histL histR base K : ℕ}
    {shift : ℤ} (H : SourceBandPairData.Stored μ fL fR pair NL NR g p (modulus h J) shift)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+14 ≤ lim.depth)
    (hg : 0 < g) (hcut : cut ≤ J*(512*h)) (hK : K=SourceBandPairSlices.count NL NR g)
    (hpair : SourceBandPairData.next pair NL NR g (modulus h J) ≤ occ)
    (hocc : occ+LightBlockSourceCatalog.count h J*J ≤ base)
    (hmaps : maps+2*(512*h)*scheduleSize h ≤ occ)
    (hcandidates : candidates+scheduleSize h ≤ occ)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h ≤ occ)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h ≤ occ)
    (hspace : space base NL NR g h J cut ≤ lim.space)
    (hword : (word NL NR h J : ℤ) ≤ lim.word)
    (hcover : BlockSourceCoverInput.Input μ h maps candidates histL histR) :
    Ends lim P d (afterCountBody pRows pBanks)
      ⟨frame [J,512*h,h,localPrime h,localBucketCap h,cut,modulus h J,occ,maps,candidates,histL,histR,
        pair,base,downsetCap (J*(512*h)) cut,LightBlockSourceCatalog.count h J,scheduleSize h,span h J cut,K],μ⟩
      (afterTime NL NR g h J cut) (fun σ =>
        σ.loc 0=(finish base NL NR g h J cut : ℤ) ∧
        Stored σ.mem fL fR base NL NR g h J cut occ (p : ℤ) shift ∧ Kept μ σ.mem occ) := by
  subst K
  have hm := modulus_pos h J
  have hsRows : LightOutputDecodeDigits.space (finish base NL NR g h J cut) (LightBlockSourceCatalog.count h J) ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hsSpan : span h J cut ≤ lim.space := (le_max_right _ _).trans hspace
  have hs : finish base NL NR g h J cut ≤ lim.space := by unfold LightOutputDecodeDigits.space at hsRows; omega
  have hfirst : first base ≤ finish base NL NR g h J cut := Nat.le_add_right _ _
  have hbase : base+5 ≤ lim.space := hfirst.trans hs
  have hwBanks : (LightSourceBandBankStep.word NL NR h J : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hwRows : (LightOutputDecodeDigits.word (LightBlockSourceCatalog.count h J) (scheduleSize h) J : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_right _ _)).trans hword
  have hNL := BandPartition.size_le NL g
  have hNR := BandPartition.size_le NR g
  have hcount : SourceBandPairSlices.count NL NR g ≤ NL+NR := by unfold SourceBandPairSlices.count; omega
  have hcountWord : (SourceBandPairSlices.count NL NR g : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show SourceBandPairSlices.count NL NR g ≤ LightSourceBandBankStep.word NL NR h J by
      unfold LightSourceBandBankStep.word; omega)).trans hwBanks
  have h32 : (32 : ℤ) ≤ lim.word := by unfold LightSourceBandBankStep.word at hwBanks; omega
  have hendAddr : (first base : ℤ)+(SourceBandPairSlices.count NL NR g : ℤ)*(span h J cut : ℤ) ≤ lim.word :=
    (by exact_mod_cast hs : (first base : ℤ)+(SourceBandPairSlices.count NL NR g : ℤ)*(span h J cut : ℤ) ≤ lim.space).trans hw
  have hendNonneg : (0 : ℤ) ≤ (SourceBandPairSlices.count NL NR g : ℤ)*(span h J cut : ℤ) := by positivity
  unfold afterCountBody afterTime
  light_set (first base : ℕ) using first
  light_set (finish base NL NR g h J cut : ℕ) using finish,baseAt
  have hrunRows := LightSourceOccurrenceArray.meets (d := d+1) (μ := μ)
    (N := LightBlockSourceCatalog.count h J) (J := J) (m := scheduleSize h) (dst := occ)
    (work := finish base NL NR g h J cut) hrows hdigits hdivide hw (by omega)
    (OutputDecodeRecords.schedule_pos h) (by unfold first at hfirst; omega) hsRows hwRows
  light_call hrunRows with r ν₁ ⟨rows,keptRows⟩
  light_store base (first base : ℕ)
  light_store (base+1) (SourceBandPairSlices.count NL NR g : ℕ)
  light_store (base+2) (span h J cut : ℕ)
  light_store (base+3) (finish base NL NR g h J cut : ℕ)
  light_store (base+4) (occ : ℕ)
  let ν₂ := Function.update (Function.update (Function.update (Function.update (Function.update ν₁ base
    (first base : ℤ)) (base+1) (SourceBandPairSlices.count NL NR g : ℤ)) (base+2) (span h J cut : ℤ))
    (base+3) (finish base NL NR g h J cut : ℤ)) (base+4) (occ : ℤ)
  have keptHeads : Kept ν₁ ν₂ base := by
    intro a ha
    dsimp only [ν₂]
    repeat' rw [Function.update_of_ne (by omega)]
  have headData : Seg ν₂ base (header base NL NR g h J cut occ) := by
    intro i hi
    have hi' : i < 5 := by simpa only [header,List.length_cons,List.length_nil] using hi
    interval_cases i <;> simp [ν₂,header]
  have H₁ := H.of_kept hm keptRows hpair
  have H₂ := H₁.of_kept hm keptHeads (by omega)
  have cover₁ := hcover.of_kept keptRows hmaps hcandidates hleft hright
  have cover₂ := cover₁.of_kept keptHeads (by omega) (by omega) (by omega) (by omega)
  have rows₂ : ∀ k < LightBlockSourceCatalog.count h J, ∀ j < J,
      ν₂ (occ+k*J+j)=((OutputDecodeOrder.indices (scheduleSize h) J k).getD j 0 : ℤ) := by
    intro k hk j hj
    have hp := Nat.mul_le_mul_right J (show k+1 ≤ LightBlockSourceCatalog.count h J by omega)
    exact (keptHeads _ (by nlinarith)).trans (rows k hk j hj)
  have occurrenceRows : ∀ k < LightBlockSourceCatalog.count h J, ∀ j < J,
      ν₂ (occ+k*J+j)=(occurrenceIndices (outputOccurrences (representative h J k)) j : ℤ) := by
    intro k hk j hj
    rw [row_coordinate hj]
    exact rows₂ k hk j hj
  have hrunBanks := C.meets (d := d+1) (μ := ν₂) (base := first base)
    H₂ hw (by omega) hg hcut (by unfold first; omega) (by unfold first; omega)
    (by unfold first; omega) (by unfold first; omega) (by unfold first; omega) (by unfold first; omega)
    hs hwBanks occurrenceRows cover₂
  light_call hrunBanks with result ν₃ ⟨banks,keptBanks⟩
  light_set (finish base NL NR g h J cut : ℕ)
  refine ⟨rfl,⟨?_,banks,?_⟩,?_⟩
  · intro i hi
    have hi' : i < 5 := by simpa only [header,List.length_cons,List.length_nil] using hi
    exact (keptBanks _ (by unfold first; omega)).trans (headData i hi)
  · intro k hk j hj
    have hp := Nat.mul_le_mul_right J (show k+1 ≤ LightBlockSourceCatalog.count h J by omega)
    exact (keptBanks _ (by unfold first; nlinarith)).trans (rows₂ k hk j hj)
  · intro a ha
    exact (keptBanks a (by unfold first; omega)).trans
      ((keptHeads a (by omega)).trans (keptRows a ha))

theorem Procs.meets {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {pair NL NR g p h J cut occ maps candidates histL histR base : ℕ}
    {shift : ℤ} (H : SourceBandPairData.Stored μ fL fR pair NL NR g p (modulus h J) shift)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+14 ≤ lim.depth)
    (hg : 0 < g) (hcut : cut ≤ J*(512*h))
    (hpair : SourceBandPairData.next pair NL NR g (modulus h J) ≤ occ)
    (hocc : occ+LightBlockSourceCatalog.count h J*J ≤ base)
    (hmaps : maps+2*(512*h)*scheduleSize h ≤ occ)
    (hcandidates : candidates+scheduleSize h ≤ occ)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h ≤ occ)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h ≤ occ)
    (hspace : space base NL NR g h J cut ≤ lim.space)
    (hword : (word NL NR h J : ℤ) ≤ lim.word)
    (hcover : BlockSourceCoverInput.Input μ h maps candidates histL histR) :
    Meets lim P pMain d
      [J,512*h,h,localPrime h,localBucketCap h,cut,modulus h J,occ,maps,candidates,histL,histR,
        pair,base,downsetCap (J*(512*h)) cut,LightBlockSourceCatalog.count h J,scheduleSize h,span h J cut]
      μ (time NL NR g h J cut) (fun r ν =>
        r=(finish base NL NR g h J cut : ℤ) ∧
        Stored ν fL fR base NL NR g h J cut occ (p : ℤ) shift ∧ Kept μ ν occ) := by
  obtain ⟨_,hcountL,_,hcountR,_⟩ := SourceBandPairSlices.heads_read H
  have hsRows : LightOutputDecodeDigits.space (finish base NL NR g h J cut) (LightBlockSourceCatalog.count h J) ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hs : finish base NL NR g h J cut ≤ lim.space := by unfold LightOutputDecodeDigits.space at hsRows; omega
  have hfirst : first base ≤ finish base NL NR g h J cut := Nat.le_add_right _ _
  have hbaseSpace : base+5 ≤ lim.space := hfirst.trans hs
  have ho := SourceBandPairData.ordered pair NL NR g (modulus h J)
  have hhead : pair+8 ≤ base := by unfold SourceBandPairData.leftBase at ho; omega
  have hwBanks : (LightSourceBandBankStep.word NL NR h J : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hNL := BandPartition.size_le NL g
  have hNR := BandPartition.size_le NR g
  have hcountWordL : (BandPartition.size NL g : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show BandPartition.size NL g ≤ LightSourceBandBankStep.word NL NR h J by
      unfold LightSourceBandBankStep.word; omega)).trans hwBanks
  have hcountWordR : (BandPartition.size NR g : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show BandPartition.size NR g ≤ LightSourceBandBankStep.word NL NR h J by
      unfold LightSourceBandBankStep.word; omega)).trans hwBanks
  have h32 : (32 : ℤ) ≤ lim.word := by unfold LightSourceBandBankStep.word at hwBanks; omega
  have haddr1 : ((pair : ℤ)+1).toNat=pair+1 := by omega
  have haddr3 : ((pair : ℤ)+3).toNat=pair+3 := by omega
  have htime : afterTime NL NR g h J cut=
      LightSourceOccurrenceArray.time (LightBlockSourceCatalog.count h J) J+
        LightSourceBandBankBatch.time NL NR g h J cut+1000 := rfl
  apply Meets.of_body C.main
  unfold body time
  light_set (BandPartition.size NL g : ℕ) using hcountL,haddr1
  light_if hy hn : (BandPartition.size NL g : ℤ) < (BandPartition.size NR g : ℤ) using hcountR,haddr3
  · have hK : BandPartition.size NR g=SourceBandPairSlices.count NL NR g := by
      unfold SourceBandPairSlices.count
      omega
    light_set (BandPartition.size NR g : ℕ) using hcountR,haddr3
    light_piece (afterCount_ends C.rows C.digits C.divide C.banks H hw hd hg hcut hK
      hpair hocc hmaps hcandidates hleft hright hspace hword hcover)
  · have hK : BandPartition.size NL g=SourceBandPairSlices.count NL NR g := by
      unfold SourceBandPairSlices.count
      omega
    light_piece (afterCount_ends C.rows C.digits C.divide C.banks H hw hd hg hcut hK
      hpair hocc hmaps hcandidates hleft hright hspace hword hcover)

end ThreeSum.LightSourceBandBanks
