import Submission.ThreeSum.LightSourceBandHistSelect
import Submission.ThreeSum.SourceBandBankLayout

/-! # Construct every occurrence bank for one common original-band index -/

namespace ThreeSum.LightSourceBandBankStep

open Light GlobalEncoding BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds SubsetAddress LightBlockSourceBatchLayout BlockSourceOccurrenceOrder

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

/-- The twelve retained-source controls and cover pointers, pair catalog,
output bank base, compact capacity, occurrence count, and common band index. -/
def body (pSelect pBatch : ℕ) : Stmt :=
  .call pSelect [v 12,v 16,v 13] 17 ;;
  .set 18 (v 0 *' v 1) ;;
  .set 19 (k 5 *' v 14 +' k 2 *' v 18 +' k 2 +' k 2 *' (v 18 +' k 1) *' v 14) ;;
  .set 20 (v 13 +' k 2 *' v 15) ;;
  .set 21 (v 20 +' v 15 *' v 19) ;;
  .set 22 (v 21 +' v 14) ;;
  .set 23 (v 22 +' v 18) ;;
  .set 24 (v 23 +' k 2) ;;
  .call pBatch [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,
    M (v 13),M (v 13 +' k 1),v 13,v 14,v 15,v 20,v 19,v 21,v 22,v 23,v 24] 25

def time (h J cut : ℕ) : ℕ := LightBlockSourceBatch.time (LightBlockSourceCatalog.count h J) h J cut+1500

def word (NL NR h J : ℕ) : ℕ := LightBlockSourceRetainedHost.word NL NR h J+2*NL+2*NR+32

structure Procs (P : Program) (pMain : ℕ) where
  pSelect : ℕ
  pBatch : ℕ
  select : P[pSelect]?=some LightSourceBandHistSelect.body
  batch : LightBlockSourceBatch.Procs P pBatch
  main : P[pMain]?=some (body pSelect pBatch)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {pair NL NR g p h J cut occ maps candidates histL histR base i : ℕ}
    {shift : ℤ} (H : SourceBandPairData.Stored μ fL fR pair NL NR g p (modulus h J) shift)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+12 ≤ lim.depth)
    (hg : 0 < g) (hi : i < SourceBandPairSlices.count NL NR g) (hcut : cut ≤ J*(512*h))
    (hpair : SourceBandPairData.next pair NL NR g (modulus h J) ≤ base)
    (hocc : occ+LightBlockSourceCatalog.count h J*J ≤ base)
    (hmaps : maps+2*(512*h)*scheduleSize h ≤ base)
    (hcandidates : candidates+scheduleSize h ≤ base)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h ≤ base)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h ≤ base)
    (hspace : LightBlockSourceRetainedHost.space
      (work base (LightBlockSourceCatalog.count h J) (J*(512*h)) cut) h J ≤ lim.space)
    (hword : (word NL NR h J : ℤ) ≤ lim.word)
    (hoccRead : ∀ k < LightBlockSourceCatalog.count h J, ∀ j < J,
      μ (occ+k*J+j)=(occurrenceIndices (outputOccurrences (representative h J k)) j : ℤ))
    (hcover : BlockSourceCoverInput.Input μ h maps candidates histL histR) :
    Meets lim P pMain d
      [J,512*h,h,localPrime h,localBucketCap h,cut,modulus h J,occ,maps,candidates,histL,histR,
        pair,base,downsetCap (J*(512*h)) cut,LightBlockSourceCatalog.count h J,i]
      μ (time h J cut) (fun _ ν =>
        LightBlockSourceCatalog.Stored ν h J base cut (p : ℤ) shift
          (SourceBandPartition.source NL g i) (fun t : Fin NL => fL t.val)
          (SourceBandPartition.source NR g i) (fun t : Fin NR => fR t.val) ∧ Kept μ ν base) := by
  have hm := modulus_pos h J
  have hc : 0 < LightBlockSourceCatalog.count h J := pow_pos (OutputDecodeRecords.schedule_pos h) J
  have hs : work base (LightBlockSourceCatalog.count h J) (J*(512*h)) cut+(J*(512*h)+1) ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hwork : work base (LightBlockSourceCatalog.count h J) (J*(512*h)) cut ≤ lim.space := by omega
  have hbanks := banks_le_work base (LightBlockSourceCatalog.count h J) (J*(512*h)) cut
  have hbanksAddr : (base : ℤ)+2*(LightBlockSourceCatalog.count h J : ℤ) ≤ lim.word :=
    (by exact_mod_cast hbanks.trans hwork :
      (base : ℤ)+2*(LightBlockSourceCatalog.count h J : ℤ) ≤ lim.space).trans hw
  have hbase2 : base+2 ≤ lim.space := by unfold banks at hbanks; omega
  have hNL := BandPartition.size_le NL g
  have hNR := BandPartition.size_le NR g
  have hiN : i ≤ NL+NR := by unfold SourceBandPairSlices.count at hi; omega
  have hselWord : ((NL+NR+i+6 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word; omega)).trans hword
  have hsWord : (LightBlockSourceRetainedHost.word NL NR h J : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word; omega)).trans hword
  have h32 : (32 : ℤ) ≤ lim.word := by unfold word at hword; omega
  have hwidth : (J : ℤ)*(512*(h : ℤ)) ≤ lim.word :=
    (by exact_mod_cast (show J*(512*h) ≤ lim.space by omega) :
      (J : ℤ)*(512*(h : ℤ)) ≤ lim.space).trans hw
  have hwidthNonneg : (0 : ℤ) ≤ (J : ℤ)*(512*(h : ℤ)) := by positivity
  have hwidthPlus : (J*(512*h) : ℤ)+1 ≤ lim.word := by
    exact (by exact_mod_cast (show J*(512*h)+1 ≤ lim.space by omega) :
      (J*(512*h) : ℤ)+1 ≤ lim.space).trans hw
  have hstrideN : stride (J*(512*h)) cut ≤ lim.space := by
    have hp := Nat.le_mul_of_pos_left (stride (J*(512*h)) cut) hc
    rw [BlockSourceCatalogCosts.work_address] at hwork
    nlinarith
  have hstrideExpr : 5*downsetCap (J*(512*h)) cut+2*(J*(512*h))+2+
      2*(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ lim.space := by
    simpa only [stride,family,Nat.mul_assoc] using hstrideN
  have hstrideZ : (5 : ℤ)*(downsetCap (J*(512*h)) cut : ℤ)+2*(J*(512*h) : ℤ)+2+
      2*((J*(512*h) : ℤ)+1)*(downsetCap (J*(512*h)) cut : ℤ) ≤ lim.word :=
    (by exact_mod_cast hstrideExpr :
      (5 : ℤ)*(downsetCap (J*(512*h)) cut : ℤ)+2*(J*(512*h) : ℤ)+2+
        2*((J*(512*h) : ℤ)+1)*(downsetCap (J*(512*h)) cut : ℤ) ≤ lim.space).trans hw
  have hcapNonneg : (0 : ℤ) ≤ (downsetCap (J*(512*h)) cut : ℤ) := Int.natCast_nonneg _
  have hfamNonneg : (0 : ℤ) ≤ 2*((J*(512*h) : ℤ)+1)*(downsetCap (J*(512*h)) cut : ℤ) := by positivity
  have hfamilyNonneg : (0 : ℤ) ≤ ((J*(512*h) : ℤ)+1)*(downsetCap (J*(512*h)) cut : ℤ) := by positivity
  have hstrideAssoc : (5 : ℤ)*(downsetCap (J*(512*h)) cut : ℤ)+2*(J*(512*h) : ℤ)+2+
      2*(((J*(512*h) : ℤ)+1)*(downsetCap (J*(512*h)) cut : ℤ)) ≤ lim.word := by
    simpa only [mul_assoc] using hstrideZ
  have hmask := masks_le_work base (LightBlockSourceCatalog.count h J) (J*(512*h)) cut
  have hmaskAddr : (banks base (LightBlockSourceCatalog.count h J) : ℤ)+
      (LightBlockSourceCatalog.count h J : ℤ)*(stride (J*(512*h)) cut : ℤ) ≤ lim.word :=
    (by exact_mod_cast hmask.trans hwork :
      (banks base (LightBlockSourceCatalog.count h J) : ℤ)+
        (LightBlockSourceCatalog.count h J : ℤ)*(stride (J*(512*h)) cut : ℤ) ≤ lim.space).trans hw
  have hmaskProdNonneg : (0 : ℤ) ≤
      (LightBlockSourceCatalog.count h J : ℤ)*(stride (J*(512*h)) cut : ℤ) := by positivity
  have hbits : maskBase base (LightBlockSourceCatalog.count h J) (J*(512*h)) cut+
      downsetCap (J*(512*h)) cut ≤ lim.space := by unfold work rowOut bitBase at hwork; omega
  have hrow : bitBase base (LightBlockSourceCatalog.count h J) (J*(512*h)) cut+J*(512*h) ≤ lim.space := by
    unfold work rowOut at hwork
    omega
  have hrowZ : (bitBase base (LightBlockSourceCatalog.count h J) (J*(512*h)) cut : ℤ)+
      (J*(512*h) : ℤ) ≤ lim.word := (by exact_mod_cast hrow :
        (bitBase base (LightBlockSourceCatalog.count h J) (J*(512*h)) cut : ℤ)+(J*(512*h) : ℤ) ≤ lim.space).trans hw
  have hworkN : rowOut base (LightBlockSourceCatalog.count h J) (J*(512*h)) cut+2 ≤ lim.space := hwork
  have hsrcL := (SourceBandPairSlices.left_end pair NL NR g (modulus h J) i).trans hpair
  have hsrcR := (SourceBandPairSlices.right_end pair NL NR g (modulus h J) i).trans hpair
  apply Meets.of_body C.main
  unfold body time
  light_call (LightSourceBandHistSelect.meets (d := d+1) C.select H hw hm hpair hbase2 hselWord)
    with unused ν ⟨headL,headR,kept⟩
  light_set (J*(512*h) : ℕ)
  light_set (stride (J*(512*h)) cut : ℕ) using stride,family,mul_assoc
  light_set (banks base (LightBlockSourceCatalog.count h J) : ℕ) using banks
  light_set (maskBase base (LightBlockSourceCatalog.count h J) (J*(512*h)) cut : ℕ) using maskBase,slot
  light_set (bitBase base (LightBlockSourceCatalog.count h J) (J*(512*h)) cut : ℕ) using bitBase
  light_set (rowOut base (LightBlockSourceCatalog.count h J) (J*(512*h)) cut : ℕ) using rowOut
  light_set (work base (LightBlockSourceCatalog.count h J) (J*(512*h)) cut : ℕ) using work
  have H' := H.of_kept hm kept hpair
  have hcover' := hcover.of_kept kept hmaps hcandidates hleft hright
  have hrows : ∀ k < LightBlockSourceCatalog.count h J, ∀ j < J,
      ν (occ+k*J+j)=(occurrenceIndices (outputOccurrences (representative h J k)) j : ℤ) := by
    intro k hk j hj
    have hp := Nat.mul_le_mul_right J (show k+1 ≤ LightBlockSourceCatalog.count h J by omega)
    exact (kept _ (by nlinarith)).trans (hoccRead k hk j hj)
  have hlenL := (SourceBandLayout.len_le_cap NL g i).trans (min_le_left _ _)
  have hlenR := (SourceBandLayout.len_le_cap NR g i).trans (min_le_left _ _)
  have hword' := (Int.ofNat_le.mpr (SourceBandBankLayout.word_mono (h := h) (J := J) hlenL hlenR)).trans hsWord
  have hrun := C.batch.meets (d := d+1) (μ := ν) (cut := cut) (p := p) (shift := shift)
    (occ := occ) (maps := maps) (candidates := candidates) (histL := histL) (histR := histR)
    (sourceHistL := SourceBandPairSlices.histLeft pair NL NR g (modulus h J) i)
    (sourceHistR := SourceBandPairSlices.histRight pair NL NR g (modulus h J) i)
    (base := base) (count := LightBlockSourceCatalog.count h J)
    (SourceBandPartition.source NL g i) (fun t : Fin NL => fL t.val)
    (SourceBandPartition.source NR g i) (fun t : Fin NR => fR t.val) (representative h J)
    (fun j => fL (BandPartition.start g i+j)) (fun j => fR (BandPartition.start g i+j))
    (SourceBandPartition.equiv NL g i) (SourceBandPartition.equiv NR g i)
    hw (by omega) hcut hocc hmaps hcandidates hleft hright hsrcL hsrcR hspace hword'
    (fun _ => rfl) (fun _ => rfl)
    (SourceBandPairSlices.left_histogram H'.toData hg)
    (SourceBandPairSlices.right_histogram H'.toData hg) hrows hcover'
  light_call hrun using headL,headR with result ν' ⟨stored,kept'⟩
  exact ⟨stored,fun a ha => (kept' a ha).trans (kept a ha)⟩

end ThreeSum.LightSourceBandBankStep
