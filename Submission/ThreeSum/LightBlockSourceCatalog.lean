import Submission.ThreeSum.LightBlockSourceBatch
import Submission.ThreeSum.LightSourceOccurrenceArray
import Submission.ThreeSum.BlockSourceOccurrenceOrder

/-!
# Constructed occurrence rows and their shared source banks

The first call constructs every big-endian occurrence row from its physical
bank index. The second call builds the two retained original source-stage
families once for that row. Original-band histograms and selected cover data
remain available throughout. No array of complete output records is read.
-/

namespace ThreeSum.LightBlockSourceCatalog

open Light BlockEncoding GlobalEncoding BlockIndex BlockCoefficientRows
open SubsetAddress LocalCoverBounds BlockSourceEncoding LightBlockSourceBatchLayout
open BlockSourceOccurrenceOrder OutputDecodeOrder OutputDecodeRecords

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

def count (h J : ℕ) : ℕ := scheduleSize h^J

def body (pRows pBatch : ℕ) : Stmt :=
  .call pRows [v 16,v 0,v 23,v 7,v 22] 24 ;;
  .call pBatch [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,
    v 14,v 15,v 16,v 17,v 18,v 19,v 20,v 21,v 22] 24

def time (h J cut : ℕ) : ℕ :=
  LightSourceOccurrenceArray.time (count h J) J+
    LightBlockSourceBatch.time (count h J) h J cut+400

def space (base h J cut : ℕ) : ℕ :=
  max (LightBlockSourceRetainedHost.space (work base (count h J) (J*(512*h)) cut) h J)
    (LightOutputDecodeDigits.space (work base (count h J) (J*(512*h)) cut) (count h J))

def word (NL NR h J : ℕ) : ℕ :=
  max (LightBlockSourceRetainedHost.word NL NR h J)
    (LightOutputDecodeDigits.word (count h J) (scheduleSize h) J)

structure Procs (P : Program) (pMain : ℕ) where
  pRows : ℕ
  pDigits : ℕ
  pDivide : ℕ
  pBatch : ℕ
  rows : P[pRows]? = some (LightSourceOccurrenceArray.body pDigits)
  digits : P[pDigits]? = some (LightOutputDecodeDigits.body pDivide)
  divide : P[pDivide]? = some LightOutputDecodeDivide.body
  batch : LightBlockSourceBatch.Procs P pBatch
  main : P[pMain]? = some (body pRows pBatch)

def Stored {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    (μ : ℕ → ℤ) (h J base cut : ℕ) (P shift : ℤ)
    (B : Finset β) (b : β → ℤ) (A : Finset γ) (a : γ → ℤ) : Prop :=
  ∀ i < count h J, LightBlockSourceBatch.BankAt μ base (count h J) cut i P shift B b A a
    (representative h J i)

theorem Stored.decoded {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {μ : ℕ → ℤ} {h J base cut k : ℕ} {P shift : ℤ}
    {B : Finset β} {b : β → ℤ} {A : Finset γ} {a : γ → ℤ}
    (H : Stored μ h J base cut P shift B b A a) (hk : k < localCount h^J) :
    LightBlockSourceBatch.BankAt μ base (count h J) cut
      (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J k)
      P shift B b A a ((GlobalKeyEnumeration.globalRecords h J).getD k (outputDefault h J)) :=
  (H _ (OutputDecodeOccurrenceCode.source_code_lt h J k)).reuse (decoded_occurrences hk)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {h J cut p NL NR occ maps candidates histL histR sourceHistL sourceHistR base : ℕ}
    {shift : ℤ} (B : Finset β) (b : β → ℤ) (A : Finset γ) (a : γ → ℤ)
    (vL vR : ℕ → ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ A)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+12 ≤ lim.depth)
    (hcut : cut ≤ J*(512*h)) (hocc : occ+count h J*J ≤ base)
    (hmaps : maps+2*(512*h)*scheduleSize h ≤ occ)
    (hcandidates : candidates+scheduleSize h ≤ occ)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h ≤ occ)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h ≤ occ)
    (hsourceHistL : sourceHistL+modulus h J ≤ occ)
    (hsourceHistR : sourceHistR+modulus h J ≤ occ)
    (hspace : space base h J cut ≤ lim.space)
    (hword : (word NL NR h J : ℤ) ≤ lim.word)
    (hinputL : ∀ j : Fin NL, vL j.val = b (eL j))
    (hinputR : ∀ j : Fin NR, vR j.val = a (eR j))
    (hhistReadL : ∀ r < modulus h J,
      μ (sourceHistL+r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) 0 vL NL r : ℤ))
    (hhistReadR : ∀ r < modulus h J,
      μ (sourceHistR+r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) shift vR NR r : ℤ))
    (hcover : BlockSourceCoverInput.Input μ h maps candidates histL histR) :
    Meets lim P pMain d
      [J,512*h,h,localPrime h,localBucketCap h,cut,modulus h J,occ,maps,candidates,
        histL,histR,sourceHistL,sourceHistR,base,downsetCap (J*(512*h)) cut,count h J,
        banks base (count h J),stride (J*(512*h)) cut,maskBase base (count h J) (J*(512*h)) cut,
        bitBase base (count h J) (J*(512*h)) cut,rowOut base (count h J) (J*(512*h)) cut,
        work base (count h J) (J*(512*h)) cut,scheduleSize h]
      μ (time h J cut) (fun _ ν =>
        Stored ν h J base cut (p : ℤ) shift B b A a ∧
        (∀ i < count h J, ∀ j < J,
          ν (occ+i*J+j)=((indices (scheduleSize h) J i).getD j 0 : ℤ)) ∧ Kept μ ν occ) := by
  have hs : LightBlockSourceRetainedHost.space (work base (count h J) (J*(512*h)) cut) h J ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hsd : LightOutputDecodeDigits.space (work base (count h J) (J*(512*h)) cut) (count h J) ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hws : (LightBlockSourceRetainedHost.word NL NR h J : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hwd : (LightOutputDecodeDigits.word (count h J) (scheduleSize h) J : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_right _ _)).trans hword
  have hbase : base ≤ work base (count h J) (J*(512*h)) cut := by
    have hb := banks_le_work base (count h J) (J*(512*h)) cut
    unfold banks at hb
    omega
  have hrunRows := LightSourceOccurrenceArray.meets (d := d+1) (μ := μ)
    (N := count h J) (J := J) (m := scheduleSize h) (dst := occ)
    (work := work base (count h J) (J*(512*h)) cut)
    C.rows C.digits C.divide hw (by omega) (by exact schedule_pos h)
    (hocc.trans hbase) hsd hwd
  apply Meets.of_body C.main
  unfold body time
  light_call hrunRows with r ν ⟨rows,kept⟩
  have hcover' := hcover.of_kept kept hmaps hcandidates hleft hright
  have hhistL' : ∀ r < modulus h J,
      ν (sourceHistL+r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) 0 vL NL r : ℤ) := by
    intro r hr
    exact (kept _ (by omega)).trans (hhistReadL r hr)
  have hhistR' : ∀ r < modulus h J,
      ν (sourceHistR+r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) shift vR NR r : ℤ) := by
    intro r hr
    exact (kept _ (by omega)).trans (hhistReadR r hr)
  have hrows : ∀ i < count h J, ∀ j < J,
      ν (occ+i*J+j)=(occurrenceIndices (outputOccurrences (representative h J i)) j : ℤ) := by
    intro i hi j hj
    rw [row_coordinate hj]
    exact rows i hi j hj
  have hrunBatch := C.batch.meets (d := d+1) (μ := ν) (cut := cut) (p := p) (shift := shift)
    (occ := occ) (maps := maps) (candidates := candidates) (histL := histL) (histR := histR)
    (sourceHistL := sourceHistL) (sourceHistR := sourceHistR) (base := base) (count := count h J)
    B b A a (representative h J) vL vR eL eR hw (by omega) hcut hocc
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    hs hws hinputL hinputR hhistL' hhistR' hrows hcover'
  light_call hrunBatch with s ν' ⟨stored,kept'⟩
  refine ⟨stored,?_,?_⟩
  · intro i hi j hj
    have hm := Nat.mul_le_mul_right J (show i+1 ≤ count h J by omega)
    exact (kept' _ (by nlinarith)).trans (rows i hi j hj)
  · intro a ha
    exact (kept' a (by omega)).trans (kept a ha)

end ThreeSum.LightBlockSourceCatalog
