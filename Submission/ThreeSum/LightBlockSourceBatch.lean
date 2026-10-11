import Submission.ThreeSum.LightBlockSourceBatchStep
import Submission.ThreeSum.BlockSourceSharing

/-!
# Actual shared source-stage catalog over occurrence vectors

One loop iteration constructs one retained bank and its two header pointers.
The original-band histograms and local-cover data are read throughout and
preserved. The semantic occurrence-row contract labels an ordinary physical
array; it does not assume any source-stage computation or output-subset loop.
-/

namespace ThreeSum.LightBlockSourceBatch

open Light BlockEncoding GlobalEncoding BlockIndex BlockCoefficientRows
open SubsetAddress LocalCoverBounds BlockSourceEncoding LightBlockSourceBatchLayout

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

structure BankAt {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {h J : ℕ} (μ : ℕ → ℤ) (base count cut i : ℕ) (P shift : ℤ)
    (B : Finset β) (b : β → ℤ) (A : Finset γ) (a : γ → ℤ) (q : GlobalOutput h J) : Prop where
  left : LightZetaStages.StoredThrough μ (leftBase base count (J*(512*h)) cut i) cut
    (BlockIndexedQuery.leftSource P B b q) (J*(512*h))
  right : LightZetaStages.StoredThrough μ (rightBase base count (J*(512*h)) cut i) cut
    (BlockIndexedQuery.rightSource P shift A a q) (J*(512*h))
  headerLeft : μ (base+2*i) = (leftBase base count (J*(512*h)) cut i : ℤ)
  headerRight : μ (base+2*i+1) = (rightBase base count (J*(512*h)) cut i : ℤ)

theorem BankAt.of_later {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {h J base count cut i k : ℕ} {μ ν : ℕ → ℤ} {P shift : ℤ}
    {B : Finset β} {b : β → ℤ} {A : Finset γ} {a : γ → ℤ} {q : GlobalOutput h J}
    (H : BankAt μ base count cut i P shift B b A a q)
    (K : KeptBut μ ν (slot base count (J*(512*h)) cut k) (base+2*k) 2)
    (hik : i < k) (hk : k < count) : BankAt ν base count cut i P shift B b A a q := by
  have hhead := header_end_le_slot (base := base) (W := J*(512*h)) (cut := cut) hk
  refine ⟨?_,?_,?_,?_⟩
  · intro j hj S hS
    have hb := banks_le_left_cell base count (J*(512*h)) cut i j S
    unfold banks at hb
    exact (K _ ⟨left_cell_lt_later hik hj hS,Or.inr (by omega)⟩).trans (H.left j hj S hS)
  · intro j hj S hS
    have hb := banks_le_right_cell base count (J*(512*h)) cut i j S
    unfold banks at hb
    exact (K _ ⟨right_cell_lt_later hik hj hS,Or.inr (by omega)⟩).trans (H.right j hj S hS)
  · exact (K _ ⟨by omega,Or.inl (by omega)⟩).trans H.headerLeft
  · exact (K _ ⟨by omega,Or.inl (by omega)⟩).trans H.headerRight

theorem BankAt.reuse {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {h J base count cut i : ℕ} {μ : ℕ → ℤ} {P shift : ℤ}
    {B : Finset β} {b : β → ℤ} {A : Finset γ} {a : γ → ℤ} {q q' : GlobalOutput h J}
    (H : BankAt μ base count cut i P shift B b A a q)
    (ho : outputOccurrences q = outputOccurrences q') :
    BankAt μ base count cut i P shift B b A a q' :=
  ⟨BlockSourceSharing.stored_left_reuse P B b ho H.left,
    BlockSourceSharing.stored_right_reuse P shift A a ho H.right,H.headerLeft,H.headerRight⟩

def body (pStep : ℕ) : Stmt :=
  .for 23 (v 16) (
    .call pStep [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7 +' v 23 *' v 0,
      v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,v 17,v 18,v 19,v 20,v 21,v 22,v 23] 24)

def time (count h J cut : ℕ) : ℕ := count*(LightBlockSourceBatchStep.time h J cut+200)+20

structure Procs (P : Program) (pMain : ℕ) where
  pStep : ℕ
  step : LightBlockSourceBatchStep.Procs P pStep
  main : P[pMain]? = some (body pStep)

def Inv {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    (μ : ℕ → ℤ) (h J cut occ maps candidates histL histR sourceHistL sourceHistR base count : ℕ)
    (p shift : ℤ) (B : Finset β) (b : β → ℤ) (A : Finset γ) (a : γ → ℤ)
    (q : ℕ → GlobalOutput h J) (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [J,512*h,h,localPrime h,localBucketCap h,cut,modulus h J,occ,maps,candidates,
      histL,histR,sourceHistL,sourceHistR,base,downsetCap (J*(512*h)) cut,count,
      banks base count,stride (J*(512*h)) cut,maskBase base count (J*(512*h)) cut,
      bitBase base count (J*(512*h)) cut,rowOut base count (J*(512*h)) cut,
      work base count (J*(512*h)) cut,i,r],ν⟩ ∧
    (∀ j < i, BankAt ν base count cut j p shift B b A a (q j)) ∧ Kept μ ν base

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {h J cut p NL NR occ maps candidates histL histR sourceHistL sourceHistR
      base count : ℕ} {shift : ℤ}
    (B : Finset β) (b : β → ℤ) (A : Finset γ) (a : γ → ℤ)
    (q : ℕ → GlobalOutput h J) (vL vR : ℕ → ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ A)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+11 ≤ lim.depth)
    (hcut : cut ≤ J*(512*h))
    (hocc : occ+count*J ≤ base) (hmaps : maps+2*(512*h)*scheduleSize h ≤ base)
    (hcandidates : candidates+scheduleSize h ≤ base)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h ≤ base)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h ≤ base)
    (hsourceHistL : sourceHistL+modulus h J ≤ base)
    (hsourceHistR : sourceHistR+modulus h J ≤ base)
    (hspace : LightBlockSourceRetainedHost.space (work base count (J*(512*h)) cut) h J ≤ lim.space)
    (hword : (LightBlockSourceRetainedHost.word NL NR h J : ℤ) ≤ lim.word)
    (hinputL : ∀ j : Fin NL, vL j.val = b (eL j))
    (hinputR : ∀ j : Fin NR, vR j.val = a (eR j))
    (hhistReadL : ∀ r < modulus h J,
      μ (sourceHistL+r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) 0 vL NL r : ℤ))
    (hhistReadR : ∀ r < modulus h J,
      μ (sourceHistR+r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) shift vR NR r : ℤ))
    (hoccRead : ∀ i < count, ∀ j < J,
      μ (occ+i*J+j) = (occurrenceIndices (outputOccurrences (q i)) j : ℤ))
    (hcover : BlockSourceCoverInput.Input μ h maps candidates histL histR) :
    Meets lim P pMain d
      [J,512*h,h,localPrime h,localBucketCap h,cut,modulus h J,occ,maps,candidates,
        histL,histR,sourceHistL,sourceHistR,base,downsetCap (J*(512*h)) cut,count,
        banks base count,stride (J*(512*h)) cut,maskBase base count (J*(512*h)) cut,
        bitBase base count (J*(512*h)) cut,rowOut base count (J*(512*h)) cut,
        work base count (J*(512*h)) cut]
      μ (time count h J cut) (fun _ ν =>
        (∀ i < count, BankAt ν base count cut i (p : ℤ) shift B b A a (q i)) ∧ Kept μ ν base) := by
  have hs : work base count (J*(512*h)) cut+(J*(512*h)+1) ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hbase : base ≤ lim.space := by
    have hb := banks_le_work base count (J*(512*h)) cut
    unfold banks at hb
    omega
  have hcount : count ≤ lim.space := by
    have hb := banks_le_work base count (J*(512*h)) cut
    unfold banks at hb
    omega
  apply Meets.of_body C.main
  unfold body time
  refine Ends.for (Inv μ h J cut occ maps candidates histL histR sourceHistL sourceHistR base count
    (p : ℤ) shift B b A a q) count (LightBlockSourceBatchStep.time h J cut+192)
    ?start ?round ?done ?bound
  case start =>
    refine ⟨0,μ,?_,?_,fun _ _ => rfl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : State))
        ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro j hj; omega
  case round =>
    rintro i _ hi _ ⟨r,ν,rfl,written,kept⟩
    have hrow : occ+i*J+J ≤ base := by
      have hm := Nat.mul_le_mul_right J (show i+1 ≤ count by omega)
      nlinarith
    have hprodNat : i*J ≤ lim.space := by omega
    have hprod : (i : ℤ)*(J : ℤ) ≤ lim.word :=
      (by exact_mod_cast hprodNat : (i : ℤ)*(J : ℤ) ≤ lim.space).trans hw
    have hprodNonneg : (0 : ℤ) ≤ (i : ℤ)*(J : ℤ) := by positivity
    have hcover' := hcover.of_kept kept hmaps hcandidates hleft hright
    have hhistL' : ∀ r < modulus h J,
        ν (sourceHistL+r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) 0 vL NL r : ℤ) := by
      intro r hr
      exact (kept _ (by omega)).trans (hhistReadL r hr)
    have hhistR' : ∀ r < modulus h J,
        ν (sourceHistR+r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) shift vR NR r : ℤ) := by
      intro r hr
      exact (kept _ (by omega)).trans (hhistReadR r hr)
    have hocc' : ∀ j < J, ν (occ+i*J+j) =
        (occurrenceIndices (outputOccurrences (q i)) j : ℤ) := by
      intro j hj
      exact (kept _ (by omega)).trans (hoccRead i hi j hj)
    have hrun := C.step.meets (d := d+1) (μ := ν) (cut := cut) (p := p) (shift := shift)
      (occ := occ+i*J) (maps := maps) (candidates := candidates) (histL := histL) (histR := histR)
      (sourceHistL := sourceHistL) (sourceHistR := sourceHistR) (base := base) (count := count) (i := i)
      B b A a (q i) vL vR eL eR hw (by omega) hcut hi hrow hmaps hcandidates hleft hright
      hsourceHistL hsourceHistR hspace hword hinputL hinputR hhistL' hhistR' hocc' hcover'
    light_call hrun with s ν' ⟨storedL,storedR,headL,headR,kept'⟩
    refine ⟨by simp,s,ν',by simp [update_frame_setLocal],?_,?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact (written j hj).of_later kept' hj hi
      · exact ⟨storedL,storedR,headL,headR⟩
    · intro a ha
      have hb := banks_le_slot base count (J*(512*h)) cut i
      unfold banks at hb
      exact (kept' a ⟨by omega,Or.inl (by omega)⟩).trans (kept a ha)
  case done =>
    rintro _ _ ⟨r,ν,rfl,written,kept⟩
    exact ⟨written,kept⟩
  case bound =>
    rintro i _ _ _ ⟨r,ν,rfl,_,_⟩
    simp

end ThreeSum.LightBlockSourceBatch
