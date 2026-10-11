import Submission.ThreeSum.LightBlockSourceRetainedHost
import Submission.ThreeSum.LightBlockSourceBatchLayout

/-!
# One actual retained source bank and its two pointer headers

The program computes the bank's addresses, constructs both original source
stage families from the shared histograms, and writes their two pointers.
Every earlier bank and every input before the header array is retained.
-/

namespace ThreeSum.LightBlockSourceBatchStep

open Light BlockEncoding GlobalEncoding BlockIndex BlockCoefficientRows
open SubsetAddress LocalCoverBounds BlockSourceEncoding

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

/-- The first fourteen arguments are the original retained-host controls and
inputs. The remaining arguments are header base, compact capacity, bank count,
bank base, bank stride, shared scratch addresses, and the current bank index. -/
def body (pSource : ℕ) : Stmt :=
  .set 24 (v 17 +' v 23 *' v 18) ;;
  .set 25 (v 24 +' v 15) ;;
  .set 26 (v 25 +' v 0 *' v 1) ;;
  .set 27 (v 26 +' v 0 *' v 1) ;;
  .set 28 (v 27 +' v 15) ;;
  .set 29 (v 28 +' v 15) ;;
  .set 30 (v 29 +' k 2 *' v 15 +' k 2) ;;
  .set 31 (v 30 +' (v 0 *' v 1 +' k 1) *' v 15) ;;
  .call pSource [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,
    v 24,v 25,v 26,v 27,v 28,v 29,v 30,v 31,v 19,v 20,v 21,v 22] 32 ;;
  .store (v 14 +' k 2 *' v 23) (v 30) ;;
  .store (v 14 +' k 2 *' v 23 +' k 1) (v 31)

def time (h J cut : ℕ) : ℕ := LightBlockSourceRetainedHost.time h J cut+500

structure Procs (P : Program) (pMain : ℕ) where
  pSource : ℕ
  source : LightBlockSourceRetainedHost.Procs P pSource
  main : P[pMain]? = some (body pSource)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {h J cut p NL NR occ maps candidates histL histR sourceHistL sourceHistR
      base count i : ℕ} {shift : ℤ}
    (B : Finset β) (b : β → ℤ) (A : Finset γ) (a : γ → ℤ)
    (q : GlobalOutput h J) (vL vR : ℕ → ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ A)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+10 ≤ lim.depth)
    (hcut : cut ≤ J*(512*h)) (hi : i < count)
    (hocc : occ+J ≤ base) (hmaps : maps+2*(512*h)*scheduleSize h ≤ base)
    (hcandidates : candidates+scheduleSize h ≤ base)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h ≤ base)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h ≤ base)
    (hsourceHistL : sourceHistL+modulus h J ≤ base)
    (hsourceHistR : sourceHistR+modulus h J ≤ base)
    (hspace : LightBlockSourceRetainedHost.space (LightBlockSourceBatchLayout.work base count (J*(512*h)) cut) h J ≤ lim.space)
    (hword : (LightBlockSourceRetainedHost.word NL NR h J : ℤ) ≤ lim.word)
    (hinputL : ∀ j : Fin NL, vL j.val = b (eL j))
    (hinputR : ∀ j : Fin NR, vR j.val = a (eR j))
    (hhistReadL : ∀ r < modulus h J,
      μ (sourceHistL+r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) 0 vL NL r : ℤ))
    (hhistReadR : ∀ r < modulus h J,
      μ (sourceHistR+r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) shift vR NR r : ℤ))
    (hoccRead : ∀ j < J, μ (occ+j) = (occurrenceIndices (outputOccurrences q) j : ℤ))
    (hcover : BlockSourceCoverInput.Input μ h maps candidates histL histR) :
    Meets lim P pMain d
      [J,512*h,h,localPrime h,localBucketCap h,cut,modulus h J,occ,maps,candidates,
        histL,histR,sourceHistL,sourceHistR,base,downsetCap (J*(512*h)) cut,count,
        LightBlockSourceBatchLayout.banks base count,LightBlockSourceBatchLayout.stride (J*(512*h)) cut,
        LightBlockSourceBatchLayout.maskBase base count (J*(512*h)) cut,LightBlockSourceBatchLayout.bitBase base count (J*(512*h)) cut,
        LightBlockSourceBatchLayout.rowOut base count (J*(512*h)) cut,LightBlockSourceBatchLayout.work base count (J*(512*h)) cut,i]
      μ (time h J cut) (fun _ ν =>
        LightZetaStages.StoredThrough ν (LightBlockSourceBatchLayout.leftBase base count (J*(512*h)) cut i) cut
          (BlockIndexedQuery.leftSource (p : ℤ) B b q) (J*(512*h)) ∧
        LightZetaStages.StoredThrough ν (LightBlockSourceBatchLayout.rightBase base count (J*(512*h)) cut i) cut
          (BlockIndexedQuery.rightSource (p : ℤ) shift A a q) (J*(512*h)) ∧
        ν (base+2*i) = (LightBlockSourceBatchLayout.leftBase base count (J*(512*h)) cut i : ℤ) ∧
        ν (base+2*i+1) = (LightBlockSourceBatchLayout.rightBase base count (J*(512*h)) cut i : ℤ) ∧
        KeptBut μ ν (LightBlockSourceBatchLayout.slot base count (J*(512*h)) cut i) (base+2*i) 2) := by
  have hs : LightBlockSourceBatchLayout.work base count (J*(512*h)) cut+(J*(512*h)+1) ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hwork : LightBlockSourceBatchLayout.work base count (J*(512*h)) cut ≤ lim.space := by omega
  have hslot := LightBlockSourceBatchLayout.slot_width_le_work (base := base) (W := J*(512*h)) (cut := cut) hi
  have hhead := LightBlockSourceBatchLayout.header_end_le_slot (base := base) (W := J*(512*h)) (cut := cut) hi
  have hbanks := LightBlockSourceBatchLayout.banks_le_slot base count (J*(512*h)) cut i
  have haddr := LightBlockSourceBatchLayout.addresses_le_work (base := base) (W := J*(512*h)) (cut := cut) hi
  have hwidth : (J : ℤ)*(512*(h : ℤ)) ≤ lim.word :=
    (by exact_mod_cast (show J*(512*h) ≤ lim.space by omega) :
      (J : ℤ)*(512*(h : ℤ)) ≤ lim.space).trans hw
  have hwidthNonneg : (0 : ℤ) ≤ (J : ℤ)*(512*(h : ℤ)) := by positivity
  have hwidthPlus : (J : ℤ)*(512*(h : ℤ))+1 ≤ lim.word :=
    (by exact_mod_cast (show J*(512*h)+1 ≤ lim.space by omega) :
      (J : ℤ)*(512*(h : ℤ))+1 ≤ lim.space).trans hw
  have hleftSpace : LightBlockSourceBatchLayout.leftBase base count (J*(512*h)) cut i ≤ lim.space := by omega
  have hrightSpace : LightBlockSourceBatchLayout.rightBase base count (J*(512*h)) cut i ≤ lim.space := by omega
  have hprodNat : i*LightBlockSourceBatchLayout.stride (J*(512*h)) cut ≤ lim.space := by
    unfold LightBlockSourceBatchLayout.slot at hslot
    omega
  have hprod : (i : ℤ)*(LightBlockSourceBatchLayout.stride (J*(512*h)) cut : ℤ) ≤ lim.word :=
    (by exact_mod_cast hprodNat :
      (i : ℤ)*(LightBlockSourceBatchLayout.stride (J*(512*h)) cut : ℤ) ≤ lim.space).trans hw
  have hprodNonneg : (0 : ℤ) ≤ (i : ℤ)*(LightBlockSourceBatchLayout.stride (J*(512*h)) cut : ℤ) := by positivity
  have htwocapNat : 2*downsetCap (J*(512*h)) cut ≤ lim.space := by
    unfold LightBlockSourceBatchLayout.leftBase at hleftSpace
    omega
  have htwocap : (2 : ℤ)*(downsetCap (J*(512*h)) cut : ℤ) ≤ lim.word :=
    (by exact_mod_cast htwocapNat : (2 : ℤ)*(downsetCap (J*(512*h)) cut : ℤ) ≤ lim.space).trans hw
  have hfamNat : (J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ lim.space := by
    unfold LightBlockSourceBatchLayout.rightBase LightBlockSourceBatchLayout.family at hrightSpace
    omega
  have hfam : ((J : ℤ)*(512*(h : ℤ))+1)*(downsetCap (J*(512*h)) cut : ℤ) ≤ lim.word :=
    (by exact_mod_cast hfamNat : ((J : ℤ)*(512*(h : ℤ))+1)*(downsetCap (J*(512*h)) cut : ℤ) ≤ lim.space).trans hw
  have hfamNonneg : (0 : ℤ) ≤ ((J : ℤ)*(512*(h : ℤ))+1)*(downsetCap (J*(512*h)) cut : ℤ) := by positivity
  have hbase : base ≤ LightBlockSourceBatchLayout.slot base count (J*(512*h)) cut i := by
    unfold LightBlockSourceBatchLayout.banks at hbanks
    omega
  have hs0 : LightBlockSourceBatchLayout.banks base count+
      i*LightBlockSourceBatchLayout.stride (J*(512*h)) cut ≤ lim.space := by
    unfold LightBlockSourceBatchLayout.slot at hslot
    omega
  have hs1 : LightBlockSourceBatchLayout.slot base count (J*(512*h)) cut i+
      downsetCap (J*(512*h)) cut ≤ lim.space := haddr.1.trans hwork
  have hs2 : LightBlockSourceBatchLayout.coeff0 base count (J*(512*h)) cut i+
      J*(512*h) ≤ lim.space := haddr.2.1.trans hwork
  have hs3 : LightBlockSourceBatchLayout.coeff1 base count (J*(512*h)) cut i+
      J*(512*h) ≤ lim.space := haddr.2.2.1.trans hwork
  have hs4 : LightBlockSourceBatchLayout.rawLeft base count (J*(512*h)) cut i+
      downsetCap (J*(512*h)) cut ≤ lim.space := haddr.2.2.2.1.trans hwork
  have hs5 : LightBlockSourceBatchLayout.rawRight base count (J*(512*h)) cut i+
      downsetCap (J*(512*h)) cut ≤ lim.space := haddr.2.2.2.2.1.trans hwork
  have hs6 : LightBlockSourceBatchLayout.flags base count (J*(512*h)) cut i+
      2*downsetCap (J*(512*h)) cut+2 ≤ lim.space := haddr.2.2.2.2.2.1.trans hwork
  have hs7 : LightBlockSourceBatchLayout.leftBase base count (J*(512*h)) cut i+
      (J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ lim.space := haddr.2.2.2.2.2.2.trans hwork
  have hs2Int : (LightBlockSourceBatchLayout.coeff0 base count (J*(512*h)) cut i : ℤ)+
      (J : ℤ)*(512*(h : ℤ)) ≤ lim.word := (by exact_mod_cast hs2 :
        (LightBlockSourceBatchLayout.coeff0 base count (J*(512*h)) cut i : ℤ)+
          (J : ℤ)*(512*(h : ℤ)) ≤ lim.space).trans hw
  have hs3Int : (LightBlockSourceBatchLayout.coeff1 base count (J*(512*h)) cut i : ℤ)+
      (J : ℤ)*(512*(h : ℤ)) ≤ lim.word := (by exact_mod_cast hs3 :
        (LightBlockSourceBatchLayout.coeff1 base count (J*(512*h)) cut i : ℤ)+
          (J : ℤ)*(512*(h : ℤ)) ≤ lim.space).trans hw
  have hs7Int : (LightBlockSourceBatchLayout.leftBase base count (J*(512*h)) cut i : ℤ)+
      ((J : ℤ)*(512*(h : ℤ))+1)*(downsetCap (J*(512*h)) cut : ℤ) ≤ lim.word :=
    (by exact_mod_cast hs7 : (LightBlockSourceBatchLayout.leftBase base count (J*(512*h)) cut i : ℤ)+
      ((J : ℤ)*(512*(h : ℤ))+1)*(downsetCap (J*(512*h)) cut : ℤ) ≤ lim.space).trans hw
  apply Meets.of_body C.main
  unfold body time
  light_set (LightBlockSourceBatchLayout.slot base count (J*(512*h)) cut i : ℕ) using LightBlockSourceBatchLayout.slot
  light_set (LightBlockSourceBatchLayout.coeff0 base count (J*(512*h)) cut i : ℕ) using LightBlockSourceBatchLayout.coeff0
  light_set (LightBlockSourceBatchLayout.coeff1 base count (J*(512*h)) cut i : ℕ) using LightBlockSourceBatchLayout.coeff1
  light_set (LightBlockSourceBatchLayout.rawLeft base count (J*(512*h)) cut i : ℕ) using LightBlockSourceBatchLayout.rawLeft
  light_set (LightBlockSourceBatchLayout.rawRight base count (J*(512*h)) cut i : ℕ) using LightBlockSourceBatchLayout.rawRight
  light_set (LightBlockSourceBatchLayout.flags base count (J*(512*h)) cut i : ℕ) using LightBlockSourceBatchLayout.flags
  light_set (LightBlockSourceBatchLayout.leftBase base count (J*(512*h)) cut i : ℕ) using LightBlockSourceBatchLayout.leftBase
  light_set (LightBlockSourceBatchLayout.rightBase base count (J*(512*h)) cut i : ℕ) using LightBlockSourceBatchLayout.rightBase,LightBlockSourceBatchLayout.family
  have hrun := C.source.meets (d := d+1) (μ := μ) (cut := cut) (p := p) (shift := shift)
    (occ := occ) (maps := maps) (candidates := candidates) (histL := histL) (histR := histR)
    (sourceHistL := sourceHistL) (sourceHistR := sourceHistR)
    (masks := LightBlockSourceBatchLayout.slot base count (J*(512*h)) cut i)
    (coeff0 := LightBlockSourceBatchLayout.coeff0 base count (J*(512*h)) cut i)
    (coeff1 := LightBlockSourceBatchLayout.coeff1 base count (J*(512*h)) cut i)
    (rawLeft := LightBlockSourceBatchLayout.rawLeft base count (J*(512*h)) cut i)
    (rawRight := LightBlockSourceBatchLayout.rawRight base count (J*(512*h)) cut i)
    (flags := LightBlockSourceBatchLayout.flags base count (J*(512*h)) cut i)
    (baseL := LightBlockSourceBatchLayout.leftBase base count (J*(512*h)) cut i)
    (baseR := LightBlockSourceBatchLayout.rightBase base count (J*(512*h)) cut i)
    (maskBase := LightBlockSourceBatchLayout.maskBase base count (J*(512*h)) cut)
    (bitBase := LightBlockSourceBatchLayout.bitBase base count (J*(512*h)) cut)
    (rowOut := LightBlockSourceBatchLayout.rowOut base count (J*(512*h)) cut)
    (work := LightBlockSourceBatchLayout.work base count (J*(512*h)) cut)
    B b A a q vL vR eL eR hw (by omega) hcut
    (hocc.trans hbase) (hmaps.trans hbase) (hcandidates.trans hbase)
    (hleft.trans hbase) (hright.trans hbase) (hsourceHistL.trans hbase) (hsourceHistR.trans hbase)
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (LightBlockSourceBatchLayout.right_end_le_masks hi)
    le_rfl le_rfl le_rfl hspace hword hinputL hinputR hhistReadL hhistReadR hoccRead hcover
  light_call hrun with r ν ⟨storedL,storedR,kept⟩
  light_store (base+2*i) (LightBlockSourceBatchLayout.leftBase base count (J*(512*h)) cut i : ℕ)
  light_store (base+2*i+1) (LightBlockSourceBatchLayout.rightBase base count (J*(512*h)) cut i : ℕ)
  dsimp only
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro j hj S hS
    have hb := LightBlockSourceBatchLayout.banks_le_left_cell base count (J*(512*h)) cut i j S
    unfold LightBlockSourceBatchLayout.banks at hb
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact storedL j hj S hS
  · intro j hj S hS
    have hb := LightBlockSourceBatchLayout.banks_le_right_cell base count (J*(512*h)) cut i j S
    unfold LightBlockSourceBatchLayout.banks at hb
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact storedR j hj S hS
  · rw [Function.update_of_ne (by omega),Function.update_self]
  · exact Function.update_self ..
  · intro x hx
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact kept x hx.1

end ThreeSum.LightBlockSourceBatchStep
