import Submission.ThreeSum.TernaryLiteralOutputCap
import Submission.ThreeSum.TernaryCoverGoodMaps
import Submission.ThreeSum.TernaryFixedDictionaries
import Submission.ThreeSum.TernaryWantedRadix
import Submission.ThreeSum.TernaryCodeSemantics
import Mathlib.Algebra.Order.Floor.Div

/-! Literal output records retain their original map occurrence IDs. Only
records belonging to globally bad raw-pair maps are omitted. Keys are the
canonical native output residues, with no signed integer carry added. -/
noncomputable section
namespace ThreeSum.TernaryGoodOutputCatalog
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open TernaryCoverGoodMaps TernaryCoverFibers TernaryLocalParameters TernaryPartitionCount
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000

variable {m p : ℕ} [Fact p.Prime]

def Rbar (m : ℕ) := 2^(fixedPi m 1)*3^(fixedPi m 2)
def cap (m p τ : ℕ) := (partitionLoss (7930175*m) (978249*m)*p*τ) ⌈/⌉ Rbar m

abbrev Output (m : ℕ) := {q // q∈vertices (fixedLength m) (fixedPi m)}
abbrev Record (m : ℕ) (I : Type*) := I×Output m

def native (w : Weight m p) (q : Output m) : ZMod p := outputHash w q.val

theorem fixed_output_cap (τ : ℕ) (w : Weight m p)
    (hgood : w∉rawBadMaps m p τ) (o : ZMod p) :
    Rbar m*outputFiberCount (native w) o≤partitionLoss (7930175*m) (978249*m)*p*τ := by
  have hraw : ∀a b : ZMod p, rawPairCount
      (leftHash (α := fixedAlpha m) (π := fixedPi m) w) (rightHash w) a b≤τ := by
    intro a b
    by_contra hn
    apply hgood
    simp only [rawBadMaps,TernaryCoverMoments.badMaps,mem_filter,mem_univ,true_and]
    exact ⟨(a,b),by change τ<rawPairCount (leftHash w) (rightHash w) a b; omega⟩
  have hL : 81204903*m+2*(7930175*m)+3*(978249*m)=fixedLength m := by simp [fixedLength]; omega
  have hα : alphaType (81204903*m) (7930175*m) (978249*m)=fixedAlpha m := by
    funext d; fin_cases d <;> simp [alphaType,fixedAlpha] <;> omega
  have hπ : piType (81204903*m) (7930175*m) (978249*m)=fixedPi m := by
    funext d; fin_cases d <;> simp [piType,fixedPi] <;> omega
  have hh := TernaryLiteralOutputCap.actual_output_cap (p := p)
    (81204903*m) (7930175*m) (978249*m) τ
  unfold TernaryLiteralOutputCap.actualOutputHash at hh
  rw [hL,hα,hπ] at hh
  have h1 : 2*(7930175*m)=fixedPi m 1 := by simp [fixedPi]; omega
  have h2 : 3*(978249*m)=fixedPi m 2 := by simp [fixedPi]; omega
  convert hh w hraw o using 1 <;> simp [Rbar,fixedPi] <;> ring
  unfold outputFiberCount native
  congr 2

theorem native_fiber_cap (τ : ℕ) (w : Weight m p) (hgood : w∉rawBadMaps m p τ) (o : ZMod p) :
    outputFiberCount (native w) o≤cap m p τ := by
  have hR : 0<Rbar m := by unfold Rbar; positivity
  have hA := fixed_output_cap τ w hgood o
  have hceil : partitionLoss (7930175*m) (978249*m)*p*τ≤Rbar m*cap m p τ := by
    exact (ceilDiv_le_iff_le_mul hR).mp le_rfl
  nlinarith

variable {I : Type*} [Fintype I] [DecidableEq I]

def catalog (maps : I → Weight m p) (τ : ℕ) : Finset (Record m I) :=
  univ.filter fun r => maps r.1∉rawBadMaps m p τ

def records (maps : I → Weight m p) (τ : ℕ) : List (Record m I) := (catalog maps τ).toList

def key (maps : I → Weight m p) (r : Record m I) : ℤ := (native (maps r.1) r.2).val

def raws (maps : I → Weight m p) (τ : ℕ) : List ℤ := (records maps τ).map (key maps)

def wordCodes (maps : I → Weight m p) (τ : ℕ) : List ℕ :=
  (records maps τ).map fun r => TernaryCodeSemantics.address r.2.val

def mapCodes {F : ℕ} (maps : Fin F → Weight m p) (τ : ℕ) : List ℕ :=
  (records maps τ).map fun r => (Fintype.equivFin (Fin F) r.1).val

@[simp] theorem mem_records (maps : I → Weight m p) (τ : ℕ) (r : Record m I) :
    r∈records maps τ ↔ maps r.1∉rawBadMaps m p τ := by simp [records,catalog]

@[simp] theorem raws_length (maps : I → Weight m p) (τ : ℕ) :
    (raws maps τ).length=(records maps τ).length := by simp [raws]

@[simp] theorem wordCodes_length (maps : I → Weight m p) (τ : ℕ) :
    (wordCodes maps τ).length=(records maps τ).length := by simp [wordCodes]

@[simp] theorem mapCodes_length {F : ℕ} (maps : Fin F → Weight m p) (τ : ℕ) :
    (mapCodes maps τ).length=(records maps τ).length := by simp [mapCodes]

theorem records_nonempty_of_good (maps : I → Weight m p) (τ : ℕ)
    (i : I) (hi : maps i∉rawBadMaps m p τ) (q : Output m) : (records maps τ)≠[] := by
  intro he
  have hh : (i,q)∈records maps τ := (mem_records maps τ (i,q)).mpr hi
  simpa [he] using hh

def fiber (maps : I → Weight m p) (τ : ℕ) (o : ZMod p) : Finset (Record m I) :=
  (catalog maps τ).filter fun r => native (maps r.1) r.2=o

theorem fiber_cap (maps : I → Weight m p) (τ : ℕ) (o : ZMod p) :
    (fiber maps τ o).card≤Fintype.card I*cap m p τ := by
  have each (i : I) : ((fiber maps τ o).filter fun r => r.1=i).card≤cap m p τ := by
    by_cases hi : maps i∈rawBadMaps m p τ
    · have he : (fiber maps τ o).filter (fun r => r.1=i)=∅ := by
        ext r
        constructor
        · intro hr
          rcases mem_filter.mp hr with ⟨hf,he⟩
          have hg := (mem_filter.mp ((mem_filter.mp hf).1)).2
          exact False.elim (hg (he ▸ hi))
        · intro hr
          have hf : False := by simpa using hr
          exact hf.elim
      rw [he,card_empty]
      exact Nat.zero_le _
    · have hh : ((fiber maps τ o).filter fun r => r.1=i).card≤outputFiberCount (native (maps i)) o := by
        apply card_le_card_of_injOn (fun r : Record m I => r.2)
        · intro r hr
          rcases mem_filter.mp hr with ⟨hf,he⟩
          have ho := (mem_filter.mp hf).2
          simpa only [outputFiberCount,Finset.mem_coe,mem_filter,mem_univ,true_and,he] using ho
        · intro r hr s hs he
          apply Prod.ext
          · exact (mem_filter.mp hr).2.trans (mem_filter.mp hs).2.symm
          · exact he
      exact hh.trans (native_fiber_cap τ (maps i) hi o)
  calc
    _=∑i : I, ((fiber maps τ o).filter fun r => r.1=i).card :=
      card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
    _≤∑_i : I, cap m p τ := sum_le_sum (fun i _ => each i)
    _=_ := by simp

private theorem indices_filter_length (xs : List ℤ) (P : ℤ → Bool) :
    ((List.range xs.length).filter fun i => P (xs.getD i 0)).length=(xs.filter P).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.length_cons,List.range_succ_eq_map]
    simp only [List.filter_cons,List.getD_cons_zero,List.filter_map,List.getD_cons_succ,
      Function.comp_def,List.length_map]
    split_ifs <;> simp_all

theorem localBucket_cap (maps : I → Weight m p) (τ : ℕ) (x : ℤ) :
    (TernaryWantedRadix.localBucket (p : ℤ) (raws maps τ) x).length≤Fintype.card I*cap m p τ := by
  have hkey (r : Record m I) : (p : ℤ)∣x-key maps r ↔ native (maps r.1) r.2=(x : ZMod p) := by
    rw [←ZMod.intCast_zmod_eq_zero_iff_dvd,Int.cast_sub]
    simp only [key,Int.cast_natCast,ZMod.natCast_zmod_val,sub_eq_zero]
    exact eq_comm
  have hlen : (TernaryWantedRadix.localBucket (p : ℤ) (raws maps τ) x).length=
      (fiber maps τ (x : ZMod p)).card := by
    unfold TernaryWantedRadix.localBucket
    have hi := indices_filter_length (raws maps τ) (fun y => decide ((p : ℤ)∣x-y))
    apply hi.trans
    unfold raws
    rw [List.filter_map,List.length_map]
    have hnodup := ((catalog maps τ).nodup_toList).filter
      (fun r => decide ((p : ℤ)∣x-key maps r))
    have hh := List.toFinset_card_of_nodup hnodup
    apply hh.symm.trans
    congr 1
    ext r
    simp [fiber,records,Function.comp_def,hkey]
  rw [hlen]
  exact fiber_cap maps τ (x : ZMod p)


theorem records_length_le (maps : I → Weight m p) (τ : ℕ) :
    (records maps τ).length≤Fintype.card I*(vertices (fixedLength m) (fixedPi m)).card := by
  have hh : (catalog maps τ).card≤(univ : Finset (Record m I)).card := card_le_card (filter_subset _ _)
  simpa [records,Record,Output] using hh

theorem cap_le_iff (τ C : ℕ) : cap m p τ≤C ↔
    partitionLoss (7930175*m) (978249*m)*p*τ≤Rbar m*C := by
  exact ceilDiv_le_iff_le_mul (by unfold Rbar; positivity)

theorem cap_pos {τ : ℕ} (hτ : 0<τ) : 0<cap m p τ := by
  have hh := (cap_le_iff (m := m) (p := p) τ (cap m p τ)).mp le_rfl
  have hA : 0<partitionLoss (7930175*m) (978249*m)*p*τ := by
    have hp := (Fact.out : p.Prime).pos
    unfold partitionLoss
    positivity
  by_contra hn
  have hz : cap m p τ=0 := by omega
  rw [hz,mul_zero] at hh
  omega

theorem key_bounds (maps : I → Weight m p) (r : Record m I) :
    0≤key maps r ∧ key maps r<(p : ℤ) := by
  unfold key
  exact ⟨Int.ofNat_zero_le _,by exact_mod_cast ZMod.val_lt (native (maps r.1) r.2)⟩

theorem wordCodes_bound (maps : I → Weight m p) (τ : ℕ) :
    ∀i<(raws maps τ).length, (wordCodes maps τ).getD i 0<4^(fixedLength m) := by
  intro i hi
  have hi' : i<(records maps τ).length := by simpa using hi
  rw [List.getD_eq_getElem _ _ (by simpa using hi')]
  simp only [wordCodes,List.getElem_map]
  exact TernaryCodeSemantics.address_lt _

theorem mapCodes_bound {F : ℕ} (maps : Fin F → Weight m p) (τ : ℕ) :
    ∀i<(raws maps τ).length, (mapCodes maps τ).getD i 0<F := by
  intro i hi
  have hi' : i<(records maps τ).length := by simpa using hi
  rw [List.getD_eq_getElem _ _ (by simpa using hi')]
  simp only [mapCodes,List.getElem_map]
  simpa only [Fintype.card_fin] using (Fintype.equivFin (Fin F) ((records maps τ)[i]).1).isLt


theorem cap_real_le (τ : ℕ) : (cap m p τ : ℝ)≤
    ((partitionLoss (7930175*m) (978249*m)*p*τ : ℕ) : ℝ)/(Rbar m : ℝ)+1 := by
  have hR : 0<Rbar m := by unfold Rbar; positivity
  have hRR : (0 : ℝ)<Rbar m := by exact_mod_cast hR
  by_cases hz : cap m p τ=0
  · rw [hz,Nat.cast_zero]
    positivity
  · have hpos : 0<cap m p τ := by omega
    have hlt : Rbar m*(cap m p τ-1)<partitionLoss (7930175*m) (978249*m)*p*τ := by
      by_contra hn
      have hh := (cap_le_iff (m := m) (p := p) τ (cap m p τ-1)).mpr (by omega)
      omega
    have hcast : ((cap m p τ-1 : ℕ) : ℝ)=(cap m p τ : ℝ)-1 := by
      rw [Nat.cast_sub (show 1≤cap m p τ by omega)]
      norm_num
    have hltR : (Rbar m : ℝ)*((cap m p τ : ℝ)-1)<
        ((partitionLoss (7930175*m) (978249*m)*p*τ : ℕ) : ℝ) := by
      have hh : (Rbar m : ℝ)*((cap m p τ-1 : ℕ) : ℝ)<
          ((partitionLoss (7930175*m) (978249*m)*p*τ : ℕ) : ℝ) := by exact_mod_cast hlt
      rwa [hcast] at hh
    have hh : (cap m p τ : ℝ)-1≤
        ((partitionLoss (7930175*m) (978249*m)*p*τ : ℕ) : ℝ)/(Rbar m : ℝ) :=
      (le_div_iff₀ hRR).mpr (by nlinarith [hltR])
    linarith


theorem cap_real_le_twice (τ : ℕ)
    (hA : Rbar m≤partitionLoss (7930175*m) (978249*m)*p*τ) :
    (cap m p τ : ℝ)≤2*(((partitionLoss (7930175*m) (978249*m)*p*τ : ℕ) : ℝ)/(Rbar m : ℝ)) := by
  have hR : (0 : ℝ)<Rbar m := by unfold Rbar; positivity
  have hRatio : (1 : ℝ)≤((partitionLoss (7930175*m) (978249*m)*p*τ : ℕ) : ℝ)/(Rbar m : ℝ) := by
    apply (le_div_iff₀ hR).mpr
    simpa only [one_mul] using (show (Rbar m : ℝ)≤((partitionLoss (7930175*m) (978249*m)*p*τ : ℕ) : ℝ) by exact_mod_cast hA)
  linarith [cap_real_le (m := m) (p := p) τ]


theorem cap_real_le_native (τ : ℕ) (hτ : 0<τ)
    (hP : (vertices (fixedLength m) (fixedPi m)).card*Rbar m≤p^2) :
    (cap m p τ : ℝ)≤2*(((partitionLoss (7930175*m) (978249*m)*p*τ : ℕ) : ℝ)/(Rbar m : ℝ)) := by
  have hR : Rbar m≤p := TernaryTypeLowerBound.partition_cap_le_prime
    (fixedPi m) (fixedPi_total m) (fixedPi_space m) p hP
  have hLoss : 0<partitionLoss (7930175*m) (978249*m) := by unfold partitionLoss; positivity
  have hp1 : p≤partitionLoss (7930175*m) (978249*m)*p := Nat.le_mul_of_pos_left p hLoss
  have hp2 : partitionLoss (7930175*m) (978249*m)*p≤partitionLoss (7930175*m) (978249*m)*p*τ :=
    Nat.le_mul_of_pos_right _ hτ
  exact cap_real_le_twice τ (hR.trans (hp1.trans hp2))

end ThreeSum.TernaryGoodOutputCatalog
