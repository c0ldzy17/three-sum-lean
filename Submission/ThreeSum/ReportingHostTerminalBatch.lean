import Submission.ThreeSum.LightReportingLeafBatch
import Submission.ThreeSum.LightReportingTerminalMasks
import Submission.ThreeSum.ReportingHostTerminalCosts
import Submission.ThreeSum.LightBlockSourceBuild

/-!
# Exact original-encoding semantics and cost of the executed terminal batch

This is the specialization of the actual seven-procedure batch to the full
endpoint masks emitted at a valid partial prefix. The precise ordered
candidate sum is charged to raw prefix mass plus the terminal cube term.
-/

namespace ThreeSum.ReportingHostTerminalBatch

open Finset BlockRows BlockIndex BlockEncoding BlockForced BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open ReportingHostTerminalChoices ReportingHostBlockBucketTest BlockSourceEncoding LightSourceResidues
open LightReportingTerminalMasks LightBlockSourceBuild
open scoped BigOperators

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

def endpointsLeft {h J : ℕ} (q : GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (512*h)))) : ℕ→ℤ :=
  fun i => endpointLeft (outputOccurrences q) (leftAt q k pre i)
def endpointsRight {h J : ℕ} (q : GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (512*h)))) : ℕ→ℤ :=
  fun i => endpointRight (outputOccurrences q) (rightAt q k pre i)
def flagsLeft {h J : ℕ} (q : GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (512*h)))) : ℕ→ℕ :=
  fun i => leftFlag (outputOccurrences q) (leftAt q k pre i)
def flagsRight {h J : ℕ} (q : GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (512*h)))) : ℕ→ℕ :=
  fun i => rightFlag (outputOccurrences q) (rightAt q k pre i)

def time {h J : ℕ} (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (512*h)))) : ℕ :=
  LightReportingLeafBatch.time
    (fun i => key p (modulus h J) 0 (left i)) (fun i => key p (modulus h J) shift (right i))
    (flagsLeft q k pre) (flagsRight q k pre) NL NR (modulus h J) (endpointBound h J)
    (endpointsLeft q k pre) (endpointsRight q k pre) (count h J k)

def Hit {h J : ℕ} (a : ℤ) (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (512*h)))) : Prop :=
  LightReportingLeafBatch.Hit a (endpointsLeft q k pre) (endpointsRight q k pre) left right
    (fun i => key p (modulus h J) 0 (left i)) (fun i => key p (modulus h J) shift (right i))
    (flagsLeft q k pre) (flagsRight q k pre) NL NR (modulus h J) (count h J k)

theorem sum_choiceAt {h J k : ℕ} (q : GlobalOutput h J) (hk : k≤J)
    (f : Finset (Coord J (512*h))→ℕ) :
    (∑ i∈range (count h J k), f (choiceAt q k i))=((choices q k).map f).sum := by
  rw [show count h J k=(choices q k).length by exact (choices_length q hk).symm,Finset.sum_range]
  calc
    (∑ i : Fin (choices q k).length, f (choiceAt q k i.val)) =
        ∑ i : Fin (choices q k).length, f ((choices q k)[i.val]) :=
      Finset.sum_congr rfl (fun i _ => congrArg f (choiceAt_eq_get q i.isLt))
    _ = _ := Fin.sum_univ_fun_getElem (choices q k) f

theorem time_eq {h J k : ℕ} (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : GlobalOutput h J) (pre : List (Finset (Fin (512*h)))) (hk : k≤J) :
    time p shift left right NL NR q k pre=
      ReportingHostTerminalCosts.actualTestWork p shift left right NL NR q k pre+
        count h J k*(2*LightResidues.residueBudget (endpointBound h J)+600)+30 := by
  unfold time
  rw [LightReportingLeafBatch.time_eq_sum]
  simp only [LightReportingLeaf.time]
  have hsum := sum_choiceAt q hk (fun S =>
    LightReportingBucketTest.time
      (fun i => key p (modulus h J) 0 (left i)) (fun i => key p (modulus h J) shift (right i)) NL NR
      (leftResidue (outputOccurrences q) (prefixLeft (prefixIndices J k) (prefixRows pre) ∪ S))
      (rightResidue (outputOccurrences q) (prefixRight (prefixIndices J k) (outputRows q) (prefixRows pre) ∪
        (remaining (prefixIndices J k) (outputRows q) \ S)))
      (leftFlag (outputOccurrences q) (prefixLeft (prefixIndices J k) (prefixRows pre) ∪ S))
      (rightFlag (outputOccurrences q) (prefixRight (prefixIndices J k) (outputRows q) (prefixRows pre) ∪
        (remaining (prefixIndices J k) (outputRows q) \ S))))
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,smul_eq_mul]
  change 30+(_+_+_+_)=_
  have hsum' : (∑ i∈range (count h J k),
      LightReportingBucketTest.time
        (fun i => key p (modulus h J) 0 (left i)) (fun i => key p (modulus h J) shift (right i)) NL NR
        (LightResidues.residue (modulus h J) 1 (endpointsLeft q k pre i))
        (LightResidues.residue (modulus h J) 1 (endpointsRight q k pre i))
        (flagsLeft q k pre i) (flagsRight q k pre i))=
      ReportingHostTerminalCosts.actualTestWork p shift left right NL NR q k pre := hsum
  rw [hsum']
  ring

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem time_le {h J k NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k≤J) (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1∈A ∧ globalModulus h J ∣ (a w.1%(p : ℤ)+lift w.2.1*(p : ℤ)+shift)-globalKey w.2.2) :
    time p shift left right NL NR w.2.2 k pre ≤
      240*prefixQuery (rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w k pre+
        (2*LightResidues.residueBudget (endpointBound h J)+1300)*2^((J-k)*(2*h))+30 := by
  rw [time_eq p shift left right NL NR w.2.2 pre hk]
  have htest := ReportingHostTerminalCosts.actualTestWork_le p shift A B C a b c left right eL eR hvL hvR w pre hk hp hkey
  have hn : count h J k≤2^((J-k)*(2*h)) := Nat.choose_le_two_pow _ _
  have hmul := Nat.mul_le_mul_right (2*LightResidues.residueBudget (endpointBound h J)+600) hn
  nlinarith

theorem hit_sound {h J k NL NR : ℕ} {av shift : ℤ} {p : ℕ} {left right : ℕ→ℤ}
    {q : GlobalOutput h J} {pre : List (Finset (Fin (512*h)))}
    (H : Hit av p shift left right NL NR q k pre) :
    ∃ i<NL, ∃ j<NR, right j-left i-av=0 := by
  obtain ⟨s,hs,_,_,i,hi,j,hj,_,_,he⟩ := H
  exact ⟨i,hi,j,hj,he⟩

theorem hit_of_compatible {h J k NL NR : ℕ} (p : ℕ) (shift av : ℤ)
    (B : Finset β) (C : Finset γ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (q : GlobalOutput h J) (pre : List (Finset (Fin (512*h)))) (hk : k≤J) (hp : ValidPrefix q k pre)
    (t : ChoiceTuple h J) (ht : t∈completions q k pre) (bc : β×γ)
    (hbc : bc∈compatiblePairs (p : ℤ) shift B C b c t) (heq : c bc.2-b bc.1-av=0) :
    Hit av p shift left right NL NR q k pre := by
  have hq := (Finset.mem_filter.mp ht).2.1
  obtain ⟨s,hs,hL,hR⟩ := completion_index q pre hk hp t ht
  obtain ⟨hmem,hdivL,hdivR⟩ := Finset.mem_filter.mp hbc
  obtain ⟨hb,hc⟩ := Finset.mem_product.mp hmem
  let i : Fin NL := eL.symm ⟨bc.1,hb⟩
  let j : Fin NR := eR.symm ⟨bc.2,hc⟩
  have hi : left i.val=b bc.1 := (hvL i).trans (by simp [i])
  have hj : right j.val=c bc.2 := (hvR j).trans (by simp [j])
  refine ⟨s,hs,?_,?_,i.val,i.isLt,j.val,j.isLt,?_,?_,?_⟩
  · change leftFlag (outputOccurrences q) (leftAt q k pre s)=1
    rw [hL]
    simp [leftFlag,leftAllowed_choice t q hq]
  · change rightFlag (outputOccurrences q) (rightAt q k pre s)=1
    rw [hR]
    simp [rightFlag,rightAllowed_choice t q hq]
  · apply (key_eq_iff (modulus_pos h J) 0 (left i.val) _).mpr
    change (modulus h J : ℤ) ∣ left i.val%(p : ℤ)+0-endpointLeft (outputOccurrences q) (leftAt q k pre s)
    simpa only [hi,hL,endpointLeft_choice t q hq,modulus_cast,add_zero] using hdivL
  · apply (key_eq_iff (modulus_pos h J) shift (right j.val) _).mpr
    change (modulus h J : ℤ) ∣ right j.val%(p : ℤ)+shift-endpointRight (outputOccurrences q) (rightAt q k pre s)
    simpa only [hj,hR,endpointRight_choice t q hq,modulus_cast] using hdivR
  · simpa only [hi,hj] using heq

end ThreeSum.ReportingHostTerminalBatch
