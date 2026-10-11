import Submission.ThreeSum.ReportingHostTerminalChoices
import Submission.ThreeSum.ReportingHostBlockBucketTest

/-!
# Charging actual terminal scans to the original raw prefix mass

The actual independent bucket tester costs `240` per selected physical pair
plus `700` per terminal candidate. This file sums those exact verified costs
over the enumerator's unchanged order. It also proves conservation of raw
mass across the actual positive frontier at any partial depth.
-/

namespace ThreeSum.ReportingHostTerminalCosts

open Finset BlockRows BlockIndex BlockEncoding BlockForced BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open ReportingHostTerminalChoices ReportingHostBlockBucketTest BlockSourceEncoding LightSourceResidues
open scoped BigOperators

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

theorem sum_linear {δ : Type*} (xs : List δ) (f : δ→ℕ) (c d : ℕ) :
    (xs.map (fun x => c*f x+d)).sum=c*(xs.map f).sum+d*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih]; ring

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def actualTestWork {h J : ℕ} (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (512*h)))) : ℕ :=
  ((choices q k).map fun S =>
    LightReportingBucketTest.time
      (fun i => key p (modulus h J) 0 (left i)) (fun j => key p (modulus h J) shift (right j)) NL NR
      (leftResidue (outputOccurrences q) (prefixLeft (prefixIndices J k) (prefixRows pre) ∪ S))
      (rightResidue (outputOccurrences q) (prefixRight (prefixIndices J k) (outputRows q) (prefixRows pre) ∪
        (remaining (prefixIndices J k) (outputRows q) \ S)))
      (leftFlag (outputOccurrences q) (prefixLeft (prefixIndices J k) (prefixRows pre) ∪ S))
      (rightFlag (outputOccurrences q) (prefixRight (prefixIndices J k) (outputRows q) (prefixRows pre) ∪
        (remaining (prefixIndices J k) (outputRows q) \ S)))).sum

theorem actualTestWork_eq {h J NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (B : Finset β) (C : Finset γ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (q : GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (512*h)))) :
    actualTestWork p shift left right NL NR q k pre =
      240*((choices q k).map (pairMass (p : ℤ) shift B C b c q k pre)).sum+700*(choices q k).length := by
  unfold actualTestWork
  simp_rw [actual_time_eq (outputOccurrences q) p shift B C b c _ _ left right eL eR hvL hvR]
  exact sum_linear (choices q k) (pairMass (p : ℤ) shift B C b c q k pre) 240 700

theorem actualTestWork_le {h J k NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k≤J) (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1∈A ∧ globalModulus h J ∣ (a w.1%(p : ℤ)+lift w.2.1*(p : ℤ)+shift)-globalKey w.2.2) :
    actualTestWork p shift left right NL NR w.2.2 k pre ≤
      240*prefixQuery (rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w k pre+
        700*2^((J-k)*(2*h)) := by
  rw [actualTestWork_eq p shift B C b c left right eL eR hvL hvR]
  exact Nat.add_le_add
    (Nat.mul_le_mul_left 240 (pairMass_sum_le_prefixQuery (p : ℤ) shift A B C a b c w pre hk hp hkey))
    (Nat.mul_le_mul_left 700 (choices_length_le w.2.2 hk))

theorem frontier_mass {h J k : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) (hk : k≤J) :
    ((ReportingHostFrontier.frontier I w k).map (prefixQuery I w k)).sum=(domain I w).card := by
  rw [← List.sum_toFinset _ (ReportingHostFrontier.frontier_nodup I w k)]
  change (∑ pre ∈ (ReportingHostFrontier.frontier I w k).toFinset,
    Subset.fiberMass (domain I w) (fun r => (word r).take k) (fun _ => 1) pre)=(domain I w).card
  rw [Subset.fiberMass_conservation]
  · simp
  · intro r hr
    apply List.mem_toFinset.mpr
    exact (ReportingHostFrontier.mem_frontier_iff I w hk _).mpr
      ⟨r,(Finset.mem_filter.mp hr).1,(Finset.mem_filter.mp hr).2,rfl⟩

theorem total_frontier_mass {h J k : ℕ} (I : Finset (RawItem h J α β γ)) (hk : k≤J) :
    (∑ w : Wanted h J α,
      ((ReportingHostFrontier.frontier I w k).map (prefixQuery I w k)).sum)=I.card := by
  simp only [frontier_mass I _ hk]
  symm
  exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)

end ThreeSum.ReportingHostTerminalCosts
