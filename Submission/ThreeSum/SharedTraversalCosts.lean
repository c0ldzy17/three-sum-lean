import Submission.ThreeSum.LightReportingWanted
import Submission.ThreeSum.DenseGuard

/-!
# Cost of the executed positive-frontier traversal

The expensive expansion remains multiplied by the number of actual positive
parents. Empty frontiers pay only the fixed level overhead. The terminal
scan is charged to the exact original bucket products, and the dense guard
removes this proportional charge from the branch which has already exceeded
the threshold.
-/

namespace ThreeSum.SharedTraversalCosts

open Finset GlobalEncoding RawIncidences RawReporting ReportingHostLevelData
open ReportingHostFrontierLayout
open scoped BigOperators

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false

def levelUnit (h J : ℕ) (D : ℕ → Catalog) (K : ℕ) : ℕ :=
  ∑ k ∈ range K, (LightReportingPositiveExpand.time h J k (D (k+1)).t+200)

def searchUnit (h J : ℕ) (D : ℕ → Catalog) (K : ℕ) : ℕ :=
  levelUnit h J D K+ReportingHostTerminalFrontier.charge h J K+240

def initialUnit (h J : ℕ) (D : ℕ → Catalog) (K : ℕ) : ℕ :=
  LightReportingWantedInitialize.time h J (D 0).t+1300*K+1860

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem levels_time_eq {h J : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (D : ℕ → Catalog) (K : ℕ) :
    LightReportingLevels.time I w D K = 30+1300*K+
      ∑ k ∈ range K, (ReportingHostFrontier.frontier I w k).length*
        (LightReportingPositiveExpand.time h J k (D (k+1)).t+200) := by
  induction K with
  | zero => simp [LightReportingLevels.time]
  | succ K ih =>
      rw [LightReportingLevels.time,ih,sum_range_succ]
      unfold LightReportingStoredStep.time LightReportingFrontierStep.time
      omega

theorem levels_time_le {h J K : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (D : ℕ → Catalog) (hK : K ≤ J) :
    LightReportingLevels.time I w D K ≤
      (domain I w).card*levelUnit h J D K+1300*K+30 := by
  rw [levels_time_eq]
  have hs : (∑ k ∈ range K, (ReportingHostFrontier.frontier I w k).length*
      (LightReportingPositiveExpand.time h J k (D (k+1)).t+200)) ≤
      (domain I w).card*levelUnit h J D K := by
    unfold levelUnit
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    exact Nat.mul_le_mul_right _ (ReportingHostFrontier.frontier_length_le_domain I w
      ((mem_range.mp hk).le.trans hK))
  omega

theorem terminal_time_le {h J K NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (left right : ℕ → ℤ)
    (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i))
    (hvR : ∀ i : Fin NR, right i.val=c (eR i))
    (w : Wanted h J α) (hK : K ≤ J)
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1%(p : ℤ)+lift w.2.1*(p : ℤ)+shift)-globalKey w.2.2) :
    let I := rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
    LightReportingTerminalStored.time p shift left right NL NR I w K ≤
      (domain I w).card*(ReportingHostTerminalFrontier.charge h J K+240)+630 := by
  dsimp only
  let I := rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
  have ht := ReportingHostTerminalFrontier.frontier_time_le p shift A B C a b c
    left right eL eR hvL hvR w hK hkey
  have hm := Nat.mul_le_mul_left (ReportingHostTerminalFrontier.charge h J K)
    (ReportingHostFrontier.frontier_length_le_domain I w hK)
  change LightReportingTerminalStored.time p shift left right NL NR I w K ≤ _
  unfold LightReportingTerminalStored.time
  change ReportingHostTerminalFrontier.time p shift left right NL NR w.2.2 K
    (ReportingHostFrontier.frontier I w K) (ReportingHostFrontier.frontier I w K).length ≤
      240*(domain I w).card+ReportingHostTerminalFrontier.charge h J K*
        (ReportingHostFrontier.frontier I w K).length+30 at ht
  nlinarith

theorem search_time_le {h J K NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (left right : ℕ → ℤ)
    (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i))
    (hvR : ∀ i : Fin NR, right i.val=c (eR i))
    (w : Wanted h J α) (D : ℕ → Catalog) (hK : K ≤ J)
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1%(p : ℤ)+lift w.2.1*(p : ℤ)+shift)-globalKey w.2.2) :
    let I := rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
    LightReportingWantedSearch.time p shift left right NL NR I w D K ≤
      (domain I w).card*searchUnit h J D K+1300*K+1160 := by
  dsimp only
  let I := rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
  have hl := levels_time_le I w D hK
  have ht := terminal_time_le p shift A B C a b c left right eL eR hvL hvR w hK hkey
  change LightReportingTerminalStored.time p shift left right NL NR I w K ≤ _ at ht
  unfold LightReportingWantedSearch.time searchUnit
  nlinarith

theorem wanted_time_le {h J K NL NR old threshold : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (left right : ℕ → ℤ)
    (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i))
    (hvR : ∀ i : Fin NR, right i.val=c (eR i))
    (w : Wanted h J α) (D : ℕ → Catalog) (hK : K ≤ J)
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1%(p : ℤ)+lift w.2.1*(p : ℤ)+shift)-globalKey w.2.2) :
    let I := rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
    LightReportingWanted.time p shift left right NL NR old threshold I w D K ≤
      initialUnit h J D K+
        (if threshold < old+rootMass I w then 0 else rootMass I w*searchUnit h J D K) := by
  dsimp only
  let I := rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
  have hs := search_time_le p shift A B C a b c left right eL eR hvL hvR w D hK hkey
  change LightReportingWantedSearch.time p shift left right NL NR I w D K ≤
    (domain I w).card*searchUnit h J D K+1300*K+1160 at hs
  change LightReportingWanted.time p shift left right NL NR old threshold I w D K ≤
    initialUnit h J D K+
      (if threshold < old+rootMass I w then 0 else rootMass I w*searchUnit h J D K)
  unfold LightReportingWanted.time initialUnit
  by_cases hg : threshold < old+rootMass I w
  · simp only [if_pos hg]
    omega
  · simp only [if_neg hg]
    rw [rootMass_eq]
    omega

end ThreeSum.SharedTraversalCosts
