import Submission.ThreeSum.LightReportingTerminal
import Submission.ThreeSum.ReportingHostTerminalOriginal

/-!
# Exact terminal-prefix order, summed cost, and original completeness

The prefix batch consumes the actual retained frontier order. Every local
scan keeps its own selected-pair charge; their sum is bounded by the exact
original raw mass at the partial depth.
-/

namespace ThreeSum.ReportingHostTerminalFrontier

open Finset BlockRows BlockEncoding GlobalEncoding RawIncidences RawReporting RawPrefixCounts
open StoredReporting LightBlockSourceBuild
open scoped BigOperators

set_option maxHeartbeats 2400000
set_option maxRecDepth 10000

def prefixAt {h : ℕ} (pres : List (List (Finset (Fin (512*h))))) (i : ℕ) : List (Finset (Fin (512*h))) :=
  pres[i]?.getD []

theorem prefixAt_eq_get {h i : ℕ} (pres : List (List (Finset (Fin (512*h))))) (hi : i<pres.length) :
    prefixAt pres i=pres[i] := by simp only [prefixAt,List.getElem?_eq_getElem hi,Option.getD_some]

def Hit {h J : ℕ} (av : ℤ) (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : GlobalOutput h J) (k : ℕ) (pres : List (List (Finset (Fin (512*h))))) (n : ℕ) : Prop :=
  ∃ i<n, ReportingHostTerminalBatch.Hit av p shift left right NL NR q k (prefixAt pres i)

theorem hit_succ {h J : ℕ} (av : ℤ) (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : GlobalOutput h J) (k : ℕ) (pres : List (List (Finset (Fin (512*h))))) (n : ℕ) :
    Hit av p shift left right NL NR q k pres (n+1) ↔
      Hit av p shift left right NL NR q k pres n ∨
      ReportingHostTerminalBatch.Hit av p shift left right NL NR q k (prefixAt pres n) := by
  constructor
  · rintro ⟨i,hi,hh⟩
    by_cases hin : i<n
    · exact Or.inl ⟨i,hin,hh⟩
    · have he : i=n := by omega
      exact Or.inr (he ▸ hh)
  · rintro (⟨i,hi,hh⟩ | hh)
    · exact ⟨i,by omega,hh⟩
    · exact ⟨n,by omega,hh⟩

theorem hit_all {h J : ℕ} (av : ℤ) (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : GlobalOutput h J) (k : ℕ) (pres : List (List (Finset (Fin (512*h))))) :
    Hit av p shift left right NL NR q k pres pres.length ↔
      ∃ pre∈pres, ReportingHostTerminalBatch.Hit av p shift left right NL NR q k pre := by
  constructor
  · rintro ⟨i,hi,hh⟩
    exact ⟨pres[i],List.getElem_mem hi,(prefixAt_eq_get pres hi) ▸ hh⟩
  · rintro ⟨pre,hpre,hh⟩
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hpre
    exact ⟨i,hi,by simpa only [prefixAt_eq_get pres hi,he] using hh⟩

def time {h J : ℕ} (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : GlobalOutput h J) (k : ℕ) (pres : List (List (Finset (Fin (512*h))))) : ℕ→ℕ
  | 0 => 30
  | n+1 => time p shift left right NL NR q k pres n+
      LightReportingTerminal.time p shift left right NL NR q k (prefixAt pres n)+300

theorem time_all {h J : ℕ} (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : GlobalOutput h J) (k : ℕ) (pres : List (List (Finset (Fin (512*h))))) :
    time p shift left right NL NR q k pres pres.length=
      (pres.map (fun pre => LightReportingTerminal.time p shift left right NL NR q k pre+300)).sum+30 := by
  have hsum (n : ℕ) : time p shift left right NL NR q k pres n=
      (∑ i∈range n, (LightReportingTerminal.time p shift left right NL NR q k (prefixAt pres i)+300))+30 := by
    induction n with
    | zero => simp [time]
    | succ n ih => simp only [time,Finset.sum_range_succ,ih]; omega
  rw [hsum,Finset.sum_range]
  congr 1
  calc
    (∑ i : Fin pres.length, (LightReportingTerminal.time p shift left right NL NR q k (prefixAt pres i.val)+300)) =
        ∑ i : Fin pres.length, (LightReportingTerminal.time p shift left right NL NR q k pres[i.val]+300) :=
      Finset.sum_congr rfl (fun i _ => by rw [prefixAt_eq_get pres i.isLt])
    _ = _ := Fin.sum_univ_fun_getElem pres
      (fun pre => LightReportingTerminal.time p shift left right NL NR q k pre+300)

def charge (h J k : ℕ) : ℕ :=
  LightReportingBinomial.time ((J-k)*(2*h))+LightReportingTerminalMasks.time h J k+
    LightReportingTerminalPreparation.time h J (LightReportingTerminalMasks.count h J k)+
    (2*LightResidues.residueBudget (endpointBound h J)+1300)*2^((J-k)*(2*h))+1830

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem prefix_time_le {h J k NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k≤J) (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1∈A ∧ globalModulus h J ∣ (a w.1%(p : ℤ)+lift w.2.1*(p : ℤ)+shift)-globalKey w.2.2) :
    LightReportingTerminal.time p shift left right NL NR w.2.2 k pre+300 ≤
      240*prefixQuery (rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w k pre+charge h J k := by
  have hh := ReportingHostTerminalBatch.time_le p shift A B C a b c left right eL eR hvL hvR w pre hk hp hkey
  unfold LightReportingTerminal.time LightReportingTerminalPrepared.time charge
  omega

theorem frontier_time_le {h J k NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (w : Wanted h J α) (hk : k≤J)
    (hkey : w.1∈A ∧ globalModulus h J ∣ (a w.1%(p : ℤ)+lift w.2.1*(p : ℤ)+shift)-globalKey w.2.2) :
    let I := rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
    let pres := ReportingHostFrontier.frontier I w k
    time p shift left right NL NR w.2.2 k pres pres.length≤
      240*(domain I w).card+charge h J k*pres.length+30 := by
  dsimp only
  rw [time_all]
  let I := rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
  let pres := ReportingHostFrontier.frontier I w k
  have hsum : (pres.map (fun pre => LightReportingTerminal.time p shift left right NL NR w.2.2 k pre+300)).sum≤
      (pres.map (fun pre => 240*prefixQuery I w k pre+charge h J k)).sum := by
    apply List.sum_le_sum
    intro pre hpre
    exact prefix_time_le p shift A B C a b c left right eL eR hvL hvR w pre hk
      (ReportingHostPositive.frontier_valid I w hk hpre) hkey
  rw [ReportingHostTerminalCosts.sum_linear,ReportingHostTerminalCosts.frontier_mass I w hk] at hsum
  dsimp only [pres,I] at hsum
  omega

end ThreeSum.ReportingHostTerminalFrontier
