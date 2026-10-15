import Submission.ThreeSum.TernaryPairedSelector
import Submission.ThreeSum.TernaryPairedRecurrence

namespace ThreeSum.TernaryPairedBudgetSelector
open Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

/-- Exact upper-budget selection. The initial paired potential is never
computed; only its proved integer upper bound U is used by the machine. -/
theorem exists_budget_row {Ω : Type*} [DecidableEq Ω]
    (S : Finset Ω) (hS : S.Nonempty) (a c p s j U N curPi curB curC : ℕ)
    (ha : 0<a) (hp : 0<p) (nextPi nextB nextC : Ω→ℕ)
    (hPi : a*(∑ x∈S,nextPi x)≤3*S.card*c*curPi)
    (hB : p*(∑ x∈S,nextB x)≤3*S.card*curB)
    (hC : p*(∑ x∈S,nextC x)≤3*S.card*curC)
    (hPiBudget : a^j*curPi≤(9*c)^j*U)
    (hBBudget : p^j*curB≤9^j*N) (hCBudget : p^j*curC≤9^j*N) :
    ∃ x∈S,
      a^(j+1)*(s*nextPi x)≤s*(9*c)^(j+1)*U ∧
      p^(j+1)*nextB x≤9^(j+1)*N ∧ p^(j+1)*nextC x≤9^(j+1)*N := by
  let f : Fin 3→Ω→ℕ := ![fun x => s*nextPi x,nextB,nextC]
  let num : Fin 3→ℕ := ![s*c*(9*c)^j*U,9^j*N,9^j*N]
  let den : Fin 3→ℕ := ![a^(j+1),p^(j+1),p^(j+1)]
  have hPi' : den 0*(∑ x∈S,f 0 x)≤3*S.card*num 0 := by
    change a^(j+1)*(∑ x∈S,s*nextPi x)≤3*S.card*(s*c*(9*c)^j*U)
    rw [←mul_sum]
    calc
      _ = s*a^j*(a*(∑ x∈S,nextPi x)) := by rw [pow_succ]; ring
      _ ≤ s*a^j*(3*S.card*c*curPi) := Nat.mul_le_mul_left _ hPi
      _ = (3*S.card*s*c)*(a^j*curPi) := by ring
      _ ≤ (3*S.card*s*c)*((9*c)^j*U) := Nat.mul_le_mul_left _ hPiBudget
      _ = _ := by ring
  have hB' : den 1*(∑ x∈S,f 1 x)≤3*S.card*num 1 := by
    change p^(j+1)*(∑ x∈S,nextB x)≤3*S.card*(9^j*N)
    calc
      _ = p^j*(p*(∑ x∈S,nextB x)) := by rw [pow_succ]; ring
      _ ≤ p^j*(3*S.card*curB) := Nat.mul_le_mul_left _ hB
      _ = (3*S.card)*(p^j*curB) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hBBudget
  have hC' : den 2*(∑ x∈S,f 2 x)≤3*S.card*num 2 := by
    change p^(j+1)*(∑ x∈S,nextC x)≤3*S.card*(9^j*N)
    calc
      _ = p^j*(p*(∑ x∈S,nextC x)) := by rw [pow_succ]; ring
      _ ≤ p^j*(3*S.card*curC) := Nat.mul_le_mul_left _ hC
      _ = (3*S.card)*(p^j*curC) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hCBudget
  obtain ⟨x,hx,hs⟩ := TernaryPairedSelector.exists_cross_multiplied S hS f num den
    (by intro i; fin_cases i <;> dsimp [den] <;> positivity)
    (by intro i; fin_cases i; exact hPi'; exact hB'; exact hC')
  refine ⟨x,hx,?_,?_,?_⟩
  · calc
      _ ≤ 9*(s*c*(9*c)^j*U) := hs 0
      _ = _ := by rw [pow_succ]; ring
  · calc
      _ ≤ 9*(9^j*N) := hs 1
      _ = _ := by rw [pow_succ]; ring
  · calc
      _ ≤ 9*(9^j*N) := hs 2
      _ = _ := by rw [pow_succ]; ring

/-- Cancellation used after the actual scan has checked its scaled score. -/
theorem cancel_scale (a b s value budget : ℕ) (hs : 0<s)
    (h : a*(s*value)≤s*b*budget) : a*value≤b*budget := by
  apply Nat.le_of_mul_le_mul_left (c := s) ?_ hs
  simpa only [mul_assoc,mul_left_comm,mul_comm] using h

/-- A single weighted budget at the final depth suffices; no evaluation
of Pi0 and no per-step comparison with its exact value is required. -/
theorem terminal_fourth_bound (K M a b U value r : ℕ) (hb : 0<b)
    (hbudget : a^r*value≤b^r*U) (hdrift : b^4*M^(4*K+3)≤a^4) :
    M^(r*(4*K+3))*value^4≤U^4 := by
  have hp := Nat.pow_le_pow_left hbudget 4
  have hd := Nat.pow_le_pow_left hdrift r
  have hh : (b^4)^r*(M^(r*(4*K+3))*value^4)≤(b^4)^r*U^4 := by
    calc
      _ = (b^4*M^(4*K+3))^r*value^4 := by
        have hm : (M^(4*K+3))^r=M^(r*(4*K+3)) := by rw [←pow_mul,Nat.mul_comm]
        rw [mul_pow,hm]
        ring
      _ ≤ (a^4)^r*value^4 := Nat.mul_le_mul_right _ hd
      _ = (a^r*value)^4 := by
        have he : (a^4)^r=(a^r)^4 := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
        rw [mul_pow,he]
      _ ≤ (b^r*U)^4 := hp
      _ = _ := by
        have he : (b^r)^4=(b^4)^r := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
        rw [mul_pow,he]
  exact Nat.le_of_mul_le_mul_left hh (pow_pos (pow_pos hb 4) r)

theorem terminal_zero (K M a b U value r n C : ℕ) (hb : 0<b)
    (hbudget : a^r*value≤b^r*U) (hdrift : b^4*M^(4*K+3)≤a^4)
    (hcover : n^2≤M^r) (hinit : U^4≤C*n^(8*K+5)) (hn : C<n) : value=0 := by
  have hbound := terminal_fourth_bound K M a b U value r hb hbudget hdrift
  have hbase : n^(8*K+6)≤M^(r*(4*K+3)) := by
    simpa only [←pow_mul,show 2*(4*K+3)=8*K+6 by ring] using Nat.pow_le_pow_left hcover (4*K+3)
  have hnpos : 0<n := by omega
  have hstrict : C*n^(8*K+5)<n^(8*K+6) := by
    have hh := Nat.mul_lt_mul_of_pos_right hn (pow_pos hnpos (8*K+5))
    simpa only [show 8*K+6=(8*K+5)+1 by omega,pow_succ,mul_comm] using hh
  by_contra hz
  have hp : 1≤value^4 := Nat.one_le_pow 4 value (Nat.pos_of_ne_zero hz)
  have hm := Nat.mul_le_mul_left (M^(r*(4*K+3))) hp
  simp only [mul_one] at hm
  omega

end ThreeSum.TernaryPairedBudgetSelector
