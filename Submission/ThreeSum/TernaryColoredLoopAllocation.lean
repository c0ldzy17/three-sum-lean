import Submission.ThreeSum.TernaryColoredLoopSetup

noncomputable section
namespace ThreeSum.TernaryColoredLoopAllocation
open Light TernaryArenaLayout TernaryArenaSourceSetup TernaryArenaSeedCandidate
open TernaryConcreteProfile TernaryLocalParameters TernaryColoredLoopSetup
open TernaryArenaPrefixFootprints
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {κ : ℕ}

/-- The mathematical selector's drift is exactly the compiled integer
constant, including every local map occurrence and output word. -/
theorem beta_eq_drift (P : Profile κ) :
    9*TernaryArenaBudgetExistence.pairFactor P.m P.F P.K=P.drift := by
  unfold TernaryArenaBudgetExistence.pairFactor Profile.drift Profile.M
    TernaryCoverScale.outputSize TernaryGoodOutputCatalog.Rbar
  ring

theorem drift_scale_pos (P : Profile κ) : 1≤P.drift*P.scale := by
  have hF:=P.F_gt_one
  have hM:=P.M_gt_one
  have hR : 0<TernaryGoodOutputCatalog.Rbar P.m := by
    unfold TernaryGoodOutputCatalog.Rbar
    positivity
  have hs : 0<P.scale := by unfold Profile.scale;positivity
  have hd : 0<P.drift := by unfold Profile.drift;positivity
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))

/-- Exact preparation-envelope arithmetic at every actual positive prefix.
The paired budget is the value written by the real initializer. -/
theorem prepare_envelope (P : Profile κ) (n free : ℕ) (A B C : List ℤ)
    (hA : A.length≤n) (j : ℕ) (hj : j<rounds P n) :
    TernaryArenaPrefixPrepare.envelope
      (TernaryArenaPrefixPrepare.inputs P.p P.m P.F j (J P n) n (initialBudget P n A)
        (P.p^(2*P.K)) (9*TernaryArenaBudgetExistence.pairFactor P.m P.F P.K)
        (2^(fixedPi P.m 2*P.K)) (input P n free A B C) P.output)≤
      (input P n free A B C).capacity := by
  rw [beta_eq_drift]
  have hh := TernaryArenaPrefixPrepareAllocation.allocated_initial P.maps P.threshold P.cap P.M
    P.radix P.K P.H P.drift P.scale n (n^κ) j (A.length*2^(J P n)) P.allocation
    (input P n free A B C) P.output
    (show j+1≤Nat.clog P.M (n^2) by change j<Nat.clog P.M (n^2) at hj;omega)
    (show (input P n free A B C).capacity=capacity P.allocation.D P.allocation.E (n+n^κ) from rfl)
    (drift_scale_pos P) (Nat.mul_le_mul_right _ hA)
  exact hh

/-- The real selector's cross products are covered by the fourth-power
allocation envelope, using the exact six compiled threshold values. -/
theorem selector_word {lim : Limits} {depth : ℕ}
    (P : Profile κ) (n free : ℕ) (A B C : List ℤ) (hA : A.length≤n)
    (hok : (TernaryArenaAllocationResources.need P.allocation n (n^κ)).Ok lim
      (input P n free A B C).free depth) (j : ℕ) (hj : j<rounds P n) :
    (LightTernaryRowSelector.word (q P n*q P n)
      (numbers P.maps P.threshold P.cap P.M P.radix P.K P.H P.drift P.scale n (n^κ) (j+1)).candidateScore
      (P.p^(j+1)) (P.p^(j+1)) ((P.p^(2*P.K))^(j+1))
      (9^(j+1)*n^2) (9^(j+1)*n^2)
      (initialBudget P n A*((9*TernaryArenaBudgetExistence.pairFactor P.m P.F P.K)*
        (2^(fixedPi P.m 2*P.K)))^(j+1)) : ℤ)≤lim.word := by
  rw [beta_eq_drift]
  have hh := TernaryArenaSelectorAllocation.selector P.maps P.threshold P.cap P.M P.radix P.K
    P.H P.drift P.scale P.allocation n (n^κ) (j+1) (A.length*2^(J P n))
    (input P n free A B C).free
    (show j+1≤Nat.clog P.M (n^2) by change j<Nat.clog P.M (n^2) at hj;omega)
    (Nat.mul_le_mul_right _ hA) hok
  simpa only [q,dim,pow_two,initialBudget,J,Profile.scale,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hh

/-- Round and radix-power words come from the same universal allocation;
no independently supplied hardware bounds remain. -/
theorem control_words {lim : Limits} {depth : ℕ}
    (P : Profile κ) (n free : ℕ) (A B C : List ℤ)
    (hok : (TernaryArenaAllocationResources.need P.allocation n (n^κ)).Ok lim
      (input P n free A B C).free depth) :
    (rounds P n : ℤ)≤lim.word ∧
      ∀j≤rounds P n, ((P.p^j : ℕ):ℤ)≤lim.word := by
  have hw := (TernaryArenaAllocationResources.ok P.allocation hok).2.1
  have hd := (P.allocation.fits n (n^κ) (rounds P n) (by rfl)).depth
  have hr : rounds P n≤cells P n := by
    dsimp only [numbers] at hd
    change _≤cells P n at hd
    omega
  refine ⟨(Int.ofNat_le.mpr hr).trans hw,?_⟩
  intro j hj
  have hp := (TernaryArenaSelectorAllocation.controls P.maps P.threshold P.cap P.M P.radix P.K
    P.H P.drift P.scale n (n^κ) j 0 (Nat.zero_le _)).2.1
  have hh := P.allocation.total_le n (n^κ) j hj
  exact (Int.ofNat_le.mpr (hp.trans hh)).trans hw

end ThreeSum.TernaryColoredLoopAllocation
