import Submission.ThreeSum.LightReportingWantedDispatch
import Submission.ThreeSum.ReportingHostWantedPrefix

/-!
# Ascending physical wanted scan with immediate successful return

The recursive prefix runs before slot n-1. A positive prefix result returns
immediately; otherwise exactly the next physical slot is dispatched. The
counter is the exact mass of the executed prefix, including the first slot
whose guard or original-value test succeeds.
-/

namespace ThreeSum.LightReportingWantedScan

open Light Finset SharedTraversalCosts LightReportingWantedDispatch

set_option maxHeartbeats 2600000
set_option maxRecDepth 24000

def Accepted (mass : ℕ→ℕ) (hit : ℕ→Prop) (threshold n : ℕ) : Prop :=
  threshold<prefixMass mass n ∨ ∃ i<n, hit i

theorem prefixMass_mono (mass : ℕ→ℕ) {i j : ℕ} (hij : i≤j) :
    prefixMass mass i≤prefixMass mass j := by
  unfold prefixMass
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hij)

theorem accepted_mono (mass : ℕ→ℕ) (hit : ℕ→Prop) (threshold : ℕ)
    {i j : ℕ} (hij : i≤j) (hi : Accepted mass hit threshold i) : Accepted mass hit threshold j := by
  rcases hi with hi | ⟨k,hk,hh⟩
  · exact Or.inl (hi.trans_le (prefixMass_mono mass hij))
  · exact Or.inr ⟨k,hk.trans_le hij,hh⟩

theorem accepted_zero (mass : ℕ→ℕ) (hit : ℕ→Prop) (threshold : ℕ) :
    ¬Accepted mass hit threshold 0 := by simp [Accepted,prefixMass_zero]

theorem accepted_succ (mass : ℕ→ℕ) (hit : ℕ→Prop) (threshold n : ℕ) :
    Accepted mass hit threshold (n+1) ↔ Accepted mass hit threshold n ∨
      threshold<prefixMass mass n+mass n ∨ hit n := by
  constructor
  · rintro (hdense | ⟨i,hi,hhit⟩)
    · exact Or.inr (Or.inl (by simpa only [prefixMass_succ] using hdense))
    · by_cases hin : i<n
      · exact Or.inl (Or.inr ⟨i,hin,hhit⟩)
      · have he : i=n := by omega
        exact Or.inr (Or.inr (he ▸ hhit))
  · rintro (hprev | hdense | hhit)
    · exact accepted_mono mass hit threshold (by omega) hprev
    · exact Or.inl (by simpa only [prefixMass_succ] using hdense)
    · exact Or.inr ⟨n,by omega,hhit⟩

def Counter (mass : ℕ→ℕ) (hit : ℕ→Prop) (threshold count counter : ℕ)
    (result : ℤ) (μ : ℕ→ℤ) : Prop :=
  ∃ k≤count, μ counter=(prefixMass mass k : ℤ) ∧
    (result=0 → k=count) ∧
    (result=1 → Accepted mass hit threshold k ∧ ∀ i<k, ¬Accepted mass hit threshold i)

def time (stepTime : ℕ→ℕ) : ℕ→ℕ
  | 0 => 30
  | n+1 => time stepTime n+stepTime n+300

def body (pSelf pDispatch : ℕ) : Stmt :=
  .ite (k 0 <' v 0)
    (.call pSelf [v 0 -' k 1,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,
      v 14,v 15,v 16,v 17,v 18,v 19,v 20,v 21,v 22] 23 ;;
      .ite (k 0 <' v 23)
        (.set 0 (k 1))
        (.call pDispatch [v 0 -' k 1,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,
          v 14,v 15,v 16,v 17,v 18,v 19,v 20,v 21,v 22] 0))
    (.set 0 (k 0))

def program : Program := LightReportingWantedDispatch.program++[body 152 151]

/-- The invariant and per-slot law are supplied by the exact retained
pipeline specialization. Every call here remains the fixed actual152
dispatcher, and the bound is its literal ascending-prefix cost sum. -/
theorem program_meets {lim : Limits} {μ : ℕ→ℤ} {C : Config}
    {mass stepTime : ℕ→ℕ} {hit : ℕ→Prop} {Inv : (ℕ→ℤ)→Prop}
    {threshold n N D d : ℕ}
    (hw : (lim.space : ℤ)≤lim.word) (hspace : N+1≤lim.space)
    (hD : D+1≤lim.depth) (hd : d+n≤D) (hn : n≤N)
    (hInv : Inv μ) (hzero : μ C.counter=0)
    (hstep : ∀ i<N, ∀ ν, ∀ e, e+i≤D+1 → Inv ν →
      ν C.counter=(prefixMass mass i : ℤ) →
      Meets lim LightReportingWantedDispatch.program 151 e (arguments C i) ν (stepTime i)
        (fun r ξ => (r=0 ∨ r=1) ∧
          (r=1 ↔ threshold<prefixMass mass i+mass i ∨ hit i) ∧
          ξ C.counter=((prefixMass mass i+mass i : ℕ) : ℤ) ∧ Inv ξ ∧
          KeptBut ν ξ C.layoutHeader C.counter 1)) :
    Meets lim program 152 d (arguments C n) μ (time stepTime n)
      (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ Accepted mass hit threshold n) ∧
        Counter mass hit threshold n C.counter r ν ∧ Inv ν ∧
        KeptBut μ ν C.layoutHeader C.counter 1) := by
  induction n generalizing μ d with
  | zero =>
      apply Meets.of_body (p := 152) (by rfl : program[152]?=some (body 152 151))
      unfold body time arguments
      light_if hbad hno : (0 : ℤ)<0
      · omega
      · light_set (0 : ℕ)
        refine ⟨by simp,by simp [accepted_zero],?_,hInv,SameOn.refl⟩
        exact ⟨0,le_rfl,by simpa only [prefixMass_zero,Int.natCast_zero] using hzero,
          fun _ => rfl,by intro hh; norm_num at hh⟩
  | succ n ih =>
      apply Meets.of_body (p := 152) (by rfl : program[152]?=some (body 152 151))
      unfold body arguments
      rw [time]
      light_if hyes hbad : (0 : ℤ)<((n+1 : ℕ) : ℤ)
      · have hprefix := ih (μ := μ) (d := d+1) (by omega) (by omega) hInv hzero
        light_call hprefix using arguments with prev ν ⟨hprevBool,hprev,hcounter,hInvν,hkeep⟩
        have hprevRange : 0≤prev ∧ prev≤1 := by rcases hprevBool with hh | hh <;> omega
        light_if hstop hcontinue : (0 : ℤ)<prev
        · have hp : prev=1 := by omega
          have ha := hprev.mp hp
          have hanext := accepted_mono mass hit threshold (by omega : n≤n+1) ha
          light_set (1 : ℕ)
          refine ⟨by simp,by simpa using hanext,?_,hInvν,hkeep⟩
          obtain ⟨k,hk,hread,_,hfirst⟩ := hcounter
          exact ⟨k,by omega,hread,by intro hh; norm_num at hh,fun _ => hfirst hp⟩
        · have hp : prev=0 := by omega
          have hnot : ¬Accepted mass hit threshold n := by intro hh; have := hprev.mpr hh; omega
          obtain ⟨k,hk,hread,hfull,_⟩ := hcounter
          have hkfull := hfull hp
          have hreadPrefix : ν C.counter=(prefixMass mass n : ℤ) := by simpa only [hkfull] using hread
          have hnext := (hstep n (by omega) ν (d+1) (by omega) hInvν hreadPrefix).append [body 152 151]
          change Meets lim program 151 (d+1) _ ν (stepTime n) _ at hnext
          light_call hnext using arguments with result ξ ⟨hbool,hresult,hreadξ,hInvξ,hkeepNext⟩
          have heq : result=1 ↔ Accepted mass hit threshold (n+1) := by
            rw [accepted_succ]
            simpa only [hnot,false_or] using hresult
          refine ⟨hbool,heq,?_,hInvξ,hkeep.trans hkeepNext⟩
          refine ⟨n+1,le_rfl,?_,fun _ => rfl,?_⟩
          · simpa only [prefixMass_succ] using hreadξ
          · intro hh
            refine ⟨heq.mp hh,?_⟩
            intro i hi haccepted
            exact hnot (accepted_mono mass hit threshold (by omega : i≤n) haccepted)
      · omega

end ThreeSum.LightReportingWantedScan
