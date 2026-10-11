import Submission.ThreeSum.ThreeSumFastResourcesHybridPolynomial
import Submission.ThreeSum.ThreeSumHybridCosts

/-!
# Exact assembly and execution of the final hybrid caller

The supplied first537 procedures are followed by the relocated four-procedure
original-triple solver, one integer-power procedure, and the hybrid caller.
The two runtime guards use the actual size and the supplied magnitude bound.
-/

namespace ThreeSum.LightThreeSumHybridCore

open Light

set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

def body (κ cutoff : ℕ) : Stmt :=
  .ite (v 0 <' k cutoff)
    (.call 540 [v 0,v 1,v 2,v 3] 0)
    (.call 541 [v 0,k κ] 4 ;;
      .ite (v 4 <' v 1)
        (.call 540 [v 0,v 1,v 2,v 3] 0)
        (.call 536 [v 2,v 0,v 3] 0))

def libraries (fastP : Program) : Program :=
  ReportingHostRelocation.program fastP LightBruteThreeSum.program

def program (fastP : Program) (κ cutoff : ℕ) : Program :=
  libraries fastP++[LightNatPower.body,body κ cutoff]

theorem libraries_length {fastP : Program} (hlen : fastP.length=537) :
    (libraries fastP).length=541 := by
  simp only [libraries,ReportingHostRelocation.program,List.length_append,
    List.length_map,hlen,LightBruteThreeSum.program_length]

theorem program_length {fastP : Program} (hlen : fastP.length=537) (κ cutoff : ℕ) :
    (program fastP κ cutoff).length=543 := by
  simp only [program,List.length_append,List.length_cons,List.length_nil,
    libraries_length hlen]

theorem main_lookup {fastP : Program} (hlen : fastP.length=537) (κ cutoff : ℕ) :
    (program fastP κ cutoff)[542]?=some (body κ cutoff) := by
  have hh : (libraries fastP++[LightNatPower.body,body κ cutoff])[(libraries fastP).length+1]?=
      some (body κ cutoff) := by
    apply getElem?_append_length_add
    rfl
  simpa only [program,libraries_length hlen] using hh

theorem power_lookup {fastP : Program} (hlen : fastP.length=537) (κ cutoff : ℕ) :
    (program fastP κ cutoff)[541]?=some LightNatPower.body := by
  have hh : (libraries fastP++[LightNatPower.body,body κ cutoff])[(libraries fastP).length+0]?=
      some LightNatPower.body := by
    apply getElem?_append_length_add
    rfl
  simpa only [program,libraries_length hlen] using hh

theorem brute_meets {lim : Limits} {fastP : Program} {κ cutoff src n U free d : ℕ}
    (hlen : fastP.length=537) (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (hn : 0<n) (hsrc : src+n≤free) (H : (LightBruteThreeSum.need n U).Ok lim free d)
    (hread : ∀ i : Fin n, μ (src+i.val)=x i) (hx : ∀ i, |x i|≤(U : ℤ)) :
    Meets lim (program fastP κ cutoff) 540 d [n,U,src,free] μ (LightBruteThreeSum.time n)
      (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ Coloring.DistinctZeroSum x) ∧ ν=μ) := by
  have hh := LightBruteThreeSum.meets (P := LightBruteThreeSum.program) (pMain := 3)
    (pScan := 2) (pRow := 0) (pDivide := 1) x μ rfl rfl rfl rfl hn hsrc H hread hx
  have hrun := (ReportingHostRelocation.meets hh fastP).append
    [LightNatPower.body,body κ cutoff]
  rw [hlen] at hrun
  exact hrun

/-- The branch law is consumed only after both runtime guards succeed. The
    final concrete module discharges it using the verified fast executable. -/
theorem program_meets {lim : Limits} {fastP : Program} {κ cutoff src n U free d : ℕ}
    (hlen : fastP.length=537) (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (hn : 0<n) (hsrc : src+n≤free)
    (H : (ThreeSumFastResourcesHybrid.need κ cutoff n U).Ok lim free d)
    (hread : ∀ i : Fin n, μ (src+i.val)=x i) (hx : ∀ i, |x i|≤(U : ℤ))
    (hfast : cutoff≤n → U≤n^κ →
      Meets lim fastP 536 (d+1) [src,n,free] μ
        (LightThreeSumFastDriver.time (SharedTraversalCosts.colorBudget κ n) n)
        (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ν free)) :
    Meets lim (program fastP κ cutoff) 542 d [n,U,src,free] μ
      (ThreeSumHybridCosts.time κ cutoff n U)
      (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ν free) := by
  have hw := H.space
  have hword := ThreeSumFastResourcesHybrid.scalar_word_of_ok H
  have hd := ThreeSumFastResourcesHybrid.outer_depth_of_ok H
  have hregions := ThreeSumFastResourcesHybrid.source_region_of_ok H hsrc
  have hspace := hregions.1
  have hfreeWord := hregions.2
  have hκWord : (κ : ℤ)≤lim.word := by omega
  have hpowerWord := ThreeSumFastResourcesHybrid.power_word_of_ok H (i := κ) le_rfl
  have hpowerCast : ((n^κ : ℕ) : ℤ)=(n : ℤ)^κ := Nat.cast_pow n κ
  have hb := brute_meets (κ := κ) (cutoff := cutoff) hlen x μ hn hsrc
    (ThreeSumFastResourcesHybrid.brute_of_ok H) hread hx
  have hp := LightNatPower.meets (d := d+1) (b := n) (e := κ)
    (power_lookup hlen κ cutoff) μ hκWord
    (fun i hi => ThreeSumFastResourcesHybrid.power_word_of_ok H hi)
  by_cases hsmall : n<cutoff
  · rw [ThreeSumHybridCosts.time,if_pos (Or.inl hsmall)]
    apply Meets.of_body (main_lookup hlen κ cutoff)
    unfold body
    light_if hyes hno : n<cutoff
    · light_call hb with r ν ⟨hbool,hcorrect,hmem⟩
      subst ν
      exact ⟨hbool,hcorrect,SameOn.refl⟩
    · omega
  · by_cases hlarge : n^κ<U
    · rw [ThreeSumHybridCosts.time,if_pos (Or.inr hlarge)]
      apply Meets.of_body (main_lookup hlen κ cutoff)
      unfold body
      light_if hyes hno : n<cutoff
      · omega
      · light_call hp with power ν ⟨hpower,hmem⟩
        subst ν
        subst power
        light_if hyesU hnoU : n^κ<U
        · light_call hb with r ξ ⟨hbool,hcorrect,hmem⟩
          subst ξ
          exact ⟨hbool,hcorrect,SameOn.refl⟩
        · omega
    · rw [ThreeSumHybridCosts.time,if_neg (not_or_intro hsmall hlarge)]
      have hf := (hfast (by omega) (by omega)).append
        (LightBruteThreeSum.program.map (ReportingHostRelocation.relocate fastP.length)++
          [LightNatPower.body,body κ cutoff])
      have hf' : Meets lim (program fastP κ cutoff) 536 (d+1) [src,n,free] μ
          (LightThreeSumFastDriver.time (SharedTraversalCosts.colorBudget κ n) n)
          (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ν free) := by
        simpa only [program,libraries,ReportingHostRelocation.program,List.append_assoc] using hf
      apply Meets.of_body (main_lookup hlen κ cutoff)
      unfold body
      light_if hyes hno : n<cutoff
      · omega
      · light_call hp with power ν ⟨hpower,hmem⟩
        subst ν
        subst power
        light_if hyesU hnoU : n^κ<U
        · omega
        · light_call hf' with r ξ hh
          exact hh

end ThreeSum.LightThreeSumHybridCore
