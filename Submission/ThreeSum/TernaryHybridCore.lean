import Submission.ThreeSum.TernaryHybridResources
import Submission.ThreeSum.ReportingHostRelocation

/-!
# Concrete finite-cutoff wrapper for an arbitrary fast 3SUM executable

The appended original-triple scan and integer-power procedure are fully
specified programs.  Procedure indices depend on the actual fast program
length.  The wrapper consumes the fast program's own semantic, resource,
and time contract after its two runtime guards have succeeded.
-/

namespace ThreeSum.TernaryHybridCore

open Light

set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

def body (fastSize fastProc κ cutoff : ℕ) : Stmt :=
  .ite (v 0 <' k cutoff)
    (.call (fastSize+3) [v 0,v 1,v 2,v 3] 0)
    (.call (fastSize+4) [v 0,k κ] 4 ;;
      .ite (v 4 <' v 1)
        (.call (fastSize+3) [v 0,v 1,v 2,v 3] 0)
        (.call fastProc [v 2,v 0,v 3] 0))

def libraries (fastP : Program) : Program :=
  ReportingHostRelocation.program fastP LightBruteThreeSum.program

def program (fastP : Program) (fastProc κ cutoff : ℕ) : Program :=
  libraries fastP++[LightNatPower.body,body fastP.length fastProc κ cutoff]

def time (fastTime : ℕ → ℕ) (κ cutoff n U : ℕ) : ℕ :=
  if n<cutoff ∨ n^κ<U then
    LightBruteThreeSum.time n+LightNatPower.time κ+1000
  else fastTime n+LightNatPower.time κ+1000

theorem libraries_length (fastP : Program) :
    (libraries fastP).length=fastP.length+4 := by
  simp only [libraries,ReportingHostRelocation.program,List.length_append,
    List.length_map,LightBruteThreeSum.program_length]

theorem program_length (fastP : Program) (fastProc κ cutoff : ℕ) :
    (program fastP fastProc κ cutoff).length=fastP.length+6 := by
  simp only [program,List.length_append,List.length_cons,List.length_nil,
    libraries_length]

theorem main_lookup (fastP : Program) (fastProc κ cutoff : ℕ) :
    (program fastP fastProc κ cutoff)[fastP.length+5]?=
      some (body fastP.length fastProc κ cutoff) := by
  have hh : (libraries fastP++[LightNatPower.body,body fastP.length fastProc κ cutoff])[(libraries fastP).length+1]?=
      some (body fastP.length fastProc κ cutoff) := by
    apply getElem?_append_length_add
    rfl
  simpa only [program,libraries_length,show fastP.length+4+1=fastP.length+5 by omega] using hh

theorem power_lookup (fastP : Program) (fastProc κ cutoff : ℕ) :
    (program fastP fastProc κ cutoff)[fastP.length+4]?=some LightNatPower.body := by
  have hh : (libraries fastP++[LightNatPower.body,body fastP.length fastProc κ cutoff])[(libraries fastP).length+0]?=
      some LightNatPower.body := by
    apply getElem?_append_length_add
    rfl
  simpa only [program,libraries_length,Nat.add_zero] using hh

theorem brute_meets {lim : Limits} {fastP : Program} {fastProc κ cutoff src n U free d : ℕ}
    (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (hn : 0<n) (hsrc : src+n≤free) (H : (LightBruteThreeSum.need n U).Ok lim free d)
    (hread : ∀ i : Fin n, μ (src+i.val)=x i) (hx : ∀ i, |x i|≤(U : ℤ)) :
    Meets lim (program fastP fastProc κ cutoff) (fastP.length+3) d [n,U,src,free] μ (LightBruteThreeSum.time n)
      (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ Coloring.DistinctZeroSum x) ∧ ν=μ) := by
  have hh := LightBruteThreeSum.meets (P := LightBruteThreeSum.program) (pMain := 3)
    (pScan := 2) (pRow := 0) (pDivide := 1) x μ rfl rfl rfl rfl hn hsrc H hread hx
  have hrun := (ReportingHostRelocation.meets hh fastP).append
    [LightNatPower.body,body fastP.length fastProc κ cutoff]
  exact hrun

variable (fastNeed : ℕ → ℕ → Need) (fastTime : ℕ → ℕ)

/-- The branch law is consumed only after both runtime guards succeed. The
    concrete fast module must discharge it using its actual executable. -/
theorem program_meets {lim : Limits} {fastP : Program} {fastProc κ cutoff src n U free d : ℕ}
    (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (hn : 0<n) (hsrc : src+n≤free)
    (H : (TernaryHybridResources.need fastNeed κ cutoff n U).Ok lim free d)
    (hread : ∀ i : Fin n, μ (src+i.val)=x i) (hx : ∀ i, |x i|≤(U : ℤ))
    (hfast : cutoff≤n → U≤n^κ →
      Meets lim fastP fastProc (d+1) [src,n,free] μ
        (fastTime n)
        (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ν free)) :
    Meets lim (program fastP fastProc κ cutoff) (fastP.length+5) d [n,U,src,free] μ
      (time fastTime κ cutoff n U)
      (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ν free) := by
  have hw := H.space
  have hword := TernaryHybridResources.scalar_word_of_ok fastNeed H
  have hd := TernaryHybridResources.outer_depth_of_ok fastNeed H
  have hregions := TernaryHybridResources.source_region_of_ok fastNeed H hsrc
  have hspace := hregions.1
  have hfreeWord := hregions.2
  have hκWord : (κ : ℤ)≤lim.word := by omega
  have hpowerWord := TernaryHybridResources.power_word_of_ok fastNeed H (i := κ) le_rfl
  have hpowerCast : ((n^κ : ℕ) : ℤ)=(n : ℤ)^κ := Nat.cast_pow n κ
  have hb := brute_meets (fastP := fastP) (fastProc := fastProc) (κ := κ) (cutoff := cutoff) x μ hn hsrc
    (TernaryHybridResources.brute_of_ok fastNeed H) hread hx
  have hp := LightNatPower.meets (d := d+1) (b := n) (e := κ)
    (power_lookup fastP fastProc κ cutoff) μ hκWord
    (fun i hi => TernaryHybridResources.power_word_of_ok fastNeed H hi)
  by_cases hsmall : n<cutoff
  · rw [time,if_pos (Or.inl hsmall)]
    apply Meets.of_body (main_lookup fastP fastProc κ cutoff)
    unfold body
    light_if hyes hno : n<cutoff
    · light_call hb with r ν ⟨hbool,hcorrect,hmem⟩
      subst ν
      exact ⟨hbool,hcorrect,SameOn.refl⟩
    · omega
  · by_cases hlarge : n^κ<U
    · rw [time,if_pos (Or.inr hlarge)]
      apply Meets.of_body (main_lookup fastP fastProc κ cutoff)
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
    · rw [time,if_neg (not_or_intro hsmall hlarge)]
      have hf := (hfast (by omega) (by omega)).append
        (LightBruteThreeSum.program.map (ReportingHostRelocation.relocate fastP.length)++
          [LightNatPower.body,body fastP.length fastProc κ cutoff])
      have hf' : Meets lim (program fastP fastProc κ cutoff) fastProc (d+1) [src,n,free] μ
          (fastTime n)
          (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ν free) := by
        simpa only [program,libraries,ReportingHostRelocation.program,List.append_assoc] using hf
      apply Meets.of_body (main_lookup fastP fastProc κ cutoff)
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

/-- The fast branch law uses its own resource need and running time.  Its
successful guards provide the complete original input magnitude condition. -/
theorem program_meets_of_fast {lim : Limits} {fastP : Program}
    {fastProc κ cutoff src n U free d : ℕ}
    (x : Fin n → ℤ) (μ : ℕ → ℤ) (hn : 0 < n) (hsrc : src+n ≤ free)
    (H : (TernaryHybridResources.need fastNeed κ cutoff n U).Ok lim free d)
    (hinput : Seg μ src (List.ofFn x)) (hx : ∀ i, |x i| ≤ (U : ℤ))
    (hfast : ∀ {lim : Limits} {src n free d : ℕ},
      ∀ (x : Fin n → ℤ) (μ : ℕ → ℤ),
        cutoff ≤ n → 0 < n → src+n ≤ free →
        (fastNeed n (n^κ)).Ok lim free d →
        Seg μ src (List.ofFn x) → (∀ i, |x i| ≤ ((n^κ : ℕ) : ℤ)) →
        Meets lim fastP fastProc d [src,n,free] μ (fastTime n)
          (fun r ν => (r=0 ∨ r=1) ∧
            (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ν free)) :
    Meets lim (program fastP fastProc κ cutoff) (fastP.length+5) d
      [n,U,src,free] μ (time fastTime κ cutoff n U)
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ν free) := by
  have hread : ∀ i : Fin n, μ (src+i.val)=x i := by
    intro i
    have hi : i.val < (List.ofFn x).length := by
      simpa only [List.length_ofFn] using i.isLt
    simpa only [List.getElem_ofFn] using hinput i.val hi
  apply program_meets fastNeed fastTime x μ hn hsrc H hread hx
  intro hcutoff hU
  apply hfast x μ hcutoff hn hsrc
    (TernaryHybridResources.fast_of_ok fastNeed H) hinput
  intro i
  exact (hx i).trans (Int.ofNat_le.mpr hU)

/-- Compile the fully specified hybrid caller into the original 3SUM task
contract.  No change to the task, its distinct-position predicate, or its
calling convention occurs. -/
theorem solves_of_fast {fastP : Program} {fastProc κ cutoff : ℕ}
    (hfast : ∀ {lim : Limits} {src n free d : ℕ},
      ∀ (x : Fin n → ℤ) (μ : ℕ → ℤ),
        cutoff ≤ n → 0 < n → src+n ≤ free →
        (fastNeed n (n^κ)).Ok lim free d →
        Seg μ src (List.ofFn x) → (∀ i, |x i| ≤ ((n^κ : ℕ) : ℤ)) →
        Meets lim fastP fastProc d [src,n,free] μ (fastTime n)
          (fun r ν => (r=0 ∨ r=1) ∧
            (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ν free)) :
    Solves s3Task (program fastP fastProc κ cutoff) (fastP.length+5)
      (time fastTime κ cutoff) (TernaryHybridResources.need fastNeed κ cutoff) := by
  refine ⟨body fastP.length fastProc κ cutoff,
    main_lookup fastP fastProc κ cutoff, fun R lim d x μ free H hok => ?_⟩
  have hp := getElem?_append_of_eq_some (main_lookup fastP fastProc κ cutoff) R
  have hinput : Seg μ x.a (List.ofFn (ThreeSumApsp.Spec.vecOf x.N x.X)) := by
    intro i hi
    have hi' : i < x.N := by simpa only [List.length_ofFn] using hi
    simpa only [List.getElem_ofFn] using (OriginalThreeSum.task_read H) ⟨i,hi'⟩
  have hh := (program_meets_of_fast fastNeed fastTime
    (κ := κ) (cutoff := cutoff) (d := d) (ThreeSumApsp.Spec.vecOf x.N x.X) μ
    H.N_pos H.below hok hinput (OriginalThreeSum.task_bound H) hfast).append R
  obtain ⟨b,hb,he⟩ := hh.mono le_rfl (fun r ν ⟨hbool,hcorrect,hkept⟩ =>
    OriginalThreeSum.task_post (x := x) (μ := μ) (ν := ν) (fr := free)
      hbool hcorrect hkept)
  have heq : b=body fastP.length fastProc κ cutoff :=
    Option.some.inj (hb.symm.trans hp)
  subst b
  exact he

end ThreeSum.TernaryHybridCore
