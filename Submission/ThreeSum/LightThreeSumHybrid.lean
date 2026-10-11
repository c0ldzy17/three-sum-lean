import Submission.ThreeSum.LightThreeSumHybridCore
import Submission.ThreeSum.LightThreeSumConcreteFast

/-!
# The complete543-procedure original-input solver

For each fixed magnitude exponent, the cutoff is chosen from the proved
uniform parameter conditions. The program tests that cutoff, computes the
integer power, and uses the exact original-triple fallback whenever needed.
Every branch returns the original distinct-position decision and preserves
all memory before the supplied free address.
-/

namespace ThreeSum.LightThreeSumHybrid

open Light ThreeSumApsp.Spec

set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

noncomputable section

def program (κ : ℕ) : Program :=
  LightThreeSumHybridCore.program LightThreeSumConcreteFast.program κ
    (ThreeSumWantedHostConditions.cutoff κ)

def need (κ : ℕ) : ℕ→ℕ→Need :=
  ThreeSumFastResourcesHybrid.need κ (ThreeSumWantedHostConditions.cutoff κ)

def time (κ : ℕ) : ℕ→ℕ→ℕ :=
  ThreeSumHybridCosts.time κ (ThreeSumWantedHostConditions.cutoff κ)

theorem program_length (κ : ℕ) : (program κ).length=543 :=
  LightThreeSumHybridCore.program_length LightThreeSumConcreteFast.program_length κ
    (ThreeSumWantedHostConditions.cutoff κ)

theorem main_lookup (κ : ℕ) :
    (program κ)[542]?=some
      (LightThreeSumHybridCore.body κ (ThreeSumWantedHostConditions.cutoff κ)) :=
  LightThreeSumHybridCore.main_lookup LightThreeSumConcreteFast.program_length κ
    (ThreeSumWantedHostConditions.cutoff κ)

/-- No execution or correctness callback remains: the successful guards
    supply the proved conditions of the actual concrete fast driver. -/
theorem program_meets {lim : Limits} {κ src n U free d : ℕ}
    (x : Fin n→ℤ) (μ : ℕ→ℤ) (hn : 0<n)
    (H : (need κ n U).Ok lim free d)
    (hsrc : src+n≤free) (hinput : Seg μ src (List.ofFn x))
    (hx : ∀ i, |x i|≤(U : ℤ)) :
    Meets lim (program κ) 542 d [n,U,src,free] μ (time κ n U)
      (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ν free) := by
  have hread : ∀ i : Fin n, μ (src+i.val)=x i := by
    intro i
    have hi : i.val<(List.ofFn x).length := by simpa only [List.length_ofFn] using i.isLt
    have hh : μ (src+i.val)=(List.ofFn x)[i.val] := hinput i.val hi
    simpa only [List.getElem_ofFn] using hh
  refine LightThreeSumHybridCore.program_meets LightThreeSumConcreteFast.program_length
    x μ hn hsrc H hread hx ?_
  intro hcutoff hU
  apply LightThreeSumConcreteFast.program_meets x μ
    (ThreeSumWantedHostConditions.ready_of_cutoff_le hcutoff)
    (ThreeSumFastResourcesHybrid.fast_of_ok H) hsrc hinput
  intro i
  exact (hx i).trans (Int.ofNat_le.mpr hU)

theorem poly_need (κ : ℕ) : PolyNeed (need κ) :=
  ThreeSumFastResourcesHybrid.poly_need κ (ThreeSumWantedHostConditions.cutoff κ)

/-- The complete executable solves the original task in every appended
    program, with the exact frozen hybrid time and affine resource need. -/
theorem solves (κ : ℕ) : Solves s3Task (program κ) 542 (time κ) (need κ) := by
  refine ⟨LightThreeSumHybridCore.body κ (ThreeSumWantedHostConditions.cutoff κ),
    main_lookup κ,fun R lim d x μ free H hok => ?_⟩
  have hp := getElem?_append_of_eq_some (main_lookup κ) R
  have hinput : Seg μ x.a (List.ofFn (vecOf x.N x.X)) := by
    intro i hi
    have hi' : i<x.N := by simpa only [List.length_ofFn] using hi
    simpa only [List.getElem_ofFn] using (OriginalThreeSum.task_read H) ⟨i,hi'⟩
  have hh := (program_meets (κ := κ) (d := d) (vecOf x.N x.X) μ H.N_pos hok
    H.below hinput (OriginalThreeSum.task_bound H)).append R
  obtain ⟨b,hb,he⟩ := hh.mono le_rfl (fun r ν ⟨hbool,hcorrect,hkept⟩ =>
    OriginalThreeSum.task_post (x := x) (μ := μ) (ν := ν) (fr := free)
      hbool hcorrect hkept)
  have heq : b=LightThreeSumHybridCore.body κ (ThreeSumWantedHostConditions.cutoff κ) :=
    Option.some.inj (hb.symm.trans hp)
  subst b
  exact he

end
end ThreeSum.LightThreeSumHybrid
