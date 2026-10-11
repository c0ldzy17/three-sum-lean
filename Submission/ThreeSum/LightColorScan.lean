import Submission.ThreeSum.ColorScan
import Submission.ThreeSum.LightColorParametersCosts

/-!
# Execute the finite coloring search

The recursive driver reuses one six-cell parameter row and all subsequent
per-color scratch. Once a color accepts, later color calls are skipped.
This is a compositional execution theorem: the concrete selected-color
decision procedure must supply the explicit per-color call contract below.
It does not assert existence of that still-being-integrated solver.
-/

namespace ThreeSum.LightColorScan

open Light ColorParameters ColorScan

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

/-- Source, length, persistent parameter header, reusable row, width, prefix length. -/
def body (pSelf pParameters pColor : ℕ) : Stmt :=
  .ite (k 0 <' v 5)
    (.call pSelf [v 0,v 1,v 2,v 3,v 4,v 5 -' k 1] 6 ;;
      .ite (k 0 <' v 6)
        (.set 0 (k 1))
        (.set 7 (v 5 -' k 1) ;;
          .call pParameters [v 4,v 7,v 3] 8 ;;
          .call pColor [v 0,v 1,v 2,v 3,v 3 +' k 6] 9 ;;
          .set 0 (v 9)))
    (.set 0 (k 0))

def time (colorTime W t : ℕ) : ℕ :=
  t*(100*count W+colorTime+3000)+100

structure Procs (P : Program) (pMain : ℕ) where
  pParameters : ℕ
  pDivide : ℕ
  pColor : ℕ
  main : P[pMain]?=some (body pMain pParameters pColor)
  parameters : P[pParameters]?=some (LightColorParameters.body pDivide)
  divide : P[pDivide]?=some LightSmallDivide.body

variable {lim : Limits} {P : Program}

theorem Procs.meets {pMain src n params free W colorTime colorDepth : ℕ}
    (R : Procs P pMain) (x : Fin n → ℤ) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : free+6 ≤ lim.space) (hsrc : src ≤ free) (hparams : params ≤ free)
    (hword : ((n+count W+W+100 : ℕ) : ℤ) ≤ lim.word)
    (hcolor : ∀ (i : ℕ) (hi : i < count W) (ν : ℕ → ℤ),
      Kept μ ν free → Seg ν free (fields (parameter hi)) →
      ∀ dd : ℕ, dd+colorDepth ≤ lim.depth →
      Meets lim P R.pColor dd [src,n,params,free,free+6] ν colorTime
        (fun r ξ => (r=0 ∨ r=1) ∧
          (r=1 ↔ ColorClassLists.witness (parameter hi) x) ∧ Kept ν ξ free))
    {t d : ℕ} {ν : ℕ → ℤ} (ht : t ≤ count W)
    (hd : d+t+colorDepth+3 ≤ lim.depth) (hkeep : Kept μ ν free) :
    Meets lim P pMain d [src,n,params,free,W,t] ν (time colorTime W t)
      (fun r ξ => (r=0 ∨ r=1) ∧ (r=1 ↔ Hit x W t) ∧ Kept ν ξ free) := by
  have hsmall (a : ℕ) (ha : a ≤ n+count W+W+100) : (a : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ha).trans hword
  have htwo := hsmall 2 (by omega)
  have hW := hsmall W (by omega)
  have hcount := hsmall (count W) (by omega)
  have hn := hsmall n (by omega)
  induction t generalizing d ν with
  | zero =>
      apply Meets.of_body R.main
      unfold body time
      light_if hbad hno : (0 : ℤ)<0
      · omega
      · light_set (0 : ℕ)
        exact ⟨by simp,by simp [hit_zero],SameOn.refl⟩
  | succ t ih =>
      have ht' : t < count W := by omega
      apply Meets.of_body R.main
      unfold body time
      light_if hyes hbad : (0 : ℤ)<((t+1 : ℕ) : ℤ)
      · have hrec := ih (d := d+1) (ν := ν) (by omega) (by omega) hkeep
        light_call hrec using time with prev ν₁ ⟨hprevBool,hprev,hkeep₁⟩
        have hprevRange : 0 ≤ prev ∧ prev ≤ 1 := by rcases hprevBool with hh | hh <;> omega
        light_if hhit hmiss : (0 : ℤ)<prev using time
        · have hh := hit_mono (by omega : t ≤ t+1) (hprev.mp (by omega))
          light_set (1 : ℕ) using time
          exact ⟨by simp,by simpa using hh,hkeep₁⟩
        · have hnoHit : ¬ Hit x W t := fun hh => hmiss (by have := hprev.mpr hh; omega)
          light_set (t : ℕ) using time
          have hp := LightColorParameters.meets (d := d+1) (W := W) (t := t) (free := free)
            (μ := ν₁) R.parameters R.divide hw hspace (hsmall _ (by omega)) (by omega)
          light_call hp using time,LightColorParameters.time with row ν₂ ⟨hrow,hdata,hkeep₂⟩
          have hrowData : Seg ν₂ free (fields (parameter ht')) := by
            simpa only [fields_parameter] using hdata
          have hkeepBefore : Kept ν₁ ν₂ free := fun i hi => hkeep₂ i (Or.inl hi)
          have htotal : Kept μ ν₂ free := fun i hi =>
            (hkeepBefore i hi).trans ((hkeep₁ i hi).trans (hkeep i hi))
          have hc := hcolor t ht' ν₂ htotal hrowData (d+1) (by omega)
          light_call hc using time,LightColorParameters.time with result ξ ⟨hbool,hresult,hkeep₃⟩
          have hrange : 0 ≤ result ∧ result ≤ 1 := by rcases hbool with hh | hh <;> omega
          light_set result using time,LightColorParameters.time
          refine ⟨hbool,?_,?_⟩
          · rw [hit_succ x ht',or_iff_right hnoHit]
            exact hresult
          · intro i hi
            exact (hkeep₃ i hi).trans ((hkeepBefore i hi).trans (hkeep₁ i hi))
      · omega

end ThreeSum.LightColorScan
