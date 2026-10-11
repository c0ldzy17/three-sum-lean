import Submission.ThreeSum.LightReportingWantedScan

/-!
# Exact whole-scan YES and NO for the original physical domain

Every emitted slot has its own original owner bands. Prefix threshold
crossings are sound by distinct physical labels; if no crossing occurs,
the terminal tests cover every original zero through an actual emitted slot.
-/

namespace ThreeSum.ReportingHostWantedDecision

open Finset Light BandRawA BandCandidateRows RawIncidences RawReporting GlobalEncoding
open ReportingHostWantedPhysical ReportingHostWantedOriginal ReportingHostWantedPrefix
open LightReportingWantedScan SharedTraversalCosts

set_option maxHeartbeats 2100000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false

section Actual

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ} {n NB NC g free P h J : ℕ}
  {rs : List Record} {shift : ℤ}
  (H : LightWantedSetup.Output μ free (LocalCoverBounds.localPrime h^J)
    (LightGuardedWanted.left P (values fA (items n g rs))) (LightGuardedWanted.right h J)
    (3*(values fA (items n g rs)).length) (LightGuardedWanted.totalKeys h J) shift)

def slotHit (fB fC : ℕ→ℤ) (NB NC K i : ℕ) : Prop :=
  if hi : i<(μ free).toNat then
    Terminal h J n NB NC g P rs fA fB fC shift (wantedAt H ⟨i,hi⟩) K
  else False

theorem slotHit_at (fB fC : ℕ→ℤ) (NB NC K : ℕ) (i : Fin (μ free).toNat) :
    slotHit H fB fC NB NC K i.val ↔
      Terminal h J n NB NC g P rs fA fB fC shift (wantedAt H i) K := by
  simp only [slotHit,dif_pos i.isLt]

theorem hit_exists_iff (fB fC : ℕ→ℤ) (NB NC K : ℕ) :
    (∃ i<(μ free).toNat, slotHit H fB fC NB NC K i) ↔
      ∃ i : Fin (μ free).toNat, Terminal h J n NB NC g P rs fA fB fC shift (wantedAt H i) K := by
  constructor
  · rintro ⟨i,hi,hhit⟩
    exact ⟨⟨i,hi⟩,(slotHit_at H fB fC NB NC K ⟨i,hi⟩).mp hhit⟩
  · rintro ⟨i,hhit⟩
    exact ⟨i.val,i.isLt,(slotHit_at H fB fC NB NC K i).mpr hhit⟩

theorem accepted_iff_original (fB fC : ℕ→ℤ) (NB NC K F : ℕ) (aux : Finset ℤ)
    (hh : 0<h) (hK : K≤J) (hp : 0<P) (hg : 4*(P : ℤ)≤globalModulus h J)
    (hsep : ∀ t∈finiteAllProducts n NB NC g rs,
      difference (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t≠0 →
        ∃ l∈aux, ¬l∣difference (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t)
    (hF : Arithmetic.weightedFalseCount (finiteAllProducts n NB NC g rs)
      (difference (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)) aux (P : ℤ)≤F) :
    Accepted (slotMass H fB fC NB NC) (slotHit H fB fC NB NC K)
      (representationCap h J*F) (μ free).toNat ↔
      ∃ t∈finiteAllProducts n NB NC g rs,
        difference (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t=0 := by
  constructor
  · rintro (hdense | hterminal)
    · exact prefix_dense_yes H fB fC NB NC (μ free).toNat F aux le_rfl hp hg hsep hF hdense
    · exact (original_zero_iff_emitted_terminal H hh hp hK).mpr
        ((hit_exists_iff H fB fC NB NC K).mp hterminal)
  · intro hzero
    exact Or.inr ((hit_exists_iff H fB fC NB NC K).mpr
      ((original_zero_iff_emitted_terminal H hh hp hK).mp hzero))

theorem yes_no_of_scan (fB fC : ℕ→ℤ) (NB NC K F : ℕ) (aux : Finset ℤ)
    (hh : 0<h) (hK : K≤J) (hp : 0<P) (hg : 4*(P : ℤ)≤globalModulus h J)
    (hsep : ∀ t∈finiteAllProducts n NB NC g rs,
      difference (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t≠0 →
        ∃ l∈aux, ¬l∣difference (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t)
    (hF : Arithmetic.weightedFalseCount (finiteAllProducts n NB NC g rs)
      (difference (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)) aux (P : ℤ)≤F)
    {r : ℤ} (hbool : r=0 ∨ r=1)
    (hscan : r=1 ↔ Accepted (slotMass H fB fC NB NC) (slotHit H fB fC NB NC K)
      (representationCap h J*F) (μ free).toNat) :
    (r=1 ↔ ∃ t∈finiteAllProducts n NB NC g rs,
      difference (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t=0) ∧
    (r=0 ↔ ¬∃ t∈finiteAllProducts n NB NC g rs,
      difference (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t=0) := by
  have he := hscan.trans (accepted_iff_original H fB fC NB NC K F aux hh hK hp hg hsep hF)
  refine ⟨he,?_⟩
  rw [← he]
  rcases hbool with hr | hr <;> simp [hr]

end Actual

end ThreeSum.ReportingHostWantedDecision
