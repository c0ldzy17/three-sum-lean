import Submission.ThreeSum.ReportingHostWantedOriginal
import Submission.ThreeSum.SharedTraversalPrefixCosts

/-!
# The exact dense counter of the physical ascending wanted scan

The finite physical labels are injective even when input values repeat.
The sum of the queried owner masses in any prefix is consequently the
mass of a distinct-label prefix in the complete original domain.
-/

namespace ThreeSum.ReportingHostWantedPrefix

open Finset Light BandRawA BandCandidateRows RawIncidences RawReporting
open GlobalEncoding ReportingHostWantedPhysical ReportingHostWantedOriginal
open ReportingHostFrontierLayout SharedTraversalCosts

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false

section Actual

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ} {n NB NC g free P h J : ℕ}
  {rs : List Record} {shift : ℤ}
  (H : LightWantedSetup.Output μ free (LocalCoverBounds.localPrime h^J)
    (LightGuardedWanted.left P (values fA (items n g rs))) (LightGuardedWanted.right h J)
    (3*(values fA (items n g rs)).length) (LightGuardedWanted.totalKeys h J) shift)

def labels : List (Wanted h J (AType n g rs)) := List.ofFn (wantedAt H)

theorem labels_nodup : (labels H).Nodup :=
  List.nodup_ofFn_ofInjective (wantedAt_injective H)

theorem prefix_nodup (k : ℕ) : ((labels H).take k).Nodup := (labels_nodup H).take

theorem prefix_step (i : Fin (μ free).toNat) :
    (labels H).take (i.val+1)=(labels H).take i.val++[wantedAt H i] := by
  have hi : i.val<(labels H).length := by simpa only [labels,List.length_ofFn] using i.isLt
  rw [List.take_succ_eq_append_getElem hi]
  simp only [labels,List.getElem_ofFn]

def slotMass (fB fC : ℕ→ℤ) (NB NC i : ℕ) : ℕ :=
  if hi : i<(μ free).toNat then
    rootMass (localItems h J n NB NC g P rs fA fB fC shift (wantedAt H ⟨i,hi⟩))
      (wantedAt H ⟨i,hi⟩)
  else 0

theorem slotMass_at (fB fC : ℕ→ℤ) (NB NC : ℕ) (i : Fin (μ free).toNat) :
    slotMass H fB fC NB NC i.val=
      rootMass (globalItems h J n NB NC g P rs fA fB fC shift) (wantedAt H i) := by
  simp only [slotMass,dif_pos i.isLt]
  exact (global_local_mass rs fA fB fC shift (wantedAt H i)).symm

theorem prefix_mass_eq (fB fC : ℕ→ℤ) (NB NC k : ℕ) (hk : k≤(μ free).toNat) :
    prefixMass (slotMass H fB fC NB NC) k=
      DenseGuard.mass (globalItems h J n NB NC g P rs fA fB fC shift) ((labels H).take k) := by
  induction k with
  | zero => simp only [prefixMass_zero,List.take_zero,DenseGuard.mass_nil]
  | succ k ih =>
      let i : Fin (μ free).toNat := ⟨k,by omega⟩
      rw [prefixMass_succ,ih (by omega)]
      rw [show (labels H).take (k+1)=(labels H).take k++[wantedAt H i] from prefix_step H i]
      rw [DenseGuard.mass_append,show slotMass H fB fC NB NC k=
        rootMass (globalItems h J n NB NC g P rs fA fB fC shift) (wantedAt H i) from slotMass_at H fB fC NB NC i]

theorem prefix_mass_le_card (fB fC : ℕ→ℤ) (NB NC k : ℕ) (hk : k≤(μ free).toNat) :
    prefixMass (slotMass H fB fC NB NC) k≤
      (globalItems h J n NB NC g P rs fA fB fC shift).card := by
  rw [prefix_mass_eq H fB fC NB NC k hk]
  exact DenseGuard.mass_le_raw_card _ _ (prefix_nodup H k)

theorem prefix_dense_yes (fB fC : ℕ→ℤ) (NB NC k F : ℕ) (aux : Finset ℤ)
    (hk : k≤(μ free).toNat) (hp : 0<P) (hg : 4*(P : ℤ)≤globalModulus h J)
    (hsep : ∀ t∈finiteAllProducts n NB NC g rs,
      difference (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t≠0 →
        ∃ l∈aux, ¬l∣difference (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t)
    (hF : Arithmetic.weightedFalseCount (finiteAllProducts n NB NC g rs)
      (difference (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)) aux (P : ℤ)≤F)
    (hdense : representationCap h J*F<prefixMass (slotMass H fB fC NB NC) k) :
    ∃ t∈finiteAllProducts n NB NC g rs,
      difference (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t=0 := by
  rw [prefix_mass_eq H fB fC NB NC k hk] at hdense
  exact DenseGuard.partial_early_yes_of_upper (finiteAllProducts n NB NC g rs)
    (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)
    aux ((labels H).take k) (prefix_nodup H k) (by exact_mod_cast hp) hg hsep hF hdense

end Actual

end ThreeSum.ReportingHostWantedPrefix
