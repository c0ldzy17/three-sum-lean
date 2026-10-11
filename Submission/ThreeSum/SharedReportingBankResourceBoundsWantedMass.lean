import Submission.ThreeSum.SharedReportingBankResourceBoundsWantedGuardMass
import Submission.ThreeSum.ReportingHostWantedPrefix

/-! # Finite word bounds for every physical wanted mass

Each original triple has at most the established representation cap many
raw witnesses. The incidence coordinate is its physical position, so the
finite product bound retains every owner and every repeated value. The
injective physical wanted labels then bound every scan prefix by the same
global raw cardinality.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Finset Light RawIncidences RawReporting GlobalEncoding
open ReportingHostFrontierLayout ReportingHostWantedLayout
open BandRawA BandCandidateRows ReportingHostWantedOriginal

set_option maxHeartbeats 1900000
set_option maxRecDepth 15000

theorem wanted_finite_raw_card_le {h J N NB NC : ℕ} {P shift : ℤ}
    (T : Finset (Original (Fin N) (Fin NB) (Fin NC)))
    (a : Fin N→ℤ) (b : Fin NB→ℤ) (c : Fin NC→ℤ)
    (hP : 0<P) (hguard : 4*P≤globalModulus h J) :
    (rawOn h J P shift T a b c).card≤massBound N NB NC (representationCap h J) := by
  have hc : T.card≤N*NB*NC := by
    simpa only [Fintype.card_prod,Fintype.card_fin,Nat.mul_assoc] using Finset.card_le_univ T
  exact (raw_card_le T a b c hP hguard).trans (Nat.mul_le_mul_right _ hc)

theorem wanted_finite_raw_card_le_magnitude {n N NB NC : ℕ} {P shift : ℤ}
    (T : Finset (Original (Fin N) (Fin NB) (Fin NC)))
    (a : Fin N→ℤ) (b : Fin NB→ℤ) (c : Fin NC→ℤ)
    (hP : 0<P) (hguard : 4*P≤globalModulus (half n) (blocks n))
    (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    (rawOn (half n) (blocks n) P shift T a b c).card≤3*(magnitude n)^7 :=
  (wanted_finite_raw_card_le T a b c hP hguard).trans (wanted_mass_bound_le hN hB hC)

theorem wanted_global_card_le {n nA NB NC g P : ℕ} (rs : List Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ)
    (hP : 0<P) (hguard : 4*(P : ℤ)≤globalModulus (half n) (blocks n))
    (hN : (items nA g rs).length≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    (globalItems (half n) (blocks n) nA NB NC g P rs fA fB fC shift).card≤3*(magnitude n)^7 :=
  wanted_finite_raw_card_le_magnitude (finiteAllProducts nA NB NC g rs)
    (fun i => valueAt nA g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)
    (by exact_mod_cast hP) hguard hN hB hC

theorem wanted_local_card_le {n nA NB NC g P : ℕ} (rs : List Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) (w : Wanted (half n) (blocks n) (AType nA g rs))
    (hP : 0<P) (hguard : 4*(P : ℤ)≤globalModulus (half n) (blocks n))
    (hN : (items nA g rs).length≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    (localItems (half n) (blocks n) nA NB NC g P rs fA fB fC shift w).card≤3*(magnitude n)^7 :=
  wanted_finite_raw_card_le_magnitude (finiteOwnerProduct nA NB NC g rs (owner rs w))
    (fun i => valueAt nA g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)
    (by exact_mod_cast hP) hguard hN hB hC

theorem wanted_global_root_le {n nA NB NC g P : ℕ} (rs : List Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) (w : Wanted (half n) (blocks n) (AType nA g rs))
    (hP : 0<P) (hguard : 4*(P : ℤ)≤globalModulus (half n) (blocks n))
    (hN : (items nA g rs).length≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    rootMass (globalItems (half n) (blocks n) nA NB NC g P rs fA fB fC shift) w≤3*(magnitude n)^7 := by
  rw [rootMass_eq]
  exact (Finset.card_filter_le _ _).trans (wanted_global_card_le rs fA fB fC shift hP hguard hN hB hC)

theorem wanted_local_root_le {n nA NB NC g P : ℕ} (rs : List Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) (w : Wanted (half n) (blocks n) (AType nA g rs))
    (hP : 0<P) (hguard : 4*(P : ℤ)≤globalModulus (half n) (blocks n))
    (hN : (items nA g rs).length≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    rootMass (localItems (half n) (blocks n) nA NB NC g P rs fA fB fC shift w) w≤3*(magnitude n)^7 := by
  rw [rootMass_eq]
  exact (Finset.card_filter_le _ _).trans (wanted_local_card_le rs fA fB fC shift w hP hguard hN hB hC)

section Physical

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ} {n nA NB NC g free P : ℕ}
  {rs : List Record} {shift : ℤ}
  (H : LightWantedSetup.Output μ free (LocalCoverBounds.localPrime (half n)^blocks n)
    (LightGuardedWanted.left P (values fA (items nA g rs)))
    (LightGuardedWanted.right (half n) (blocks n)) (3*(values fA (items nA g rs)).length)
    (LightGuardedWanted.totalKeys (half n) (blocks n)) shift)

theorem wanted_physical_slot_mass_le (i : ℕ)
    (hP : 0<P) (hguard : 4*(P : ℤ)≤globalModulus (half n) (blocks n))
    (hN : (items nA g rs).length≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    ReportingHostWantedPrefix.slotMass H fB fC NB NC i≤3*(magnitude n)^7 := by
  unfold ReportingHostWantedPrefix.slotMass
  split
  · exact wanted_local_root_le rs fA fB fC shift _ hP hguard hN hB hC
  · exact Nat.zero_le _

theorem wanted_physical_prefix_mass_le (k : ℕ) (hk : k≤(μ free).toNat)
    (hP : 0<P) (hguard : 4*(P : ℤ)≤globalModulus (half n) (blocks n))
    (hN : (items nA g rs).length≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    SharedTraversalCosts.prefixMass (ReportingHostWantedPrefix.slotMass H fB fC NB NC) k≤3*(magnitude n)^7 :=
  (ReportingHostWantedPrefix.prefix_mass_le_card H fB fC NB NC k hk).trans
    (wanted_global_card_le rs fA fB fC shift hP hguard hN hB hC)

end Physical
end ThreeSum.SharedReportingBankResourceBounds
