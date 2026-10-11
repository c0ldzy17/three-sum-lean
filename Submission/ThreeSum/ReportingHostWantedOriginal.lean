import Submission.ThreeSum.ReportingHostWantedPhysical
import Submission.ThreeSum.ReportingHostWantedComplete
import Submission.ThreeSum.BandRawAFiniteSlices

/-!
# Actual emitted slots decide the complete physical owner domain

Each slot selects its own independently retained B/C bands. Its terminal
semantics is the exact finite owner fiber, while the cumulative guard uses
their disjoint global union. This connects the physical wanted array to
original-value terminal tests at every permitted partial reporting depth.
-/

namespace ThreeSum.ReportingHostWantedOriginal

open Finset Light BandRawA BandCandidateRows RawIncidences RawReporting
open GlobalEncoding ReportingHostWantedPhysical
open ReportingHostFrontierLayout

set_option maxHeartbeats 2300000
set_option maxRecDepth 12000

abbrev AType (n g : ℕ) (rs : List Record) := Fin (items n g rs).length

def owner {h J n g : ℕ} (rs : List Record) (w : Wanted h J (AType n g rs)) : ℕ :=
  (BandRawA.labelAt n g rs w.1.val).owner

def left {h J n g : ℕ} (rs : List Record) (fB : ℕ→ℤ)
    (w : Wanted h J (AType n g rs)) (j : ℕ) : ℤ :=
  fB (BandPartition.start g (ownerRecord n g rs w.1.val).b+j)

def right {h J n g : ℕ} (rs : List Record) (fC : ℕ→ℤ)
    (w : Wanted h J (AType n g rs)) (j : ℕ) : ℤ :=
  fC (BandPartition.start g (ownerRecord n g rs w.1.val).c+j)

def leftCount {h J n g : ℕ} (rs : List Record) (NB : ℕ)
    (w : Wanted h J (AType n g rs)) : ℕ := bandLength NB g (ownerRecord n g rs w.1.val).b

def rightCount {h J n g : ℕ} (rs : List Record) (NC : ℕ)
    (w : Wanted h J (AType n g rs)) : ℕ := bandLength NC g (ownerRecord n g rs w.1.val).c

def globalItems (h J n NB NC g p : ℕ) (rs : List Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) : Finset (RawItem h J (AType n g rs) (Fin NB) (Fin NC)) :=
  rawOn h J (p : ℤ) shift (finiteAllProducts n NB NC g rs)
    (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)

def localItems (h J n NB NC g p : ℕ) (rs : List Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) (w : Wanted h J (AType n g rs)) :
    Finset (RawItem h J (AType n g rs) (Fin NB) (Fin NC)) :=
  rawOn h J (p : ℤ) shift (finiteOwnerProduct n NB NC g rs (owner rs w))
    (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)

def Terminal (h J n NB NC g p : ℕ) (rs : List Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) (w : Wanted h J (AType n g rs)) (k : ℕ) : Prop :=
  ∃ pre∈ReportingHostFrontier.frontier (localItems h J n NB NC g p rs fA fB fC shift w) w k,
    ReportingHostTerminalBatch.Hit (valueAt n g rs fA w.1.val) p shift
      (left rs fB w) (right rs fC w) (leftCount rs NB w) (rightCount rs NC w) w.2.2 k pre

theorem owner_lt {h J n g : ℕ} (rs : List Record) (w : Wanted h J (AType n g rs)) :
    owner rs w<rs.length := (at_bounds w.1.isLt).1

theorem mem_owner {h J n g : ℕ} (rs : List Record) (w : Wanted h J (AType n g rs)) :
    w.1∈finiteAIndices n g rs (owner rs w) :=
  (finiteAIndices_owner (owner_lt rs w)).mpr rfl

theorem global_local_domain {h J n NB NC g p : ℕ} (rs : List Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) (w : Wanted h J (AType n g rs)) :
    domain (globalItems h J n NB NC g p rs fA fB fC shift) w=
      domain (localItems h J n NB NC g p rs fA fB fC shift w) w :=
  DenseGuardBands.domain_global_eq_owner rs (owner_lt rs w) _ _ _ w rfl

theorem global_local_mass {h J n NB NC g p : ℕ} (rs : List Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) (w : Wanted h J (AType n g rs)) :
    rootMass (globalItems h J n NB NC g p rs fA fB fC shift) w=
      rootMass (localItems h J n NB NC g p rs fA fB fC shift w) w :=
  DenseGuardBands.rootMass_global_eq_owner rs (owner_lt rs w) _ _ _ w rfl

theorem global_local_frontier {h J n NB NC g p : ℕ} (rs : List Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) (w : Wanted h J (AType n g rs)) (k : ℕ) :
    ReportingHostFrontier.frontier (globalItems h J n NB NC g p rs fA fB fC shift) w k=
      ReportingHostFrontier.frontier (localItems h J n NB NC g p rs fA fB fC shift w) w k :=
  ReportingHostWantedComplete.frontier_eq_of_domain w (global_local_domain rs fA fB fC shift w) k

theorem terminal_sound {h J n NB NC g p k : ℕ} (rs : List Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) (w : Wanted h J (AType n g rs))
    (H : Terminal h J n NB NC g p rs fA fB fC shift w k) :
    ∃ t∈finiteAllProducts n NB NC g rs,
      difference (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t=0 := by
  obtain ⟨pre,_,hhit⟩ := H
  obtain ⟨t,ht,ha,hzero⟩ := ReportingHostTerminalOriginal.hit_sound_original p shift
    (finiteAIndices n g rs (owner rs w))
    (finiteBandPositions NB g (ownerRecord n g rs w.1.val).b)
    (finiteBandPositions NC g (ownerRecord n g rs w.1.val).c)
    (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)
    (left rs fB w) (right rs fC w)
    (finiteBandEquiv NB g (ownerRecord n g rs w.1.val).b)
    (finiteBandEquiv NC g (ownerRecord n g rs w.1.val).c)
    (fun _ => rfl) (fun _ => rfl) w pre (mem_owner rs w) hhit
  have hlocal : t∈finiteOwnerProduct n NB NC g rs (owner rs w) := ht
  exact ⟨t,(DenseGuardBands.finite_owner_fiber (owner_lt rs w) w.1 rfl t ha).mpr hlocal,hzero⟩

theorem terminal_of_raw {h J n NB NC g p k : ℕ} (rs : List Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) (w : Wanted h J (AType n g rs)) (hk : k≤J)
    (r : RawItem h J (AType n g rs) (Fin NB) (Fin NC))
    (hr : r∈globalItems h J n NB NC g p rs fA fB fC shift) (hw : wantedOf r=w)
    (hzero : difference (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) r.1=0) :
    Terminal h J n NB NC g p rs fA fB fC shift w k := by
  have ha : r.1.1=w.1 := congrArg Prod.fst hw
  have hglobal := mem_rawOn.mp hr
  have hlocal : r.1∈finiteOwnerProduct n NB NC g rs (owner rs w) :=
    (DenseGuardBands.finite_owner_fiber (owner_lt rs w) w.1 rfl r.1 ha).mp hglobal.1
  have hraw : r∈localItems h J n NB NC g p rs fA fB fC shift w := mem_rawOn.mpr ⟨hlocal,hglobal.2⟩
  exact ReportingHostTerminalOriginal.frontier_hit_of_raw p shift
    (finiteAIndices n g rs (owner rs w))
    (finiteBandPositions NB g (ownerRecord n g rs w.1.val).b)
    (finiteBandPositions NC g (ownerRecord n g rs w.1.val).c)
    (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)
    (left rs fB w) (right rs fC w)
    (finiteBandEquiv NB g (ownerRecord n g rs w.1.val).b)
    (finiteBandEquiv NC g (ownerRecord n g rs w.1.val).c)
    (fun _ => rfl) (fun _ => rfl) w hk r hraw hw hzero

section Actual

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ} {n NB NC g free P h J : ℕ}
  {rs : List Record} {shift : ℤ}
  (H : LightWantedSetup.Output μ free (LocalCoverBounds.localPrime h^J)
    (LightGuardedWanted.left P (values fA (items n g rs))) (LightGuardedWanted.right h J)
    (3*(values fA (items n g rs)).length) (LightGuardedWanted.totalKeys h J) shift)

theorem raw_emitted {r : RawItem h J (AType n g rs) (Fin NB) (Fin NC)}
    (hr : r∈globalItems h J n NB NC g P rs fA fB fC shift) :
    ∃ slot : Fin (μ free).toNat, wantedAt H slot=wantedOf r := by
  apply wantedAt_complete H
  have hh := (mem_witnesses.mp (mem_rawOn.mp hr).2).2
  simpa only [globalModulus,Nat.cast_pow,wantedOf,tupleKey] using hh

theorem original_zero_iff_emitted_terminal {k : ℕ}
    (hh : 0<h) (hp : 0<P) (hk : k≤J) :
    (∃ t∈finiteAllProducts n NB NC g rs,
      difference (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t=0) ↔
      ∃ slot : Fin (μ free).toNat, Terminal h J n NB NC g P rs fA fB fC shift (wantedAt H slot) k := by
  constructor
  · rintro ⟨t,ht,hzero⟩
    obtain ⟨r,hr,hrt⟩ := raw_complete (h := h) (J := J) (P := (P : ℤ)) (d := shift)
      (a := fun i => valueAt n g rs fA i.val) (b := fun j => fB j.val) (c := fun j => fC j.val)
      hh (by exact_mod_cast hp) ht (by rw [hzero]; exact dvd_zero _)
    obtain ⟨slot,hslot⟩ := raw_emitted H hr
    exact ⟨slot,terminal_of_raw rs fA fB fC shift (wantedAt H slot) hk r hr hslot.symm
      (by simpa only [hrt] using hzero)⟩
  · rintro ⟨slot,hterminal⟩
    exact terminal_sound rs fA fB fC shift (wantedAt H slot) hterminal

end Actual

end ThreeSum.ReportingHostWantedOriginal
