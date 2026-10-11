import Submission.ThreeSum.DenseGuard
import Submission.ThreeSum.BandRawAFinite

/-!
# Owner queries are the exact fibers of the global physical domain

The A incidence fixes its owner. Restricting to that owner's B/C bands
therefore leaves the entire wanted fiber unchanged. The mass read by the
owner-local query is exactly the mass charged by the global dense guard.
-/

namespace ThreeSum.DenseGuardBands

open Finset GlobalEncoding RawIncidences RawReporting ReportingHostFrontierLayout

section General

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem domain_eq_of_first_fiber {h J : ℕ} {P shift : ℤ}
    (T U : Finset (Original α β γ)) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (w : Wanted h J α)
    (hf : ∀ t : Original α β γ, t.1=w.1 → (t ∈ T ↔ t ∈ U)) :
    domain (rawOn h J P shift T a b c) w=domain (rawOn h J P shift U a b c) w := by
  ext r
  simp only [domain,mem_filter,mem_rawOn]
  constructor
  · rintro ⟨⟨ht,hr⟩,he⟩
    have ha : r.1.1=w.1 := congrArg (fun z : Wanted h J α => z.1) he
    exact ⟨⟨(hf r.1 ha).mp ht,hr⟩,he⟩
  · rintro ⟨⟨hu,hr⟩,he⟩
    have ha : r.1.1=w.1 := congrArg (fun z : Wanted h J α => z.1) he
    exact ⟨⟨(hf r.1 ha).mpr hu,hr⟩,he⟩

end General

open BandRawA

theorem finite_owner_fiber {nA nB nC g s : ℕ} {rs : List BandCandidateRows.Record}
    (hs : s < rs.length) (i : Fin (items nA g rs).length)
    (hi : (BandRawA.labelAt nA g rs i.val).owner=s)
    (t : Fin (items nA g rs).length × Fin nB × Fin nC) (ht : t.1=i) :
    t ∈ finiteAllProducts nA nB nC g rs ↔ t ∈ finiteOwnerProduct nA nB nC g rs s := by
  have ho : (BandRawA.labelAt nA g rs t.1.val).owner=s := by rw [ht]; exact hi
  simp only [mem_finiteAllProducts,mem_finiteOwnerProduct,mem_allProducts,mem_ownerProduct hs,
    coordinates,ownerRecord,ho,true_and]

theorem domain_global_eq_owner {h J nA nB nC g s : ℕ} {P shift : ℤ}
    (rs : List BandCandidateRows.Record) (hs : s < rs.length)
    (a : Fin (items nA g rs).length→ℤ) (b : Fin nB→ℤ) (c : Fin nC→ℤ)
    (w : Wanted h J (Fin (items nA g rs).length))
    (ho : (BandRawA.labelAt nA g rs w.1.val).owner=s) :
    domain (rawOn h J P shift (finiteAllProducts nA nB nC g rs) a b c) w=
      domain (rawOn h J P shift (finiteOwnerProduct nA nB nC g rs s) a b c) w :=
  domain_eq_of_first_fiber _ _ a b c w (finite_owner_fiber hs w.1 ho)

theorem prefixQuery_global_eq_owner {h J nA nB nC g s k : ℕ} {P shift : ℤ}
    (rs : List BandCandidateRows.Record) (hs : s < rs.length)
    (a : Fin (items nA g rs).length→ℤ) (b : Fin nB→ℤ) (c : Fin nC→ℤ)
    (w : Wanted h J (Fin (items nA g rs).length))
    (ho : (BandRawA.labelAt nA g rs w.1.val).owner=s)
    (pre : List (Finset (Fin (512*h)))) :
    prefixQuery (rawOn h J P shift (finiteAllProducts nA nB nC g rs) a b c) w k pre=
      prefixQuery (rawOn h J P shift (finiteOwnerProduct nA nB nC g rs s) a b c) w k pre := by
  simp only [prefixQuery,domain_global_eq_owner rs hs a b c w ho]

theorem rootMass_global_eq_owner {h J nA nB nC g s : ℕ} {P shift : ℤ}
    (rs : List BandCandidateRows.Record) (hs : s < rs.length)
    (a : Fin (items nA g rs).length→ℤ) (b : Fin nB→ℤ) (c : Fin nC→ℤ)
    (w : Wanted h J (Fin (items nA g rs).length))
    (ho : (BandRawA.labelAt nA g rs w.1.val).owner=s) :
    rootMass (rawOn h J P shift (finiteAllProducts nA nB nC g rs) a b c) w=
      rootMass (rawOn h J P shift (finiteOwnerProduct nA nB nC g rs s) a b c) w :=
  prefixQuery_global_eq_owner rs hs a b c w ho []

end ThreeSum.DenseGuardBands
