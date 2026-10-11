import Submission.ThreeSum.ReportingHostTerminalOriginal
import Submission.ThreeSum.DenseGuardWanted
import Submission.ThreeSum.DenseGuardBands

/-!
# Exact completeness for the physically emitted wanted array

Every original zero has a raw witness whose wanted label occurs in the
actual join output. At every permitted partial depth its word has a
positive retained prefix, and the terminal tester includes its physical
pair. Conversely a terminal hit in any actual slot supplies an original
owner-domain zero. Equal wanted fibers also have equal ordered frontiers,
so the global guard and owner-local traversal use the same records.
-/

namespace ThreeSum.ReportingHostWantedComplete

open Finset GlobalEncoding RawIncidences RawReporting ReportingHostTerminalBatch
open LocalCoverBounds

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

section Fibers

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem prefixQuery_eq_of_domain {h J : ℕ} {I U : Finset (RawItem h J α β γ)}
    (w : Wanted h J α) (he : domain I w=domain U w) :
    prefixQuery I w=prefixQuery U w := by
  funext k pre
  simp only [prefixQuery,he]

theorem frontier_eq_of_domain {h J : ℕ} {I U : Finset (RawItem h J α β γ)}
    (w : Wanted h J α) (he : domain I w=domain U w) (k : ℕ) :
    ReportingHostFrontier.frontier I w k=ReportingHostFrontier.frontier U w k := by
  unfold ReportingHostFrontier.frontier
  rw [prefixQuery_eq_of_domain w he]

end Fibers

theorem frontier_global_eq_owner {h J nA nB nC g s k : ℕ} {P shift : ℤ}
    (rs : List BandCandidateRows.Record) (hs : s<rs.length)
    (a : Fin (BandRawA.items nA g rs).length→ℤ) (b : Fin nB→ℤ) (c : Fin nC→ℤ)
    (w : Wanted h J (Fin (BandRawA.items nA g rs).length))
    (ho : (BandRawA.labelAt nA g rs w.1.val).owner=s) :
    ReportingHostFrontier.frontier
      (rawOn h J P shift (BandRawA.finiteAllProducts nA nB nC g rs) a b c) w k=
    ReportingHostFrontier.frontier
      (rawOn h J P shift (BandRawA.finiteOwnerProduct nA nB nC g rs s) a b c) w k :=
  frontier_eq_of_domain w (DenseGuardBands.domain_global_eq_owner rs hs a b c w ho) k

section Emitted

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

theorem raw_emitted {μ : ℕ→ℤ} {free P h J : ℕ} {shift : ℤ} {xs : List ℤ}
    (H : LightWantedSetup.Output μ free (localPrime h^J) (LightGuardedWanted.left P xs)
      (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J) shift)
    {T : Finset (Original (Fin xs.length) β γ)} {b : β→ℤ} {c : γ→ℤ}
    {r : RawItem h J (Fin xs.length) β γ}
    (hr : r∈rawOn h J (P : ℤ) shift T (fun i => xs.getD i.val 0) b c) :
    ∃ slot : Fin (μ free).toNat, DenseGuardWanted.labelAt H slot=wantedOf r := by
  exact List.mem_ofFn.mp (DenseGuardWanted.labels_complete H (RawAKeyLists.raw_wanted_mem hr))

theorem original_zero_iff_emitted_terminal {μ : ℕ→ℤ} {free P h J k NL NR : ℕ}
    {shift : ℤ} {xs : List ℤ}
    (H : LightWantedSetup.Output μ free (localPrime h^J) (LightGuardedWanted.left P xs)
      (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J) shift)
    (A : Finset (Fin xs.length)) (B : Finset β) (C : Finset γ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (hh : 0<h) (hp : 0<P) (hk : k≤J) :
    (∃ t∈A ×ˢ (B ×ˢ C), difference (fun i => xs.getD i.val 0) b c t=0) ↔
      ∃ slot : Fin (μ free).toNat,
        let w := DenseGuardWanted.labelAt H slot
        w.1∈A ∧
        ∃ pre∈ReportingHostFrontier.frontier
          (rawOn h J (P : ℤ) shift (A ×ˢ (B ×ˢ C)) (fun i => xs.getD i.val 0) b c) w k,
          Hit (xs.getD w.1.val 0) P shift left right NL NR w.2.2 k pre := by
  constructor
  · rintro ⟨t,ht,hzero⟩
    obtain ⟨r,hr,hrt⟩ := raw_complete (h := h) (J := J) (P := (P : ℤ)) (d := shift)
      (a := fun i => xs.getD i.val 0) (b := b) (c := c) hh (by exact_mod_cast hp) ht
      (by rw [hzero]; exact dvd_zero _)
    obtain ⟨slot,hslot⟩ := raw_emitted H hr
    refine ⟨slot,?_⟩
    dsimp only
    rw [hslot]
    refine ⟨(Finset.mem_product.mp (mem_rawOn.mp hr).1).1,?_⟩
    exact ReportingHostTerminalOriginal.frontier_hit_of_raw P shift A B C
      (fun i => xs.getD i.val 0) b c left right eL eR hvL hvR (wantedOf r) hk r hr rfl
      (by simpa only [hrt] using hzero)
  · rintro ⟨slot,ha,pre,hpre,hhit⟩
    obtain ⟨t,ht,_,he⟩ := ReportingHostTerminalOriginal.hit_sound_original P shift A B C
      (fun i => xs.getD i.val 0) b c left right eL eR hvL hvR
      (DenseGuardWanted.labelAt H slot) pre ha hhit
    exact ⟨t,ht,he⟩

end Emitted

end ThreeSum.ReportingHostWantedComplete
