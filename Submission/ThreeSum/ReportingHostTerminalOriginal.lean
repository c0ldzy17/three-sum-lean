import Submission.ThreeSum.ReportingHostTerminalBatch

/-!
# Original raw witnesses reach the actually tested terminal prefixes

Every true raw incidence has a stored positive prefix at any chosen partial
depth, and its retained completion appears in the actual terminal batch.
Conversely, every positive terminal result supplies an original finite
owner-domain triple whose integer values satisfy the exact equation.
-/

namespace ThreeSum.ReportingHostTerminalOriginal

open Finset BlockRows BlockEncoding GlobalEncoding RawIncidences RawReporting RawPrefixCounts
open StoredReporting
open ReportingHostTerminalBatch

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem hit_of_raw {h J k NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k≤J) (hp : ValidPrefix w.2.2 k pre)
    (r : RawItem h J α β γ) (hr : r∈rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c)
    (hw : wantedOf r=w) (hpre : (word r).take k=pre) (hzero : difference a b c r.1=0) :
    Hit (a w.1) p shift left right NL NR w.2.2 k pre := by
  have hq : tupleOutput r.2.1=w.2.2 := congrArg (fun w => w.2.2) hw
  have ha : r.1.1=w.1 := congrArg Prod.fst hw
  have hraw := mem_rawOn.mp hr
  have hrep := (mem_witnesses.mp hraw.2).1
  have hpair := (tuple_mem_representations r.2.1 (b r.1.2.1%(p : ℤ))
    (c r.1.2.2%(p : ℤ)+shift)).mp hrep
  have hcompletion : r.2.1∈completions w.2.2 k pre :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq,hpre⟩
  have hcompatible : r.1.2∈compatiblePairs (p : ℤ) shift B C b c r.2.1 :=
    Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hraw.1).2,hpair⟩
  exact hit_of_compatible p shift (a w.1) B C b c left right eL eR hvL hvR w.2.2 pre hk hp
    r.2.1 hcompletion r.1.2 hcompatible (by simpa only [difference,ha] using hzero)

theorem hit_sound_original {h J k NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (ha : w.1∈A)
    (H : Hit (a w.1) p shift left right NL NR w.2.2 k pre) :
    ∃ t∈A ×ˢ (B ×ˢ C), t.1=w.1 ∧ difference a b c t=0 := by
  obtain ⟨i,hi,j,hj,he⟩ := hit_sound H
  let u := eL ⟨i,hi⟩
  let v := eR ⟨j,hj⟩
  refine ⟨(w.1,u.val,v.val),Finset.mem_product.mpr ⟨ha,Finset.mem_product.mpr ⟨u.property,v.property⟩⟩,rfl,?_⟩
  change c v.val-b u.val-a w.1=0
  rw [← hvL ⟨i,hi⟩,← hvR ⟨j,hj⟩]
  exact he

theorem frontier_hit_of_raw {h J k NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (w : Wanted h J α) (hk : k≤J) (r : RawItem h J α β γ)
    (hr : r∈rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c)
    (hw : wantedOf r=w) (hzero : difference a b c r.1=0) :
    ∃ pre∈ReportingHostFrontier.frontier (rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w k,
      Hit (a w.1) p shift left right NL NR w.2.2 k pre := by
  let I := rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
  have hfront : (word r).take k∈ReportingHostFrontier.frontier I w k :=
    (ReportingHostFrontier.mem_frontier_iff I w hk _).mpr ⟨r,hr,hw,rfl⟩
  refine ⟨(word r).take k,hfront,?_⟩
  exact hit_of_raw p shift A B C a b c left right eL eR hvL hvR w _ hk
    (ReportingHostPositive.frontier_valid I w hk hfront) r hr hw rfl hzero

theorem original_zero_iff_reported {h J k NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (hh : 0<h) (hp : 0<p) (hk : k≤J) :
    (∃ t∈A ×ˢ (B ×ˢ C), difference a b c t=0) ↔
      ∃ w : Wanted h J α, w.1∈A ∧
        ∃ pre∈ReportingHostFrontier.frontier (rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w k,
          Hit (a w.1) p shift left right NL NR w.2.2 k pre := by
  constructor
  · rintro ⟨t,ht,hzero⟩
    obtain ⟨r,hr,hrt⟩ := raw_complete (h := h) (J := J) (P := (p : ℤ)) (d := shift)
      (a := a) (b := b) (c := c) hh (by exact_mod_cast hp) ht (by rw [hzero]; exact dvd_zero _)
    have ha : (wantedOf r).1∈A := (Finset.mem_product.mp (mem_rawOn.mp hr).1).1
    refine ⟨wantedOf r,ha,?_⟩
    exact frontier_hit_of_raw p shift A B C a b c left right eL eR hvL hvR (wantedOf r) hk r hr rfl
      (by simpa only [hrt] using hzero)
  · rintro ⟨w,ha,pre,hpre,hhit⟩
    obtain ⟨t,ht,_,he⟩ := hit_sound_original p shift A B C a b c left right eL eR hvL hvR w pre ha hhit
    exact ⟨t,ht,he⟩

end ThreeSum.ReportingHostTerminalOriginal
