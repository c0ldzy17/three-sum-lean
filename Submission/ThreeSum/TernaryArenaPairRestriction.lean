import Submission.ThreeSum.TernaryArenaSourceSetup
import Submission.ThreeSum.TernaryNativeTensorScore

noncomputable section
namespace ThreeSum.TernaryArenaPairRestriction
open Finset TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps TernaryArenaSourceSetup
open TernaryNativePairMoments TernaryNativeTensorScore
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
variable {p m F r : ℕ} [Fact p.Prime]

def restrict (I : Input) (nB nC : ℕ) (fB fC : ℕ→ℕ) : Input :=
  {I with nB:=nB,nC:=nC,leftInput:=fun i => I.leftInput (fB i),rightInput:=fun i => I.rightInput (fC i)}

variable (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (nB nC : ℕ) (fB fC : ℕ→ℕ)
    (hB : ∀ i<nB, fB i<I.nB) (hC : ∀ i<nC, fC i<I.nC)

abbrev full := setup (r := r) maps τ cap Q I
abbrev small := setup (r := r) maps τ cap Q (restrict I nB nC fB fC)

include hB hC

private theorem source_mem (right : Bool) (a : ℕ×ℕ)
    (ha : a∈(source (r := r) maps cap (restrict I nB nC fB fC) right).records) :
    ((if right then fC a.1 else fB a.1),a.2)∈(source (r := r) maps cap I right).records := by
  have hv := (TernarySourceHostModel.mem_records _ _ _ _ _ _).mp ha
  apply (TernarySourceHostModel.mem_records _ _ _ _ _ _).mpr
  cases right
  · refine ⟨hB a.1 hv.1,hv.2.1,hv.2.2⟩
  · refine ⟨hC a.1 hv.1,hv.2.1,hv.2.2⟩

def embed {i : ℕ} (x : Pair (small (r := r) maps τ cap Q I nB nC fB fC) i) :
    Pair (full (r := r) maps τ cap Q I) i :=
  ⟨((fB x.val.1.1,x.val.1.2),(fC x.val.2.1,x.val.2.2)),by
    have hx := mem_filter.mp x.property
    have hl := mem_filter.mp (mem_product.mp hx.1).1
    have hr := mem_filter.mp (mem_product.mp hx.1).2
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_filter.mpr ⟨source_mem maps cap I nB nC fB fC hB hC false _ hl.1,hl.2⟩,
      mem_filter.mpr ⟨source_mem maps cap I nB nC fB fC hB hC true _ hr.1,hr.2⟩⟩,hx.2⟩⟩

theorem embed_injective
    (hfB : ∀ a<nB, ∀ b<nB, fB a=fB b→a=b)
    (hfC : ∀ a<nC, ∀ b<nC, fC a=fC b→a=b) (i : ℕ) :
    Function.Injective (embed (r := r) maps τ cap Q I nB nC fB fC hB hC (i := i)) := by
  intro x y he
  apply Subtype.ext
  have hxy := congrArg Subtype.val he
  change ((fB x.val.1.1,x.val.1.2),(fC x.val.2.1,x.val.2.2))=
    ((fB y.val.1.1,y.val.1.2),(fC y.val.2.1,y.val.2.2)) at hxy
  have xL := ((TernarySourceHostModel.mem_records _ _ _ _ _ _).mp
    (mem_filter.mp (mem_product.mp (mem_filter.mp x.property).1).1).1).1
  have yL := ((TernarySourceHostModel.mem_records _ _ _ _ _ _).mp
    (mem_filter.mp (mem_product.mp (mem_filter.mp y.property).1).1).1).1
  have xR := ((TernarySourceHostModel.mem_records _ _ _ _ _ _).mp
    (mem_filter.mp (mem_product.mp (mem_filter.mp x.property).1).2).1).1
  have yR := ((TernarySourceHostModel.mem_records _ _ _ _ _ _).mp
    (mem_filter.mp (mem_product.mp (mem_filter.mp y.property).1).2).1).1
  have hL2 := congrArg (fun z : (ℕ×ℕ)×(ℕ×ℕ) => z.1.2) hxy
  have hR2 := congrArg (fun z : (ℕ×ℕ)×(ℕ×ℕ) => z.2.2) hxy
  change x.val.1.2=y.val.1.2 at hL2
  change x.val.2.2=y.val.2.2 at hR2
  apply Prod.ext
  · exact Prod.ext (hfB _ xL _ yL (congrArg (fun z : (ℕ×ℕ)×(ℕ×ℕ) => z.1.1) hxy))
      hL2
  · exact Prod.ext (hfC _ xR _ yR (congrArg (fun z : (ℕ×ℕ)×(ℕ×ℕ) => z.2.1) hxy))
      hR2

/-- Physical singleton compaction only removes nonnegative original tuple
summands. Dictionary multiplicities and every wanted occurrence remain exact. -/
theorem potential_le (K J : ℕ) (L R : ℕ→ℕ→ℤ)
    (hfB : ∀ a<nB, ∀ b<nB, fB a=fB b→a=b)
    (hfC : ∀ a<nC, ∀ b<nC, fC a=fC b→a=b) :
    pairedPotential (small (r := r) maps τ cap Q I nB nC fB fC) K J
      (fun i => L (fB i)) (fun i => R (fC i))≤
      pairedPotential (full (r := r) maps τ cap Q I) K J L R := by
  unfold pairedPotential
  apply sum_le_sum
  intro i hi
  let e := embed (r := r) maps τ cap Q I nB nC fB fC hB hC (i := i.val)
  let lift := fun x : Fin K→Pair (small (r := r) maps τ cap Q I nB nC fB fC) i.val => fun k => e (x k)
  have hinj : Function.Injective lift := by
    intro a b hab
    funext k
    exact embed_injective (r := r) maps τ cap Q I nB nC fB fC hB hC hfB hfC i.val (congrFun hab k)
  let weight := fun x : Fin K→Pair (full (r := r) maps τ cap Q I) i.val =>
    TernaryPairedPotential.rowWeight (Sum.elim
      (fun k => originalLeft (full (r := r) maps τ cap Q I) J L i.val (x k))
      (fun k => originalRight (full (r := r) maps τ cap Q I) J R i.val (x k)))
  change (∑ x, weight (lift x))≤∑ x, weight x
  calc
    _ = ∑ x∈(univ : Finset (Fin K→Pair (small (r := r) maps τ cap Q I nB nC fB fC) i.val)).image lift, weight x := by
      rw [sum_image]
      exact fun a ha b hb h => hinj h
    _ ≤ _ := sum_le_sum_of_subset (subset_univ _)

end ThreeSum.TernaryArenaPairRestriction
