import Submission.ThreeSum.TernaryColoredLoopSetup
import Submission.ThreeSum.TernaryColoredLoopAllocation
import Submission.ThreeSum.TernaryArenaLoop

noncomputable section
namespace ThreeSum.TernaryColoredLoopSetup
open Light TernaryArenaLayout TernaryArenaSourceSetup TernaryArenaSeedCandidate
open TernaryConcreteProfile TernaryLocalParameters TernaryArenaSelectedSigned
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {κ : ℕ}

/-- Concrete readiness from actual preprocessing reads and fixed profile
mathematics. No phase execution or selected-row oracle is assumed. -/
theorem ready (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (μ : ℕ→ℤ)
    [Fact (Irreducible (TernaryComputedExtensionMenu.modulus P.p (dim P n) c))]
    {lim : Limits} {depth : ℕ}
    (hw : (TernaryArenaAllocationResources.need P.allocation n (n^κ)).Ok lim
      (input P n free A B C).free (depth+2))
    (hmeta : TernaryPreparedOriginals.Metadata n (n^κ) A B C)
    (hinputs : TernaryArenaFixedParameters.InputGuards P.K P.m P.radix κ n)
    (horiginal : TernaryArenaPrefixInputs.Originals (input P n free A B C) (arrays P n free menu A B C)
      (q P n*q P n) P.radix P.radix n
      (TernaryComputedExtensionMenu.functional (p:=P.p) (c:=c) (dim_pos P n))
      (TernaryArenaFamilyBudget.seedAt (TernaryComputedExtensionMenu.seeds (p:=P.p) (d:=dim P n) (c:=c)))
      (left (n^κ) P.radix (J P n) (fun i=>B.getD i 0))
      (right (n^κ) P.radix (J P n) (fun i=>C.getD i 0))
      (requester (n^κ) P.radix (J P n) (fun i=>A.getD i 0)) μ) :
    TernaryArenaLoop.Ready (setup P n free menu c A B C μ) lim depth := by
  have hp9 : 9<P.p := P.primeLarge
  have hbp : P.radix≤P.p := by have hh : 2*P.radix<P.p:=P.basePrime;omega
  have hs:=field_sizes P n c
  have hc:=TernaryColoredLoopAllocation.control_words P n free A B C hw
  have htag:=P.tag_bound
  refine {
    hardware:=hw
    capacity:=rfl
    mpos:=P.blockPositive
    rounds:=le_rfl
    roundsPositive:=by
      exact Nat.clog_pos P.M_gt_one (by have:=hinputs.1;nlinarith)
    dimension:=rfl
    belowDimension:=hinputs.2.1.le
    leftCount:=hmeta.lengthB
    rightCount:=hmeta.lengthC
    targetCount:=Nat.mul_le_mul_right _ hmeta.lengthA
    positions:=le_rfl
    seeds:=by simp only [setup,q,dim,pow_two];exact le_rfl
    weights:=le_rfl
    tags:=htag
    weightLower:=?_
    prefixAt:=rfl
    family:=P.F_gt_one
    locals:=P.local_nonempty
    queryTime:=?_
    originals:=horiginal
    prepareEnvelope:=?_
    selectorWord:=?_
    budgets:=budgets P n free menu c A B C μ hmeta hinputs
    ellNonzero:=TernaryComputedExtensionMenu.functional_ne_zero (dim_pos P n)
    prime:=by change 3≤P.p;omega
    leftBound:=fun i t=>left_bound P.radix_gt_one (fun i=>B.getD i 0) i t.val
    rightBound:=fun i t=>right_bound P.radix_gt_one (fun i=>C.getD i 0) i t.val
    leftNonneg:=fun i t=>signed_nonnegative hbp (left_bound P.radix_gt_one (fun i=>B.getD i 0) i t.val)
    rightNonneg:=fun i t=>signed_nonnegative hbp (right_bound P.radix_gt_one (fun i=>C.getD i 0) i t.val)
    targetNonneg:=fun i t=>signed_nonnegative hbp (requester_bound P.radix_gt_one (fun i=>A.getD i 0) i t.val)
    leftInjective:=left_injective P n A B C hmeta hinputs
    rightInjective:=right_injective P n A B C hmeta hinputs
    minor:=by simpa only [setup,←two_mul,Profile.radix,Profile.p] using P.minor
    fieldSize1:=hs.1
    fieldSize:=hs.2
    threshold:=TernaryCoverCapParameters.rawThreshold_pos _ _ _
    nonempty:=?_
    roundsWord:=hc.1
    powerWords:=hc.2 }
  · change P.radix^2≤weight P n
    have hh:=Nat.pow_le_pow_left htag 2
    unfold weight TernaryArenaPrefixFootprints.weight
    omega
  · intro j hj
    exact query_time P n free A B C (j+1) (by change j<rounds P n at hj;omega)
  · intro j hj
    exact TernaryColoredLoopAllocation.prepare_envelope P n free A B C hmeta.lengthA j hj
  · intro j hj
    exact TernaryColoredLoopAllocation.selector_word P n free A B C hmeta.lengthA hw j hj
  · change 1≤(TernaryGoodOutputCatalog.raws P.maps P.threshold).length
    rw [TernaryGoodOutputCatalog.raws_length]
    exact TernaryExecutableParameters.output_nonempty P.K_pos P.blockPositive P.k_pos

end ThreeSum.TernaryColoredLoopSetup
