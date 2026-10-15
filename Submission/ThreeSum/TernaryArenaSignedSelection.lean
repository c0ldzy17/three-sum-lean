import Submission.ThreeSum.TernaryArenaSelectedSigned
import Submission.ThreeSum.LightTernaryInitialBudgets

noncomputable section
namespace ThreeSum.TernaryArenaSignedSelection
open TernaryArenaSourceSetup TernaryArenaSeedCandidate TernaryArenaSelectedBudgets
open TernaryArenaSelectedSigned TernaryArenaBudgetExistence TernaryCoverGoodMaps
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

variable (maps : Fin F→Weight m p) (τ cap U V scoreBound : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (K n radix nA : ℕ)
    (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p)
    (X B C : ℕ→ℤ) (catalog : ℕ→ℕ→ℕ→ℕ)

/-- The initial scalar is exactly the finite integer written by the
actual initialization kernel. -/
def initialBudget : ℕ := LightTernaryInitialBudgets.initial K radix n A.J (nA*2^A.J)

def state (r : ℕ) : State (p := p) A :=
  run maps τ cap U V scoreBound Q (base I A.J nA) A radix K n (initialBudget A K n radix nA) e ℓ
    (left U radix A.J B) (right U radix A.J C) (requester U radix A.J X) catalog r

/-- All signed-input side conditions of the deterministic real selector
follow from the original bounded distinct source integers. -/
theorem budget (stop : ℕ) (hstop : stop≤A.J) (hℓ : ℓ≠0) (hp : 3≤p)
    (hbase : 1<radix) (hprime : 2*radix<p) (hcap : 4*U<radix^A.J)
    (hinjB : Function.Injective (fun i : Fin I.nB => B i.val))
    (hinjC : Function.Injective (fun i : Fin I.nC => C i.val))
    (hB : ∀i<I.nB, |B i|≤(U : ℤ)) (hC : ∀i<I.nC, |C i|≤(U : ℤ))
    (hdet : (K+K).factorial*radix^(K+K)<p)
    (hsize1 : 8*(A.J+2)*p^2≤Fintype.card E)
    (hsize : 8*(A.J+2)*p^(2*(K+K))≤Fintype.card E)
    (hnB : I.nB≤n) (hnC : I.nC≤n) :
    ∀j≤stop, Budget maps τ cap Q (base I A.J nA) A K n (initialBudget A K n radix nA)
      (left U radix A.J B) (right U radix A.J C) (requester U radix A.J X) j
      (state maps τ cap U V scoreBound Q I A K n radix nA e ℓ X B C catalog j) := by
  have hbp : radix≤p := by omega
  exact run_budget maps τ cap U V scoreBound Q (base I A.J nA) A radix K n
    (initialBudget A K n radix nA) e ℓ (left U radix A.J B) (right U radix A.J C)
    (requester U radix A.J X) catalog stop hstop hℓ hp
    (fun i t => left_bound hbase B i t.val) (fun i t => right_bound hbase C i t.val)
    (fun i t => signed_nonnegative hbp (left_bound hbase B i t.val))
    (fun i t => signed_nonnegative hbp (right_bound hbase C i t.val))
    (fun i t => signed_nonnegative hbp (requester_bound hbase X i t.val))
    (TernarySignedFeatureHash.left_injective (fun i : Fin I.nB => B i.val) hbase hprime hcap
      (fun i => hB i.val i.isLt) hinjB)
    (TernarySignedFeatureHash.right_injective (fun i : Fin I.nC => C i.val) hbase hprime hcap
      (fun i => hC i.val i.isLt) hinjC)
    hdet hsize1 hsize hnB hnC (by rfl)

/-- Closed original signed selection: the literal computed initial budget,
actual three-score row scan, retained native groups and integer drift give
zero potential for the exact final solver input. -/
theorem native_zero (r M : ℕ) (hr : r≤A.J) (hℓ : ℓ≠0) (hp : 3≤p)
    (hbase : 1<radix) (hprime : 2*radix<p) (hcap : 4*U<radix^A.J)
    (hinjB : Function.Injective (fun i : Fin I.nB => B i.val))
    (hinjC : Function.Injective (fun i : Fin I.nC => C i.val))
    (hB : ∀i<I.nB, |B i|≤(U : ℤ)) (hC : ∀i<I.nC, |C i|≤(U : ℤ))
    (hdet : (K+K).factorial*radix^(K+K)<p)
    (hsize1 : 8*(A.J+2)*p^2≤Fintype.card E)
    (hsize : 8*(A.J+2)*p^(2*(K+K))≤Fintype.card E)
    (hnA : nA≤n) (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hfactor : 0<9*pairFactor m F K)
    (hdrift : (9*pairFactor m F K)^4*M^(4*K+3)≤(p^(2*K))^4)
    (hcover : n^2≤M^r) (hcarry : (2^A.J)^4*(A.J+2)^(8*K)≤n)
    (hn : ((2*K).factorial*radix^(2*K))^8<n) :
    let s := state maps τ cap U V scoreBound Q I A K n radix nA e ℓ X B C catalog r
    TernaryNativeTensorScore.pairedPotential
      (setup (r := r) maps τ cap Q
        (TernaryArenaNativeComplete.input I U radix nA (selectedHash A s r) X B C)) K A.J
      (fun j i => TernarySignedLayout.feature (TernarySignedReduction.leftRaw U radix A.J (B j)) i)
      (fun j i => TernarySignedLayout.feature (TernarySignedReduction.rightRaw U radix A.J (C j)) i)=0 := by
  have hh := budget maps τ cap U V scoreBound Q I A K n radix nA e ℓ X B C catalog
    r hr hℓ hp hbase hprime hcap hinjB hinjC hB hC hdet hsize1 hsize hnB hnC r le_rfl
  have hi : (initialBudget A K n radix nA)^4≤
      ((2*K).factorial*radix^(2*K))^8*n^(8*K+5) := by
    have ht : nA*2^A.J≤n*2^A.J := Nat.mul_le_mul_right _ hnA
    have hb := TernaryPairedInitialBudget.target_count_fourth_bound K (A.J+2) radix n (2^A.J)
      (nA*2^A.J) 1 ht (by simpa only [one_mul] using hcarry)
    simpa only [initialBudget,LightTernaryInitialBudgets.initial,
      LightTernaryInitialBudgets.determinantBound,one_mul] using hb
  exact native_signed_zero maps τ cap Q I A K n (initialBudget A K n radix nA)
    r U radix nA M (((2*K).factorial*radix^(2*K))^8)
    (state maps τ cap U V scoreBound Q I A K n radix nA e ℓ X B C catalog r) X B C
    hh hfactor hdrift hcover hi hn

end ThreeSum.TernaryArenaSignedSelection
