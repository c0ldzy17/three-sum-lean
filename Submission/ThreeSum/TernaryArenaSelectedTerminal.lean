import Submission.ThreeSum.TernaryArenaSelectedBudgets
import Submission.ThreeSum.TernaryArenaCompactSupport
import Submission.ThreeSum.TernaryPairedBudgetCollision

noncomputable section
namespace ThreeSum.TernaryArenaSelectedTerminal
open TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps
open TernaryArenaSourceSetup TernaryArenaSeedCandidate TernaryArenaSeedData
open TernaryArenaBudgetExistence TernaryArenaSelectedBudgets
set_option maxHeartbeats 5000000
variable {p m F : ℕ} [Fact p.Prime]

/-- A selected row state, read as the genuine simultaneous linear map. -/
def hashMap (A : Inputs) (s : State (p := p) A) (r : ℕ) :
    (Fin (A.J+2)→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p) :=
  LinearMap.pi (fun j => s.row j.val)

def input (I : Input) (A : Inputs) (s : State (p := p) A) (L R O : ℕ→ℕ→ℤ) (r : ℕ) : Input :=
  TernaryArenaPrefixGroups.input I (fun i t => L i t.val) (fun i t => R i t.val) s.row
    (root s.row (fun i t => O i t.val)) r

variable (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs) (K n U0 : ℕ) (L R O : ℕ→ℕ→ℤ) (r : ℕ) (s : State (p := p) A)

theorem native_zero (M C : ℕ)
    (hbudget : Budget maps τ cap Q I A K n U0 L R O r s)
    (hb : 0<9*pairFactor m F K)
    (hdrift : (9*pairFactor m F K)^4*M^(4*K+3)≤(p^(2*K))^4)
    (hcover : n^2≤M^r) (hinit : U0^4≤C*n^(8*K+5)) (hn : C<n) :
    TernaryNativeTensorScore.pairedPotential
      (setup (r := r) maps τ cap Q (input I A s L R O r)) K A.J L R=0 := by
  have hz := TernaryPairedBudgetSelector.terminal_zero K M (p^(2*K)) (9*pairFactor m F K)
    U0 (current maps τ cap I A s.row L R O Q r K) r n C hb hbudget.paired hdrift hcover hinit hn
  have he := TernaryArenaPrefixPotential.value_eq_native maps τ cap I L R s.row
    (root s.row (fun i t => O i t.val)) Q r K
  exact he.symm.trans hz

/-- Terminal potential zero immediately supplies the actual compact native
moment support bound used by the post-selection machine. -/
theorem compact_support (M C0 : ℕ) (B C : ℕ→ℤ) (a b : Fin (A.J+2))
    (hbudget : Budget maps τ cap Q I A K n U0 L R O r s)
    (hb : 0<9*pairFactor m F K)
    (hdrift : (9*pairFactor m F K)^4*M^(4*K+3)≤(p^(2*K))^4)
    (hcover : n^2≤M^r) (hinit : U0^4≤C0*n^(8*K+5)) (hn : C0<n)
    (hLtag : ∀j<I.nB, L j a.val=1 ∧ L j b.val=0)
    (hRtag : ∀j<I.nC, R j a.val=0 ∧ R j b.val=1)
    (hraw : ∀u<I.nB, ∀v<I.nC, ∀u'<I.nB, ∀v'<I.nC,
      (fun t : Fin (A.J+2) => (L u t.val : ZMod p))+(fun t => (R v t.val : ZMod p))=
      (fun t : Fin (A.J+2) => (L u' t.val : ZMod p))+(fun t => (R v' t.val : ZMod p))→
        C v-B u=C v'-B u') :
    let I₀ := input I A s L R O r
    let keysB := fun i => TernaryExtensionEncoding.coefficientCode (hashMap A s r (fun t => (L i t.val : ZMod p)))
    let keysC := fun i => TernaryExtensionEncoding.coefficientCode (hashMap A s r (fun t => (R i t.val : ZMod p)))
    let fB := LightOriginalSurvivors.index keysB I.nB
    let fC := LightOriginalSurvivors.index keysC I.nC
    let I' := TernaryArenaPairRestriction.restrict I₀ (LightOriginalSurvivors.indices keysB I.nB).length
      (LightOriginalSurvivors.indices keysC I.nC).length fB fC
    ∀i<(setup (r := r) maps τ cap Q I').front.count,
      (TernaryPairedSupport.physicalSupport (TernaryNativePairMoments.mode
        (fun j => B (fB j)) (fun j => C (fC j)) (S := setup (r := r) maps τ cap Q I') (i := i))).card≤2*p^K := by
  have hz := native_zero maps τ cap Q I A K n U0 L R O r s M C0 hbudget hb hdrift hcover hinit hn
  exact TernaryArenaCompactSupport.support maps τ cap Q (input I A s L R O r) L R B C
    (hashMap A s r) (fun i => hashMap A s r (fun t => (O i t.val : ZMod p)))
    (fun i => TernaryExtensionEncoding.coefficientCode (hashMap A s r (fun t => (L i t.val : ZMod p))))
    (fun i => TernaryExtensionEncoding.coefficientCode (hashMap A s r (fun t => (R i t.val : ZMod p))))
    a b (by intros; rfl) (by intros; rfl) (by intros; rfl) (by intros; rfl) (by intros; rfl)
    hLtag hRtag hraw hz

end ThreeSum.TernaryArenaSelectedTerminal
