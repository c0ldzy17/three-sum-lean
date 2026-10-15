import Submission.ThreeSum.TernaryArenaFamilyBudget
import Submission.ThreeSum.TernaryArenaPrefixInitial

noncomputable section
namespace ThreeSum.TernaryArenaSelectedBudgets
open Finset TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps TernaryCoverLocal
open TernaryArenaSourceSetup TernaryArenaSeedCandidate TernaryArenaSeedData
open TernaryArenaBudgetExistence TernaryArenaFamilyBudget
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

/-- Literal append changes the full vector collision count into the genuine
conditional collision score. -/
theorem collisions_update (A : Inputs) (ℓ : E→ₗ[ZMod p] ZMod p)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L : ℕ→ℕ→ℤ) (r n : ℕ) (seed : E×E) :
    collisions A (Function.update row r (TernaryOriginalRowMenu.row (A.J+2) ℓ seed)) L (r+1) n=
      nextCollision A ℓ row L r n seed := by
  unfold collisions nextCollision
  simp_rw [updated_hash]
  have he : TernaryOriginalCollisions.collisionPairs
      (fun i : Fin n => TernaryExtensionEncoding.appendVector
        (hash row r (fun i t => L i t.val) i.val)
        (TernaryOriginalRowMenu.row (A.J+2) ℓ seed (fun t => (L i.val t.val : ZMod p))))=
      TernaryOriginalCollisions.collisionPairs
      (fun i : Fin n => TernaryExtensionEncoding.coefficientCode (TernaryExtensionEncoding.appendVector
        (hash row r (fun i t => L i t.val) i.val)
        (TernaryOriginalRowMenu.row (A.J+2) ℓ seed (fun t => (L i.val t.val : ZMod p))))) := by
    ext ab
    simp only [TernaryOriginalCollisions.collisionPairs,mem_filter,mem_univ,true_and,
      (TernaryExtensionEncoding.coefficientCode_injective (r+1)).eq_iff]
  rw [he,TernaryOriginalAppendSemantics.collision_count]

structure State (A : Inputs) where
  row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p
  rows : List (Fin A.J→ZMod p)

def initial (A : Inputs) : State (p := p) A := ⟨0,[]⟩

variable (maps : Fin F→Weight m p) (τ cap U V scoreBound : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (b K n U0 : ℕ)
    (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→ℕ→ℤ) (catalog : ℕ→ℕ→ℕ→ℕ)

def candidates (j : ℕ) (s : State (p := p) A) :=
  family maps τ cap U V scoreBound Q I A j b e ℓ s.row L R O s.rows (catalog j)

def chosen (j : ℕ) (s : State (p := p) A) : ℕ :=
  LightTernaryRowSelector.pick
    (budgetGood (candidates maps τ cap U V scoreBound Q I A b e ℓ L R O catalog j s) p m F j K n U0) N-1

def step (j : ℕ) (s : State (p := p) A) : State (p := p) A :=
  let seed := seedAt e (chosen maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalog j s)
  ⟨Function.update s.row j (TernaryOriginalRowMenu.row (A.J+2) ℓ seed),
    TernaryPhysicalDigitSpan.digitProjection A.J (TernaryOriginalRowMenu.seedRow (A.J+2) ℓ seed)::s.rows⟩

/-- The semantic state uses exactly the ordinal returned by the actual
integer cross-product selector, with its documented one-based convention. -/
def run : ℕ→State (p := p) A
  | 0 => initial A
  | j+1 => step maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalog j
      (run j)

structure Budget (j : ℕ) (s : State (p := p) A) : Prop where
  paired : (p^(2*K))^j*current maps τ cap I A s.row L R O Q j K≤(9*pairFactor m F K)^j*U0
  left : p^j*collisions A s.row L j I.nB≤9^j*n^2
  right : p^j*collisions A s.row R j I.nC≤9^j*n^2
  length : s.rows.length=j

/-- All choices in a successful actual scan preserve the three budgets. -/
theorem step_budget (j : ℕ) (s : State (p := p) A)
    (hex : ∃i<N, budgetGood (candidates maps τ cap U V scoreBound Q I A b e ℓ L R O catalog j s) p m F j K n U0 i)
    (hL : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+L i t.val)
    (hR : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+R i t.val)
    (hO : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+O i t.val)
    (hlen : s.rows.length=j) :
    Budget maps τ cap Q I A K n U0 L R O (j+1)
      (step maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalog j s) := by
  let good := budgetGood (candidates maps τ cap U V scoreBound Q I A b e ℓ L R O catalog j s) p m F j K n U0
  have hg : good (chosen maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalog j s) :=
    LightTernaryRowSelector.pick_good good N ((LightTernaryRowSelector.pick_pos_iff good N).mpr hex)
  have h := good_preserves maps τ cap U V scoreBound Q I A j b K e ℓ s.row L R O s.rows (catalog j)
    n U0 _ hL hR hO hg
  refine ⟨h.1,?_,?_,by simp [step,hlen]⟩
  · simpa only [step,collisions_update] using h.2.1
  · simpa only [step,collisions_update] using h.2.2

theorem collisions_le_square (j : ℕ) (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L : ℕ→ℕ→ℤ) (q : ℕ) : collisions A row L j q≤q^2 := by
  unfold collisions TernaryOriginalCollisions.collisionPairs
  have h := Finset.card_le_card (Finset.filter_subset (s := (univ : Finset (Fin q×Fin q)))
    (p := fun ab => ab.1≠ab.2 ∧ hash row j (fun i t => L i t.val) ab.1.val=
      hash row j (fun i t => L i t.val) ab.2.val))
  simpa only [card_univ,Fintype.card_prod,Fintype.card_fin,pow_two] using h

theorem initial_budget
    (hL : ∀ i (t : Fin (A.J+2)), (L i t.val).natAbs≤b)
    (hR : ∀ i (t : Fin (A.J+2)), (R i t.val).natAbs≤b)
    (hB : I.nB≤n) (hC : I.nC≤n)
    (hU : I.requesterCount*n^(2*K)*(A.J+2)^(2*K)*((2*K).factorial*b^(2*K))^2≤U0) :
    Budget maps τ cap Q I A K n U0 L R O 0 (initial A) := by
  refine ⟨?_,?_,?_,rfl⟩
  · simp only [pow_zero,one_mul]
    exact (TernaryArenaPrefixInitial.actual_initializer_bound maps τ cap I
      (fun i t => L i t.val) (fun i t => R i t.val) (initial A).row
      (root (initial A).row (fun i t => O i t.val)) Q K b n hL hR hB hC).trans hU
  · simp only [pow_zero,one_mul]
    exact (collisions_le_square A 0 (initial A).row L I.nB).trans (Nat.pow_le_pow_left hB 2)
  · simp only [pow_zero,one_mul]
    exact (collisions_le_square A 0 (initial A).row R I.nC).trans (Nat.pow_le_pow_left hC 2)

/-- The complete deterministic prefix induction. Every selected ordinal is
exactly the real three-score scan result. There are no contraction or score
correctness assumptions in the induction hypotheses. -/
theorem run_budget (stop : ℕ) (hstop : stop≤A.J) (hℓ : ℓ≠0) (hp : 3≤p)
    (hL : ∀ i (t : Fin (A.J+2)), (L i t.val).natAbs≤b)
    (hR : ∀ i (t : Fin (A.J+2)), (R i t.val).natAbs≤b)
    (hLn : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+L i t.val)
    (hRn : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+R i t.val)
    (hOn : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+O i t.val)
    (hinjL : Function.Injective (fun i : Fin I.nB => fun t : Fin (A.J+2) => (L i.val t.val : ZMod p)))
    (hinjR : Function.Injective (fun i : Fin I.nC => fun t : Fin (A.J+2) => (R i.val t.val : ZMod p)))
    (hdet : (K+K).factorial*b^(K+K)<p)
    (hsize1 : 8*(A.J+2)*p^2≤Fintype.card E)
    (hsize : 8*(A.J+2)*p^(2*(K+K))≤Fintype.card E)
    (hB : I.nB≤n) (hC : I.nC≤n)
    (hU : I.requesterCount*n^(2*K)*(A.J+2)^(2*K)*((2*K).factorial*b^(2*K))^2≤U0) :
    ∀j≤stop, Budget maps τ cap Q I A K n U0 L R O j
      (run maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalog j) := by
  intro j
  induction j with
  | zero =>
    intro hj
    exact initial_budget maps τ cap Q I A b K n U0 L R O hL hR hB hC hU
  | succ j ih =>
    intro hj
    have hh := ih (by omega)
    let s := run maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalog j
    have hlength : s.rows.length=j := hh.length
    have hlen : s.rows.length<A.J := by omega
    have hex := exists_good maps τ cap U V scoreBound Q I A j b K e ℓ s.row L R O s.rows
      (catalog j) n U0 hℓ hlen hp hL hR hLn hRn hOn hinjL hinjR hdet hsize1 hsize
      hh.paired hh.left hh.right
    exact step_budget maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalog j s hex hLn hRn hOn hh.length

end ThreeSum.TernaryArenaSelectedBudgets
