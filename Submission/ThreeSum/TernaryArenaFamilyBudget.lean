import Submission.ThreeSum.TernaryArenaBudgetExistence

noncomputable section
namespace ThreeSum.TernaryArenaFamilyBudget
open Finset TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps TernaryCoverLocal
open TernaryArenaSourceSetup TernaryArenaSeedCandidate LightTernarySeedScoreFactory
open LightTernaryControllerFactory TernaryOriginalRowMenu TernaryExtensionEncoding
open TernaryArenaSeedData TernaryArenaBudgetExistence
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

def seedAt (e : (E×E)≃Fin N) (i : ℕ) : E×E := if hi : i<N then e.symm ⟨i,hi⟩ else (0,0)

@[simp] theorem seedAt_index (e : (E×E)≃Fin N) (seed : E×E) : seedAt e (e seed).val=seed := by
  simp [seedAt,(e seed).isLt]

def family (maps : Fin F→Weight m p) (τ cap U V scoreBound : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (r b : ℕ)
    (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→ℕ→ℤ) (rows : List (Fin A.J→ZMod p)) (catalog : ℕ→ℕ→ℕ) :
    Family (config p (r+1) I A 0) :=
  TernaryArenaSeedCandidate.family maps τ cap U V scoreBound Q I A
    (fun k => data I A r b k ℓ (seedAt e k) row (fun i t => L i t.val) (fun i t => R i t.val)
      (fun i t => O i t.val) rows catalog) L R

variable (maps : Fin F→Weight m p) (τ cap U V scoreBound : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (r b K : ℕ)
    (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→ℕ→ℤ) (rows : List (Fin A.J→ZMod p)) (catalog : ℕ→ℕ→ℕ)

abbrev D := family maps τ cap U V scoreBound Q I A r b e ℓ row L R O rows catalog

theorem flag_one (seed : E×E)
    (hs : seed∈admissible (A.J+2) ℓ (TernaryPhysicalDigitSpan.forbidden rows)) :
    (D maps τ cap U V scoreBound Q I A r b e ℓ row L R O rows catalog).flag (e seed).val=1 := by
  change (data I A r b (e seed).val ℓ (seedAt e (e seed).val) row
    (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) rows catalog).flag=1
  rw [seedAt_index]
  exact (flag_eq_one_iff I A r b _ ℓ seed row _ _ _ rows catalog).mpr hs

theorem scoreB_eq (i : ℕ) (hL : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+L i t.val) :
    (D maps τ cap U V scoreBound Q I A r b e ℓ row L R O rows catalog).scoreB i=
      (nextCollision A ℓ row L r I.nB (seedAt e i) : ℤ) :=
  collisionB_eq I A r b i ℓ (seedAt e i) row _ _ _ rows catalog hL

theorem scoreC_eq (i : ℕ) (hR : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+R i t.val) :
    (D maps τ cap U V scoreBound Q I A r b e ℓ row L R O rows catalog).scoreC i=
      (nextCollision A ℓ row R r I.nC (seedAt e i) : ℤ) :=
  collisionC_eq I A r b i ℓ (seedAt e i) row _ _ _ rows catalog hR

theorem scoreP_eq (i : ℕ)
    (hL : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+L i t.val)
    (hR : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+R i t.val)
    (hO : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+O i t.val) :
    (D maps τ cap U V scoreBound Q I A r b e ℓ row L R O rows catalog).scoreP K i=
      (scale m r K*nextValue maps τ cap I A ℓ row L R O Q r K (seedAt e i) : ℕ) :=
  candidate_score maps τ cap U V scoreBound Q I A r b i K ℓ (seedAt e i) row L R O rows catalog hR hO hL

/-- The existential average witness is an actual integer ordinal visited by
Controller166, with the literal admissibility flag and actual three scores. -/
theorem good_of_seed (n U0 : ℕ) (seed : E×E)
    (hs : seed∈admissible (A.J+2) ℓ (TernaryPhysicalDigitSpan.forbidden rows))
    (hL : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+L i t.val)
    (hR : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+R i t.val)
    (hO : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+O i t.val)
    (hp : (p^(2*K))^(r+1)*(scale m r K*nextValue maps τ cap I A ℓ row L R O Q r K seed)≤
      scale m r K*(9*pairFactor m F K)^(r+1)*U0)
    (hb : p^(r+1)*nextCollision A ℓ row L r I.nB seed≤9^(r+1)*n^2)
    (hc : p^(r+1)*nextCollision A ℓ row R r I.nC seed≤9^(r+1)*n^2) :
    ∃i<N, LightTernaryRowSelector.Good
      (D maps τ cap U V scoreBound Q I A r b e ℓ row L R O rows catalog).flag
      (D maps τ cap U V scoreBound Q I A r b e ℓ row L R O rows catalog).scoreB
      (D maps τ cap U V scoreBound Q I A r b e ℓ row L R O rows catalog).scoreC
      ((D maps τ cap U V scoreBound Q I A r b e ℓ row L R O rows catalog).scoreP K)
      (p^(r+1)) (p^(r+1)) ((p^(2*K))^(r+1))
      (9^(r+1)*n^2) (9^(r+1)*n^2) (scale m r K*(9*pairFactor m F K)^(r+1)*U0) i := by
  refine ⟨(e seed).val,(e seed).isLt,?_,?_,?_,?_⟩
  · rw [flag_one maps τ cap U V scoreBound Q I A r b e ℓ row L R O rows catalog seed hs]
    norm_num
  · rw [scoreB_eq maps τ cap U V scoreBound Q I A r b e ℓ row L R O rows catalog _ hL,seedAt_index]
    exact_mod_cast (by simpa only [Nat.mul_comm] using hb)
  · rw [scoreC_eq maps τ cap U V scoreBound Q I A r b e ℓ row L R O rows catalog _ hR,seedAt_index]
    exact_mod_cast (by simpa only [Nat.mul_comm] using hc)
  · rw [scoreP_eq maps τ cap U V scoreBound Q I A r b K e ℓ row L R O rows catalog _ hL hR hO,seedAt_index]
    exact_mod_cast (by simpa only [Nat.mul_comm] using hp)


def budgetGood {C : Config} [Fact C.p.Prime] (D : Family C) (p m F r K n U0 : ℕ) (i : ℕ) : Prop :=
  LightTernaryRowSelector.Good D.flag D.scoreB D.scoreC (D.scoreP K)
    (p^(r+1)) (p^(r+1)) ((p^(2*K))^(r+1))
    (9^(r+1)*n^2) (9^(r+1)*n^2) (scale m r K*(9*pairFactor m F K)^(r+1)*U0) i

/-- This is the complete actual controller's existential premise, derived
from original input vectors and the previous upper budgets. -/
theorem exists_good (n U0 : ℕ) (hℓ : ℓ≠0) (hlen : rows.length<A.J) (hp : 3≤p)
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
    (hPi : (p^(2*K))^r*current maps τ cap I A row L R O Q r K≤(9*pairFactor m F K)^r*U0)
    (hB : p^r*collisions A row L r I.nB≤9^r*n^2)
    (hC : p^r*collisions A row R r I.nC≤9^r*n^2) :
    ∃i<N, budgetGood (D maps τ cap U V scoreBound Q I A r b e ℓ row L R O rows catalog) p m F r K n U0 i := by
  obtain ⟨seed,hs,hp,hb,hc⟩ := TernaryArenaBudgetExistence.exists_seed maps τ cap I A ℓ hℓ row L R O Q
    rows hlen r K b n U0 hp hL hR hinjL hinjR hdet hsize1 hsize hPi hB hC
  exact good_of_seed maps τ cap U V scoreBound Q I A r b K e ℓ row L R O rows catalog n U0 seed hs hLn hRn hOn hp hb hc

/-- The actual chosen score test preserves all upper budgets. Positive
factorial scaling cancels; the initial paired potential is never evaluated. -/
theorem good_preserves (n U0 i : ℕ)
    (hL : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+L i t.val)
    (hR : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+R i t.val)
    (hO : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+O i t.val)
    (hg : budgetGood (D maps τ cap U V scoreBound Q I A r b e ℓ row L R O rows catalog) p m F r K n U0 i) :
    (p^(2*K))^(r+1)*nextValue maps τ cap I A ℓ row L R O Q r K (seedAt e i)≤
      (9*pairFactor m F K)^(r+1)*U0 ∧
      p^(r+1)*nextCollision A ℓ row L r I.nB (seedAt e i)≤9^(r+1)*n^2 ∧
      p^(r+1)*nextCollision A ℓ row R r I.nC (seedAt e i)≤9^(r+1)*n^2 := by
  rcases hg with ⟨hf,hb,hc,hp⟩
  rw [scoreB_eq maps τ cap U V scoreBound Q I A r b e ℓ row L R O rows catalog i hL] at hb
  rw [scoreC_eq maps τ cap U V scoreBound Q I A r b e ℓ row L R O rows catalog i hR] at hc
  rw [scoreP_eq maps τ cap U V scoreBound Q I A r b K e ℓ row L R O rows catalog i hL hR hO] at hp
  have hbn : p^(r+1)*nextCollision A ℓ row L r I.nB (seedAt e i)≤9^(r+1)*n^2 := by
    norm_cast at hb
    simpa only [mul_comm] using hb
  have hcn : p^(r+1)*nextCollision A ℓ row R r I.nC (seedAt e i)≤9^(r+1)*n^2 := by
    norm_cast at hc
    simpa only [mul_comm] using hc
  have hpn : (p^(2*K))^(r+1)*(scale m r K*nextValue maps τ cap I A ℓ row L R O Q r K (seedAt e i))≤
      scale m r K*(9*pairFactor m F K)^(r+1)*U0 := by
    norm_cast at hp
    simpa only [mul_comm] using hp
  exact ⟨TernaryPairedBudgetSelector.cancel_scale _ _ _ _ _ (by unfold scale; positivity) hpn,hbn,hcn⟩

end ThreeSum.TernaryArenaFamilyBudget
