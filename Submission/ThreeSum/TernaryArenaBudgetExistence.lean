import Submission.ThreeSum.TernaryArenaSeedData
import Submission.ThreeSum.TernaryPairedBudgetSelector

noncomputable section
namespace ThreeSum.TernaryArenaBudgetExistence
open Finset TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps TernaryCoverLocal
open TernaryArenaSourceSetup TernaryArenaSeedCandidate LightTernarySeedScoreFactory
open TernaryOriginalRowMenu TernaryExtensionEncoding TernaryArenaSeedData
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

def pairFactor (m F K : ℕ) : ℕ := F*(vertices (fixedLength m) (fixedPi m)).card*
  (2^(fixedPi m 1)*3^(fixedPi m 2))^K

def scale (m r K : ℕ) : ℕ := 2^(((r+1)*fixedPi m 2)*K)

def current (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input) (A : Inputs)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p) (L R O : ℕ→ℕ→ℤ)
    (Q : TernaryGoodOutputCatalog.Output m) (r K : ℕ) : ℕ :=
  TernaryArenaPrefixPotential.value maps τ cap I (fun i t => L i t.val) (fun i t => R i t.val)
    row (root row (fun i t => O i t.val)) Q r K

def nextValue (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input) (A : Inputs)
    (ℓ : E→ₗ[ZMod p] ZMod p) (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→ℕ→ℤ) (Q : TernaryGoodOutputCatalog.Output m) (r K : ℕ) (seed : E×E) : ℕ :=
  current maps τ cap I A (Function.update row r (TernaryOriginalRowMenu.row (A.J+2) ℓ seed)) L R O Q (r+1) K

def collisions (A : Inputs) (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L : ℕ→ℕ→ℤ) (r n : ℕ) : ℕ :=
  (TernaryOriginalCollisions.collisionPairs (fun i : Fin n => hash row r (fun i t => L i t.val) i.val)).card

def nextCollision (A : Inputs) (ℓ : E→ₗ[ZMod p] ZMod p)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p) (L : ℕ→ℕ→ℤ) (r n : ℕ) (seed : E×E) : ℕ :=
  TernaryOriginalCollisions.nextCollisions ℓ (fun i : Fin n => fun t : Fin (A.J+2) => (L i.val t.val : ZMod p))
    (fun i : Fin n => hash row r (fun i t => L i t.val) i.val) seed

theorem exists_seed (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input) (A : Inputs)
    (ℓ : E→ₗ[ZMod p] ZMod p) (hℓ : ℓ≠0)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→ℕ→ℤ) (Q : TernaryGoodOutputCatalog.Output m)
    (rows : List (Fin A.J→ZMod p)) (hlen : rows.length<A.J)
    (r K b n U0 : ℕ) (hp : 3≤p)
    (hL : ∀ i (t : Fin (A.J+2)), (L i t.val).natAbs≤b)
    (hR : ∀ i (t : Fin (A.J+2)), (R i t.val).natAbs≤b)
    (hinjL : Function.Injective (fun i : Fin I.nB => fun t : Fin (A.J+2) => (L i.val t.val : ZMod p)))
    (hinjR : Function.Injective (fun i : Fin I.nC => fun t : Fin (A.J+2) => (R i.val t.val : ZMod p)))
    (hdet : (K+K).factorial*b^(K+K)<p)
    (hsize1 : 8*(A.J+2)*p^2≤Fintype.card E)
    (hsize : 8*(A.J+2)*p^(2*(K+K))≤Fintype.card E)
    (hPi : (p^(2*K))^r*current maps τ cap I A row L R O Q r K≤(9*pairFactor m F K)^r*U0)
    (hB : p^r*collisions A row L r I.nB≤9^r*n^2)
    (hC : p^r*collisions A row R r I.nC≤9^r*n^2) :
    ∃seed∈admissible (A.J+2) ℓ (TernaryPhysicalDigitSpan.forbidden rows),
      (p^(2*K))^(r+1)*(scale m r K*nextValue maps τ cap I A ℓ row L R O Q r K seed)≤
        scale m r K*(9*pairFactor m F K)^(r+1)*U0 ∧
      p^(r+1)*nextCollision A ℓ row L r I.nB seed≤9^(r+1)*n^2 ∧
      p^(r+1)*nextCollision A ℓ row R r I.nC seed≤9^(r+1)*n^2 := by
  let V := TernaryPhysicalDigitSpan.forbidden rows
  let S := admissible (A.J+2) ℓ V
  have hV : V≠⊤ := TernaryPhysicalDigitSpan.forbidden_proper rows hlen
  have hhalf := admissible_at_least_half (A.J+2) ℓ hℓ V hV (by simpa using hp) (by simpa using hsize1)
  have hS : S.Nonempty := Finset.card_pos.mp (by
    have hE : 0<Fintype.card E := Fintype.card_pos_iff.mpr ⟨0⟩
    have hE2 : 0<Fintype.card E^2 := pow_pos hE _
    change 0<(admissible (A.J+2) ℓ V).card
    omega)
  have hpI := TernaryArenaPrefixStep.sum_appended_bound maps τ cap I
    (fun i t => L i t.val) (fun i t => R i t.val) row (root row (fun i t => O i t.val)) Q
    ℓ hℓ V hV hp (fun seed i => TernaryOriginalRowMenu.row (A.J+2) ℓ seed (fun t => (O i t.val : ZMod p)))
    r K b hL hR hdet hsize1 hsize
  have hPiAvg : p^(2*K)*(∑seed∈S,nextValue maps τ cap I A ℓ row L R O Q r K seed)≤
      3*S.card*pairFactor m F K*current maps τ cap I A row L R O Q r K := by
    have hu : K+K=2*K := by omega
    simp_rw [←root_update] at hpI
    rw [hu] at hpI
    convert hpI using 1 <;> simp only [nextValue,current,S,pairFactor] <;> ring
  have hBavg : p*(∑seed∈S,nextCollision A ℓ row L r I.nB seed)≤3*S.card*collisions A row L r I.nB := by
    simpa only [ZMod.card,collisions,nextCollision] using
      TernaryOriginalCollisions.sum_nextCollisions_bound ℓ hℓ _ hinjL
        (fun i : Fin I.nB => hash row r (fun i t => L i t.val) i.val) V hV (by simpa using hp)
        (by simpa using hsize1)
  have hCavg : p*(∑seed∈S,nextCollision A ℓ row R r I.nC seed)≤3*S.card*collisions A row R r I.nC := by
    simpa only [ZMod.card,collisions,nextCollision] using
      TernaryOriginalCollisions.sum_nextCollisions_bound ℓ hℓ _ hinjR
        (fun i : Fin I.nC => hash row r (fun i t => R i t.val) i.val) V hV (by simpa using hp)
        (by simpa using hsize1)
  exact TernaryPairedBudgetSelector.exists_budget_row S hS (p^(2*K)) (pairFactor m F K) p (scale m r K) r U0 (n^2)
    (current maps τ cap I A row L R O Q r K) (collisions A row L r I.nB) (collisions A row R r I.nC)
    (pow_pos (Fact.out : p.Prime).pos _) (Fact.out : p.Prime).pos
    (nextValue maps τ cap I A ℓ row L R O Q r K) (nextCollision A ℓ row L r I.nB) (nextCollision A ℓ row R r I.nC)
    hPiAvg hBavg hCavg hPi hB hC

end ThreeSum.TernaryArenaBudgetExistence
