import Submission.ThreeSum.TernaryArenaSeedCandidate
import Submission.ThreeSum.TernaryArenaPrefixStep
import Submission.ThreeSum.TernaryOriginalAppendSemantics

noncomputable section
namespace ThreeSum.TernaryArenaSeedData
open Finset TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps TernaryArenaSourceSetup
open TernaryArenaSeedCandidate LightTernarySeedScoreFactory TernaryExtensionEncoding
open TernaryOriginalRowMenu
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

def physical {J : ℕ} (v : ℕ→Fin (J+2)→ℤ) (i k : ℕ) : ℤ :=
  if hk : k<J+2 then v i (digitOrder J ⟨k,hk⟩) else 0

def root {J : ℕ} (row : ℕ→(Fin (J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (O : ℕ→Fin (J+2)→ℤ) (i j : ℕ) : ZMod p := row j (fun t => (O i t : ZMod p))

def hash {J : ℕ} (row : ℕ→(Fin (J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (r : ℕ) (v : ℕ→Fin (J+2)→ℤ) (i : ℕ) : Fin r→ZMod p :=
  fun j => row j.val (fun t => (v i t : ZMod p))

def data (I : Input) (A : Inputs) (r b seedOrdinal : ℕ)
    (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→Fin (A.J+2)→ℤ) (rows : List (Fin A.J→ZMod p))
    (catalog : ℕ→ℕ→ℕ) : Data (config p (r+1) I A seedOrdinal) where
  oldB:=fun i => coefficientCode (hash row r L i)
  oldC:=fun i => coefficientCode (hash row r R i)
  oldO:=fun i => coefficientCode (hash row r O i)
  B:=physical L
  Cvalues:=physical R
  O:=physical O
  coeff:=fun k => if hk : k<A.J+2 then (seedRow (A.J+2) ℓ seed (digitOrder A.J ⟨k,hk⟩)).val else 0
  position:=I.positions
  catalog:=catalog
  logicalRows:=rows
  logicalRow:=(show Fin (A.J+2)→ZMod p from seedRow (A.J+2) ℓ seed)
  bB:=b
  bC:=b
  bO:=b

theorem updated_hash {J r : ℕ}
    (row : ℕ→(Fin (J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (newrow : (Fin (J+2)→ZMod p)→ₗ[ZMod p] ZMod p) (v : ℕ→Fin (J+2)→ℤ) (i : ℕ) :
    hash (Function.update row r newrow) (r+1) v i=
      appendVector (hash row r v i) (newrow (fun t => (v i t : ZMod p))) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [hash,appendVector]
  · simp [hash,appendVector,Function.update_of_ne (Nat.ne_of_lt k.isLt)]

theorem key_eq (I : Input) (A : Inputs) (r b k : ℕ)
    (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (v : ℕ→Fin (A.J+2)→ℤ) (hv : ∀ i t, 0≤(p : ℤ)+v i t) (i : ℕ) :
    LightTernaryAppendKeys.key p (p^r) (A.J+2)
      (fun i => coefficientCode (hash row r v i)) (physical v)
      (fun k => if hk : k<A.J+2 then (seedRow (A.J+2) ℓ seed (digitOrder A.J ⟨k,hk⟩)).val else 0) i=
      coefficientCode (hash (Function.update row r (TernaryOriginalRowMenu.row (A.J+2) ℓ seed)) (r+1) v i) := by
  rw [updated_hash]
  exact TernaryOriginalAppendSemantics.append_key ℓ seed (v i) (physical v i) _ (hash row r v i)
    (by intro j; simp [physical,j.isLt])
    (by intro j hj; simpa only [physical,dif_pos hj] using hv i (digitOrder A.J ⟨j,hj⟩))
    (by intro j; simp [j.isLt])


theorem newB_eq (I : Input) (A : Inputs) (r b k : ℕ)
    (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→Fin (A.J+2)→ℤ) (rows : List (Fin A.J→ZMod p)) (catalog : ℕ→ℕ→ℕ)
    (hL : ∀ i t, 0≤(p : ℤ)+L i t) (i : ℕ) :
    (data I A r b k ℓ seed row L R O rows catalog).newB i=
      coefficientCode (hash (Function.update row r (TernaryOriginalRowMenu.row (A.J+2) ℓ seed)) (r+1) L i) := by
  exact key_eq I A r b k ℓ seed row L hL i

theorem newC_eq (I : Input) (A : Inputs) (r b k : ℕ)
    (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→Fin (A.J+2)→ℤ) (rows : List (Fin A.J→ZMod p)) (catalog : ℕ→ℕ→ℕ)
    (hR : ∀ i t, 0≤(p : ℤ)+R i t) (i : ℕ) :
    (data I A r b k ℓ seed row L R O rows catalog).newC i=
      coefficientCode (hash (Function.update row r (TernaryOriginalRowMenu.row (A.J+2) ℓ seed)) (r+1) R i) := by
  exact key_eq I A r b k ℓ seed row R hR i

theorem newO_eq (I : Input) (A : Inputs) (r b k : ℕ)
    (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→Fin (A.J+2)→ℤ) (rows : List (Fin A.J→ZMod p)) (catalog : ℕ→ℕ→ℕ)
    (hO : ∀ i t, 0≤(p : ℤ)+O i t) (i : ℕ) :
    (data I A r b k ℓ seed row L R O rows catalog).newO i=
      coefficientCode (hash (Function.update row r (TernaryOriginalRowMenu.row (A.J+2) ℓ seed)) (r+1) O i) := by
  exact key_eq I A r b k ℓ seed row O hO i

theorem root_update {J : ℕ}
    (row : ℕ→(Fin (J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (newrow : (Fin (J+2)→ZMod p)→ₗ[ZMod p] ZMod p) (O : ℕ→Fin (J+2)→ℤ) (r : ℕ) :
    root (Function.update row r newrow) O=
      fun o => Function.update (root row O o) r (newrow (fun t => (O o t : ZMod p))) := by
  funext o j
  by_cases hj : j=r
  · subst j; simp [root]
  · simp [root,Function.update_of_ne hj]

theorem sourceInput_eq (I : Input) (A : Inputs) (r b k : ℕ)
    (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→Fin (A.J+2)→ℤ) (rows : List (Fin A.J→ZMod p)) (catalog : ℕ→ℕ→ℕ)
    (hL : ∀ i t, 0≤(p : ℤ)+L i t) (hR : ∀ i t, 0≤(p : ℤ)+R i t) (hO : ∀ i t, 0≤(p : ℤ)+O i t) :
    sourceInput I A k (data I A r b k ℓ seed row L R O rows catalog)=
      TernaryArenaPrefixGroups.input I L R (Function.update row r (TernaryOriginalRowMenu.row (A.J+2) ℓ seed))
        (root (Function.update row r (TernaryOriginalRowMenu.row (A.J+2) ℓ seed)) O) (r+1) := by
  have hb := funext (newB_eq I A r b k ℓ seed row L R O rows catalog hL)
  have hc := funext (newC_eq I A r b k ℓ seed row L R O rows catalog hR)
  have ho := funext (newO_eq I A r b k ℓ seed row L R O rows catalog hO)
  unfold sourceInput Data.targets
  rw [hb,hc,ho]
  rfl

theorem flag_eq_one_iff (I : Input) (A : Inputs) (r b k : ℕ)
    (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→Fin (A.J+2)→ℤ) (rows : List (Fin A.J→ZMod p)) (catalog : ℕ→ℕ→ℕ) :
    (data I A r b k ℓ seed row L R O rows catalog).flag=1 ↔
      seed∈admissible (A.J+2) ℓ (TernaryPhysicalDigitSpan.forbidden rows) :=
by
  change ((LightStoredSpan.admissibleFlag (rows.map (TernaryPhysicalDigitSpan.reversal A.J))
    (TernaryPhysicalDigitSpan.physicalDigits (seedRow (A.J+2) ℓ seed)) : ℕ) : ℤ)=1 ↔ _
  rw [Nat.cast_eq_one]
  exact TernaryPhysicalDigitSpan.flag_menu_iff ℓ rows seed

theorem collisionB_eq (I : Input) (A : Inputs) (r b k : ℕ)
    (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→Fin (A.J+2)→ℤ) (rows : List (Fin A.J→ZMod p)) (catalog : ℕ→ℕ→ℕ)
    (hL : ∀ i t, 0≤(p : ℤ)+L i t) :
    (data I A r b k ℓ seed row L R O rows catalog).collisionB=
      (TernaryOriginalCollisions.nextCollisions ℓ (fun i : Fin I.nB => fun t => (L i.val t : ZMod p))
        (fun i : Fin I.nB => hash row r L i.val) seed : ℤ) := by
  unfold Data.collisionB
  simp_rw [newB_eq I A r b k ℓ seed row L R O rows catalog hL,updated_hash]
  rw [TernaryOriginalAppendSemantics.collision_count]
  rfl

theorem collisionC_eq (I : Input) (A : Inputs) (r b k : ℕ)
    (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→Fin (A.J+2)→ℤ) (rows : List (Fin A.J→ZMod p)) (catalog : ℕ→ℕ→ℕ)
    (hR : ∀ i t, 0≤(p : ℤ)+R i t) :
    (data I A r b k ℓ seed row L R O rows catalog).collisionC=
      (TernaryOriginalCollisions.nextCollisions ℓ (fun i : Fin I.nC => fun t => (R i.val t : ZMod p))
        (fun i : Fin I.nC => hash row r R i.val) seed : ℤ) := by
  unfold Data.collisionC
  simp_rw [newC_eq I A r b k ℓ seed row L R O rows catalog hR,updated_hash]
  rw [TernaryOriginalAppendSemantics.collision_count]
  rfl


theorem candidate_score {m F : ℕ} (maps : Fin F→Weight m p) (τ cap U V scoreBound : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (r b k K : ℕ)
    (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→ℕ→ℤ) (rows : List (Fin A.J→ZMod p)) (catalog : ℕ→ℕ→ℕ)
    (hR : ∀ i : ℕ, ∀ t : Fin (A.J+2), 0≤(p : ℤ)+R i t.val)
    (hO : ∀ i : ℕ, ∀ t : Fin (A.J+2), 0≤(p : ℤ)+O i t.val)
    (hLall : ∀ i : ℕ, ∀ t : Fin (A.J+2), 0≤(p : ℤ)+L i t.val) :
    (candidate maps τ cap U V scoreBound Q I A k
      (data I A r b k ℓ seed row (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) rows catalog) L R).score K=
      (2^(((r+1)*fixedPi m 2)*K)*
        TernaryArenaPrefixPotential.value maps τ cap I (fun i t => L i t.val) (fun i t => R i t.val)
          (Function.update row r (TernaryOriginalRowMenu.row (A.J+2) ℓ seed))
          (root (Function.update row r (TernaryOriginalRowMenu.row (A.J+2) ℓ seed)) (fun i t => O i t.val)) Q (r+1) K : ℕ) := by
  change ((2 : ℤ)^((r+1)*fixedPi m 2))^K*
    (TernaryNativeTensorScore.pairedPotential
      (setup (r := r+1) maps τ cap Q (sourceInput I A k
        (data I A r b k ℓ seed row (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) rows catalog)))
      K A.J L R : ℤ)=_
  rw [sourceInput_eq I A r b k ℓ seed row _ _ _ rows catalog hLall hR hO,
    ←TernaryArenaPrefixPotential.value_eq_native]
  push_cast
  rw [←pow_mul]

end ThreeSum.TernaryArenaSeedData
