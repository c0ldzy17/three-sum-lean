import Submission.ThreeSum.TernaryArenaPhase
import Submission.ThreeSum.TernaryPreparedOriginals
import Submission.ThreeSum.TernaryArenaSignedSelection
import Submission.ThreeSum.TernaryArenaFixedParameters

noncomputable section
namespace ThreeSum.TernaryArenaPhaseBudget
open TernaryArenaSourceSetup TernaryArenaSeedCandidate TernaryArenaSelectedBudgets
open TernaryArenaSeedData TernaryArenaBudgetExistence TernaryArenaFamilyBudget
open TernaryCoverGoodMaps TernaryLocalParameters TernaryExtensionEncoding
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

theorem threshold (m j K F U0 : ℕ) :
    U0*((9*pairFactor m F K)*(2^((fixedPi m 2)*K)))^(j+1)=
      scale m j K*(9*pairFactor m F K)^(j+1)*U0 := by
  have hs : (2^((fixedPi m 2)*K))^(j+1)=scale m j K := by
    unfold scale
    rw [←pow_mul]
    congr 1
    ring
  rw [mul_pow,hs]
  ring

/-- Exact scalar field-size guards for the extension degree computed by the
actual prelude. -/
theorem field_sizes (J K : ℕ) (hK : 0<K)
    (hcard : Fintype.card E=p^(menuDegree p (J+2) K)) :
    8*(J+2)*p^2≤Fintype.card E ∧ 8*(J+2)*p^(2*(K+K))≤Fintype.card E := by
  have hlow := menu_field_lower (p := p) (J+2) K
  have hpow : p^2≤p^(4*K) := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
  have hΛ : 8*(J+2)*p^(4*K)≤8*((J+2)+1)*p^(4*K) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 8 (Nat.le_succ (J+2)))
  rw [hcard]
  constructor
  · calc
      _≤8*(J+2)*p^(4*K) := Nat.mul_le_mul_left _ hpow
      _≤8*((J+2)+1)*p^(4*K) := hΛ
      _≤_ := hlow
  · have he : 2*(K+K)=4*K := by omega
    rw [he]
    exact hΛ.trans hlow

/-- The literal Core-family phase existential follows from the proved
selected-prefix budgets, including the machine's exact geometric threshold. -/
theorem good (maps : Fin F→Weight m p) (τ cap tag : ℕ) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs) (j b K n U0 : ℕ) (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p)
    (s : State (p := p) A) (L R O : ℕ→ℕ→ℤ) (catalog : ℕ→ℕ→ℕ)
    (hbudget : Budget maps τ cap Q I A K n U0 L R O j s)
    (hj : j<A.J) (hℓ : ℓ≠0) (hp : 3≤p)
    (hL : ∀ i (t : Fin (A.J+2)), (L i t.val).natAbs≤b)
    (hR : ∀ i (t : Fin (A.J+2)), (R i t.val).natAbs≤b)
    (hLn : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+L i t.val)
    (hRn : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+R i t.val)
    (hOn : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+O i t.val)
    (hinjL : Function.Injective (fun i : Fin I.nB => fun t : Fin (A.J+2) => (L i.val t.val : ZMod p)))
    (hinjR : Function.Injective (fun i : Fin I.nC => fun t : Fin (A.J+2) => (R i.val t.val : ZMod p)))
    (hdet : (K+K).factorial*b^(K+K)<p)
    (hsize1 : 8*(A.J+2)*p^2≤Fintype.card E) (hsize : 8*(A.J+2)*p^(2*(K+K))≤Fintype.card E) :
    ∃i<N,LightTernaryRowSelector.Good
      (TernaryArenaPhase.family maps τ cap tag Q I A j b ℓ (seedAt e) L R O s catalog).flag
      (TernaryArenaPhase.family maps τ cap tag Q I A j b ℓ (seedAt e) L R O s catalog).scoreB
      (TernaryArenaPhase.family maps τ cap tag Q I A j b ℓ (seedAt e) L R O s catalog).scoreC
      ((TernaryArenaPhase.family maps τ cap tag Q I A j b ℓ (seedAt e) L R O s catalog).scoreP K)
      (p^(j+1)) (p^(j+1)) ((p^(2*K))^(j+1)) (9^(j+1)*n^2) (9^(j+1)*n^2)
      (U0*((9*pairFactor m F K)*(2^((fixedPi m 2)*K)))^(j+1)) i := by
  have hlen : s.rows.length<A.J := by rw [hbudget.length];exact hj
  obtain ⟨i,hi,hg⟩ := exists_good maps τ cap tag (TernaryArenaSeedPrimitiveGuards.rawCap m p (j+1))
    (TernaryNativeMomentBounds.scoreBound (setup (r := j+1) maps τ cap Q I)) Q I A j b K e ℓ
    s.row L R O s.rows catalog n U0 hℓ hlen hp hL hR hLn hRn hOn hinjL hinjR hdet hsize1 hsize
    hbudget.paired hbudget.left hbudget.right
  refine ⟨i,hi,?_⟩
  rw [threshold]
  exact hg

/-- Actual normalized preprocessing and actual prelude dimensions yield the
literal phase selector witness at every prefix. There is no good-row,
contraction, previous-budget or source-injectivity premise. -/
theorem prepared_good (maps : Fin F→Weight m p) (τ cap V scoreBound : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (free n U radix K C0 weightCap queryTime menu j : ℕ)
    (A B C : List ℤ) (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p)
    (catalogs : ℕ→ℕ→ℕ→ℕ) (catalog : ℕ→ℕ→ℕ)
    (hmeta : TernaryPreparedOriginals.Metadata n U A B C)
    (hK : 0<K) (hb : 1<radix) (hp : 2*radix<p) (hℓ : ℓ≠0)
    (hdet : (2*K).factorial*radix^(2*K)<p)
    (hj : j<LightTernaryDimensions.r (TernaryCoverScale.outputSize m) n)
    (hcard : Fintype.card E=p^(menuDegree p
      (LightTernaryDimensions.J (TernaryCoverScale.outputSize m) radix n U+2) K)) :
    let J := LightTernaryDimensions.J (TernaryCoverScale.outputSize m) radix n U
    let I := TernaryPreparedOriginals.input free n U J C0 weightCap queryTime A B C
    let AP := TernaryPreparedOriginals.inputs free n J menu A B C
    let L := TernaryArenaSelectedSigned.left U radix J (fun i => B.getD i 0)
    let R := TernaryArenaSelectedSigned.right U radix J (fun i => C.getD i 0)
    let O := TernaryArenaSelectedSigned.requester U radix J (fun i => A.getD i 0)
    let U0 := LightTernaryInitialBudgets.initial K radix n J (A.length*2^J)
    let s := run maps τ cap U V scoreBound Q I AP radix K n U0 e ℓ L R O catalogs j
    ∃i<N,LightTernaryRowSelector.Good
      (TernaryArenaPhase.family maps τ cap radix Q I AP j radix ℓ (seedAt e) L R O s catalog).flag
      (TernaryArenaPhase.family maps τ cap radix Q I AP j radix ℓ (seedAt e) L R O s catalog).scoreB
      (TernaryArenaPhase.family maps τ cap radix Q I AP j radix ℓ (seedAt e) L R O s catalog).scoreC
      ((TernaryArenaPhase.family maps τ cap radix Q I AP j radix ℓ (seedAt e) L R O s catalog).scoreP K)
      (p^(j+1)) (p^(j+1)) ((p^(2*K))^(j+1)) (9^(j+1)*n^2) (9^(j+1)*n^2)
      (U0*((9*pairFactor m F K)*(2^((fixedPi m 2)*K)))^(j+1)) i := by
  intro J I AP L R O U0 s
  have hcap : 4*U<radix^J := TernarySignedPadding.padded_length_capacity hb U _
  have hstop : LightTernaryDimensions.r (TernaryCoverScale.outputSize m) n≤AP.J :=
    (TernarySignedPadding.padded_length_proper radix U _).le
  have hp3 : 3≤p := by omega
  have hbp : radix≤p := by omega
  have hminor : (K+K).factorial*radix^(K+K)<p := by simpa only [show K+K=2*K by omega] using hdet
  obtain ⟨hsize1,hsize⟩ := field_sizes AP.J K hK hcard
  have hh := TernaryArenaSignedSelection.budget maps τ cap U V scoreBound Q I AP K n radix A.length e ℓ
    (fun i => A.getD i 0) (fun i => B.getD i 0) (fun i => C.getD i 0) catalogs
    (LightTernaryDimensions.r (TernaryCoverScale.outputSize m) n) hstop hℓ hp3 hb hp hcap
    hmeta.injectiveB hmeta.injectiveC hmeta.boundB hmeta.boundC hminor hsize1 hsize hmeta.lengthB hmeta.lengthC
  have hbudget : Budget maps τ cap Q I AP K n U0 L R O j s := hh j hj.le
  exact good maps τ cap radix Q I AP j radix K n U0 e ℓ s L R O catalog hbudget
    (hj.trans_le hstop) hℓ hp3
    (fun i t => TernaryArenaSelectedSigned.left_bound hb _ i t.val)
    (fun i t => TernaryArenaSelectedSigned.right_bound hb _ i t.val)
    (fun i t => TernaryArenaSelectedSigned.signed_nonnegative hbp (TernaryArenaSelectedSigned.left_bound hb _ i t.val))
    (fun i t => TernaryArenaSelectedSigned.signed_nonnegative hbp (TernaryArenaSelectedSigned.right_bound hb _ i t.val))
    (fun i t => TernaryArenaSelectedSigned.signed_nonnegative hbp (TernaryArenaSelectedSigned.requester_bound hb _ i t.val))
    (TernarySignedFeatureHash.left_injective (fun i : Fin B.length => B.getD i.val 0) hb hp hcap
      (fun i => hmeta.boundB i.val i.isLt) hmeta.injectiveB)
    (TernarySignedFeatureHash.right_injective (fun i : Fin C.length => C.getD i.val 0) hb hp hcap
      (fun i => hmeta.boundC i.val i.isLt) hmeta.injectiveC) hminor hsize1 hsize

theorem beta_eq (m F K : ℕ) :
    9*pairFactor m F K=9*F*(TernaryCoverScale.outputSize m)*(TernaryGoodOutputCatalog.Rbar m)^K := by
  unfold pairFactor TernaryCoverScale.outputSize TernaryGoodOutputCatalog.Rbar
  ring

/-- Cardinality of the exact found-field type in actual runtime dimensions.
This is the only scalar field identity consumed by prepared_good. -/
theorem computed_card (M radix K n U c : ℕ)
    [Fact (Irreducible (TernaryComputedExtensionMenu.modulus p
      (LightTernaryDimensions.dim M radix p K n U) c))] :
    Fintype.card (AdjoinRoot (TernaryComputedExtensionMenu.modulus p
      (LightTernaryDimensions.dim M radix p K n U) c))=
      p^(menuDegree p (LightTernaryDimensions.J M radix n U+2) K) :=
  TernaryComputedExtensionMenu.field_card

end ThreeSum.TernaryArenaPhaseBudget
