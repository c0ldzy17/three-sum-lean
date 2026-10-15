import Submission.ThreeSum.TernaryArenaPrefixPotential
import Submission.ThreeSum.TernaryPairedInitialBudget

noncomputable section
namespace ThreeSum.TernaryArenaPrefixInitial
open Finset TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps TernaryCoverLocal
open TernaryArenaSourceSetup TernaryArenaPrefixGroups TernaryArenaPrefixPairs TernaryArenaPrefixPotential
open TernaryPairedPotential TernaryPairedContraction
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
variable {p m F Λ : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input) (L R : ℕ→Fin Λ→ℤ)
    (row : ℕ→(Fin Λ→ZMod p)→ₗ[ZMod p] ZMod p) (root : ℕ→ℕ→ZMod p)
    (Q : TernaryGoodOutputCatalog.Output m)

theorem initial_index_card (K : ℕ) :
    Fintype.card ((M maps τ cap I L R row root).Index 0 K)≤I.requesterCount*(I.nB*I.nC)^K := by
  let M := M maps τ cap I L R row root
  have hG : Fintype.card (M.Group 0)≤I.requesterCount := by
    have hh := Fintype.card_le_of_injective (fun g : M.Group 0 => g.val.1) (by
      intro g h he
      apply Subtype.ext
      exact Prod.ext he (funext (fun i => Fin.elim0 i)))
    simpa using hh
  have hP (g : M.Group 0) : Fintype.card (M.Pair g)≤I.nB*I.nC := by
    have hh := Fintype.card_le_of_injective (fun x : M.Pair g => x.val.1) (by
      intro x y he
      apply Subtype.ext
      exact Prod.ext he (funext (fun i => Fin.elim0 i)))
    simpa using hh
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _g : M.Group 0, (I.nB*I.nC)^K := by
      apply sum_le_sum
      intro g hg
      simpa using Nat.pow_le_pow_left (hP g) K
    _ = Fintype.card (M.Group 0)*(I.nB*I.nC)^K := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hG

theorem initial_bound (K b : ℕ) (hL : ∀ i j, (L i j).natAbs≤b) (hR : ∀ i j, (R i j).natAbs≤b) :
    value maps τ cap I L R row root Q 0 K≤
      I.requesterCount*(I.nB*I.nC)^K*Λ^(K+K)*((K+K).factorial*b^(K+K))^2 := by
  rw [value_eq_model]
  have hm (x : (M maps τ cap I L R row root).Index 0 K) :
      minorWeight ((M maps τ cap I L R row root).matrix x)≤Λ^(K+K)*((K+K).factorial*b^(K+K))^2 := by
    apply minorWeight_le _ b
    intro i j
    unfold TernaryNativePrefixLineage.Model.matrix
    cases finSumFinEquiv.symm i with
    | inl k => exact hL _ _
    | inr k => exact hR _ _
  unfold potential
  calc
    _ ≤ ∑ _x : (M maps τ cap I L R row root).Index 0 K, Λ^(K+K)*((K+K).factorial*b^(K+K))^2 :=
      sum_le_sum (fun x hx => hm x)
    _ = Fintype.card ((M maps τ cap I L R row root).Index 0 K)*
        (Λ^(K+K)*((K+K).factorial*b^(K+K))^2) := by simp
    _ ≤ (I.requesterCount*(I.nB*I.nC)^K)*(Λ^(K+K)*((K+K).factorial*b^(K+K))^2) :=
      Nat.mul_le_mul_right _ (initial_index_card maps τ cap I L R row root K)
    _ = _ := by ring

theorem actual_initializer_bound (K b n : ℕ)
    (hL : ∀ i j, (L i j).natAbs≤b) (hR : ∀ i j, (R i j).natAbs≤b)
    (hB : I.nB≤n) (hC : I.nC≤n) :
    value maps τ cap I L R row root Q 0 K≤
      I.requesterCount*n^(2*K)*Λ^(2*K)*((2*K).factorial*b^(2*K))^2 := by
  have hh := initial_bound maps τ cap I L R row root Q K b hL hR
  have hc : (I.nB*I.nC)^K≤n^(2*K) := by
    calc
      _ ≤ (n*n)^K := Nat.pow_le_pow_left (Nat.mul_le_mul hB hC) K
      _ = _ := by rw [←pow_two,←pow_mul]
  have he : K+K=2*K := by omega
  rw [he] at hh
  exact hh.trans (by gcongr)

end ThreeSum.TernaryArenaPrefixInitial
