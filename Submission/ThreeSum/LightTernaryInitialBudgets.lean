import Submission.ThreeSum.LightNatPower
import Submission.ThreeSum.LightArray

namespace ThreeSum.LightTernaryInitialBudgets
open Light
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def determinantBound (K bDigit : ℕ) : ℕ :=(2*K).factorial*bDigit^(2*K)
def initial (K bDigit n J nO : ℕ) : ℕ :=
  nO*n^(2*K)*(J+2)^(2*K)*(determinantBound K bDigit)^2

def body (K bDigit a b scaleBase : ℕ) : Stmt :=
  .call 0 [v 0,k (2*K)] 5 ;;
  .call 0 [v 1 +' k 2,k (2*K)] 6 ;;
  .set 7 (v 2 *' v 5 *' v 6 *' k ((determinantBound K bDigit)^2)) ;;
  .set 8 (v 0 *' v 0) ;;
  .store (v 3 +' k 41) (k 1) ;;
  .store (v 3 +' k 42) (k 1) ;;
  .store (v 3 +' k 43) (k 1) ;;
  .store (v 3 +' k 44) (v 8) ;;
  .store (v 3 +' k 45) (v 8) ;;
  .store (v 3 +' k 46) (v 7) ;;
  .store (v 4) (k a) ;;
  .store (v 4 +' k 1) (k b) ;;
  .store (v 4 +' k 2) (k scaleBase) ;;
  .set 0 (v 7)

def program (K bDigit a b scaleBase : ℕ) : Program :=
  LightNatPower.program++[body K bDigit a b scaleBase]
def time (K : ℕ) : ℕ :=2*LightNatPower.time (2*K)+1000
def word (K bDigit a b scaleBase n J nO : ℕ) : ℕ :=
  initial K bDigit n J nO+n*n+n+J+2+nO+n^(2*K)+(J+2)^(2*K)+
    (determinantBound K bDigit)^2+a+b+scaleBase+2*K+100

/-- Initial denominators and all three thresholds are genuine program
outputs. The paired threshold uses the actual requester/carry row count. -/
theorem program_meets {lim : Limits} {K bDigit a b scaleBase n J nO seed constants d : ℕ}
    (μ : ℕ → ℤ) (hn : 1≤n) (hbDigit : 1≤bDigit)
    (hw : (lim.space : ℤ)≤lim.word) (hseed : seed+47≤constants)
    (hspace : constants+3≤lim.space)
    (hword : (word K bDigit a b scaleBase n J nO : ℤ)≤lim.word) (hd : d<lim.depth) :
    Meets lim (program K bDigit a b scaleBase) 1 d [n,J,nO,seed,constants] μ (time K)
      (fun r ν => r=(initial K bDigit n J nO : ℤ) ∧
        Seg ν (seed+41) [1,1,1,((n*n : ℕ) : ℤ),((n*n : ℕ) : ℤ),(initial K bDigit n J nO : ℤ)] ∧
        Seg ν constants [(a : ℤ),b,scaleBase] ∧
        ∀ x, (x<seed+41 ∨ seed+47≤x) → (x<constants ∨ constants+3≤x) → ν x=μ x) := by
  have hbudget (v : ℕ) (hv : v≤word K bDigit a b scaleBase n J nO) : (v : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr hv).trans hword
  have hDpos : 1≤determinantBound K bDigit := by
    have hp := Nat.mul_pos (Nat.factorial_pos (2*K)) (pow_pos (by omega : 0<bDigit) (2*K))
    exact hp
  have hDsq : 1≤(determinantBound K bDigit)^2 := Nat.one_le_pow _ _ hDpos
  have hLpow : 1≤(J+2)^(2*K) := Nat.one_le_pow _ _ (by omega)
  have hnPow : ((n^(2*K) : ℕ) : ℤ)≤lim.word := hbudget _ (by unfold word; omega)
  have hLPow : (((J+2)^(2*K) : ℕ) : ℤ)≤lim.word := hbudget _ (by unfold word; omega)
  have hJWord : ((J+2 : ℕ) : ℤ)≤lim.word := hbudget _ (by unfold word; omega)
  have heWord : ((2*K : ℕ) : ℤ)≤lim.word := hbudget _ (by unfold word; omega)
  have hnSq : ((n*n : ℕ) : ℤ)≤lim.word := hbudget _ (by unfold word; omega)
  have hinitWord : (initial K bDigit n J nO : ℤ)≤lim.word := hbudget _ (by unfold word; omega)
  have hDword : (((determinantBound K bDigit)^2 : ℕ) : ℤ)≤lim.word := hbudget _ (by unfold word; omega)
  have hNPow := LightNatPower.program_meets (d := d+1) μ heWord
    (fun i hi => (Int.ofNat_le.mpr (Nat.pow_le_pow_right hn hi)).trans hnPow)
  have h0 := hNPow.append [body K bDigit a b scaleBase]
  apply Meets.of_body (by rfl)
  unfold body time
  light_call h0 with rn μn ⟨hrn,hμn⟩
  subst μn
  have hLPowCall := (LightNatPower.program_meets (d := d+1) μ heWord
    (fun i hi => (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by omega : 1≤J+2) hi)).trans hLPow)).append
      [body K bDigit a b scaleBase]
  light_call hLPowCall with rl μl ⟨hrl,hμl⟩
  subst μl
  have hpart2 : nO*n^(2*K)*(J+2)^(2*K)≤initial K bDigit n J nO :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hpart1 : nO*n^(2*K)≤initial K bDigit n J nO :=
    (Nat.le_mul_of_pos_right _ (by omega : 0<(J+2)^(2*K))).trans hpart2
  have hpart1Z : (nO : ℤ)*(n : ℤ)^(2*K)≤lim.word := by exact_mod_cast (Int.ofNat_le.mpr hpart1).trans hinitWord
  have hpart2Z : (nO : ℤ)*(n : ℤ)^(2*K)*((J : ℤ)+2)^(2*K)≤lim.word := by exact_mod_cast (Int.ofNat_le.mpr hpart2).trans hinitWord
  have hpart3Z : (nO : ℤ)*(n : ℤ)^(2*K)*((J : ℤ)+2)^(2*K)*
      (((determinantBound K bDigit)^2 : ℕ) : ℤ)≤lim.word := by exact_mod_cast hinitWord
  have hpart1N : 0≤(nO : ℤ)*(n : ℤ)^(2*K) := by positivity
  have hpart2N : 0≤(nO : ℤ)*(n : ℤ)^(2*K)*((J : ℤ)+2)^(2*K) := by positivity
  have hpart3N : 0≤(nO : ℤ)*(n : ℤ)^(2*K)*((J : ℤ)+2)^(2*K)*
      (((determinantBound K bDigit)^2 : ℕ) : ℤ) := by positivity
  have hDwordFull : (determinantBound K bDigit : ℤ)^2≤lim.word := by exact_mod_cast hDword
  have hpart3Full : (nO : ℤ)*(n : ℤ)^(2*K)*((J : ℤ)+2)^(2*K)*
      (determinantBound K bDigit : ℤ)^2≤lim.word := by exact_mod_cast hinitWord
  have hpart3FullN : 0≤(nO : ℤ)*(n : ℤ)^(2*K)*((J : ℤ)+2)^(2*K)*
      (determinantBound K bDigit : ℤ)^2 := by positivity
  light_set (initial K bDigit n J nO : ℕ) using initial,hrn,hrl
  have hnSqN : 0≤(n : ℤ)*(n : ℤ) := by positivity
  light_set (n*n : ℕ)
  light_store (seed+41) (1 : ℕ)
  light_store (seed+42) (1 : ℕ)
  light_store (seed+43) (1 : ℕ)
  light_store (seed+44) (n*n : ℕ)
  light_store (seed+45) (n*n : ℕ)
  light_store (seed+46) (initial K bDigit n J nO : ℕ)
  have haWord := hbudget a (by unfold word; omega)
  have hbWord := hbudget b (by unfold word; omega)
  have hsWord := hbudget scaleBase (by unfold word; omega)
  light_store constants (a : ℕ)
  light_store (constants+1) (b : ℕ)
  light_store (constants+2) (scaleBase : ℕ)
  light_set (initial K bDigit n J nO : ℕ)
  refine ⟨by simp,?_,?_,?_⟩
  · simp [seg_cons,Function.update_apply]
    omega
  · simp [seg_cons,Function.update_apply]
  · intro x hx hy
    dsimp only [State.mem]
    repeat rw [Function.update_of_ne (by omega)]

end ThreeSum.LightTernaryInitialBudgets
