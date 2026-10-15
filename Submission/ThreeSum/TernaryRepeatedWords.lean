import Submission.ThreeSum.TernaryWantedFactorial
import Submission.ThreeSum.TernaryNativeCoverWitness

noncomputable section
namespace ThreeSum.TernaryRepeatedWords
open TernaryJointType Finset
open scoped BigOperators
set_option maxHeartbeats 3000000

def word {r L : ℕ} (blocks : Fin r → TritWord L) : TritWord (r*L) :=
  fun i => blocks (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

theorem word_at {r L : ℕ} (blocks : Fin r → TritWord L) (i : Fin r) (j : Fin L) :
    word blocks (finProdFinEquiv (i,j))=blocks i j := by
  simp [word]

theorem typed {r L : ℕ} (blocks : Fin r → TritWord L) (π : DigitType)
    (h : ∀ i, HasType (blocks i) π) : HasType (word blocks) (fun d => r*π d) := by
  intro d
  unfold digitCount
  calc
    _ = ∑ ij : Fin r × Fin L, if blocks ij.1 ij.2=d then 1 else 0 := by
      simpa only [word,Equiv.symm_apply_apply] using
        (Equiv.sum_comp finProdFinEquiv (fun i : Fin (r*L) => if word blocks i=d then (1 : ℕ) else 0)).symm
    _ = ∑ i : Fin r, digitCount (blocks i) d := by rw [Fintype.sum_prod_type]; rfl
    _ = ∑ _i : Fin r, π d := sum_congr rfl (fun i _ => h i d)
    _ = _ := by simp

theorem adds {r L : ℕ} (a b q : Fin r → TritWord L)
    (h : ∀ i, PointwiseSum (a i) (b i) (q i)) : PointwiseSum (word a) (word b) (word q) := by
  intro i
  exact h (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

theorem wordList {r L : ℕ} (blocks : Fin r → TritWord L) :
    TernaryBankEnumeration.wordList (word blocks)=
      (List.ofFn (fun i => TernaryBankEnumeration.wordList (blocks i))).flatten := by
  unfold TernaryBankEnumeration.wordList
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply List.ofFn_inj.mpr
  funext i
  apply List.ofFn_inj.mpr
  funext j
  simpa only [finProdFinEquiv,Equiv.coe_fn_mk,Nat.add_comm,Nat.mul_comm] using
    congrArg Fin.val (word_at blocks i j)

/-- Canonical little-endian tuple codes reverse block order in physical word
addresses. Reversal does not change the exact repeated digit type. -/
def canonical {r L : ℕ} (blocks : Fin r → TritWord L) : TritWord (r*L) :=
  word (fun i => blocks i.rev)


theorem ofFn_rev {A : Type*} {r : ℕ} (f : Fin r → A) :
    List.ofFn (fun i => f i.rev)=(List.ofFn f).reverse := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp only [List.getElem_ofFn,List.getElem_reverse] 
  congr 1
  apply Fin.ext
  simp [Fin.rev]
  omega

theorem canonical_wordList {r L : ℕ} (blocks : Fin r → TritWord L) :
    TernaryBankEnumeration.wordList (canonical blocks)=
      (List.ofFn blocks).reverse.flatMap TernaryBankEnumeration.wordList := by
  rw [canonical,wordList]
  simp only [List.flatMap,List.map_reverse,List.map_ofFn]
  exact congrArg List.flatten (ofFn_rev (fun i => TernaryBankEnumeration.wordList (blocks i)))

theorem canonical_typed {r L : ℕ} (blocks : Fin r → TritWord L) (π : DigitType)
    (h : ∀ i, HasType (blocks i) π) : HasType (canonical blocks) (fun d => r*π d) :=
  typed _ π (fun i => h i.rev)

theorem canonical_adds {r L : ℕ} (a b q : Fin r → TritWord L)
    (h : ∀ i, PointwiseSum (a i) (b i) (q i)) :
    PointwiseSum (canonical a) (canonical b) (canonical q) :=
  adds _ _ _ (fun i => h i.rev)

theorem canonical_factorial {r L : ℕ} (blocks : Fin r → TritWord L) (π : DigitType)
    (h : ∀ i, HasType (blocks i) π) :
    TernaryConvolution.factorial (canonical blocks)=(2 : ℤ)^(r*π 2) := by
  rw [TernaryConvolution.factorial_eq_power_two,canonical_typed blocks π h 2]

end ThreeSum.TernaryRepeatedWords
