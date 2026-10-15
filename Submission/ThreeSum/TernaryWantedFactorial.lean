import Submission.ThreeSum.TernaryConvolution
import Submission.ThreeSum.TernaryBankEnumeration

noncomputable section
namespace ThreeSum.TernaryWantedFactorial
open TernaryJointType
set_option maxHeartbeats 1000000

def listFactorial (xs : List ℕ) : ℤ := (xs.map fun d => (d.factorial : ℤ)).prod

theorem listFactorial_append (xs ys : List ℕ) :
    listFactorial (xs++ys)=listFactorial xs*listFactorial ys := by
  simp [listFactorial]

theorem listFactorial_word {L : ℕ} (w : TritWord L) :
    listFactorial (TernaryBankEnumeration.wordList w)=TernaryConvolution.factorial w := by
  simp [listFactorial,TernaryBankEnumeration.wordList,TernaryConvolution.factorial,
    Fin.prod_ofFn,Function.comp_def]

theorem typed_blocks_factorial {L : ℕ} (π : DigitType) (qs : List (TritWord L))
    (hq : ∀ q∈qs, HasType q π) :
    listFactorial (qs.flatMap TernaryBankEnumeration.wordList)=(2 : ℤ)^(qs.length*π 2) := by
  induction qs with
  | nil => simp [listFactorial]
  | cons q qs ih =>
    have hq0 := hq q (by simp)
    have hqs : ∀ q∈qs, HasType q π := by intro r hr; exact hq r (by simp [hr])
    simp only [List.flatMap_cons,listFactorial_append,listFactorial_word,
      TernaryConvolution.factorial_eq_power_two,hq0 2,ih hqs,List.length_cons]
    rw [Nat.add_mul,one_mul,pow_add]
    ring

theorem factorial_of_canonical_blocks {N L : ℕ} (Q : TritWord N) (π : DigitType)
    (qs : List (TritWord L)) (hq : ∀ q∈qs, HasType q π)
    (hword : TernaryBankEnumeration.wordList Q=qs.reverse.flatMap TernaryBankEnumeration.wordList) :
    TernaryConvolution.factorial Q=(2 : ℤ)^(qs.length*π 2) := by
  rw [← listFactorial_word,hword]
  have hh := typed_blocks_factorial π qs.reverse (by
    intro q hq'; exact hq q (List.mem_reverse.mp hq'))
  simpa using hh

end ThreeSum.TernaryWantedFactorial
