import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Basic
import Lean.Elab.Tactic.Omega

/-!
# Executable binary search with a comparison budget

`upperSearch` finds the first array entry strictly above a query.  Its fuel is
logarithmic, and the proof accounts for the actual branches taken.  Array
accesses here are explicit function calls; a machine realization must still
implement those calls by bounded-address loads.
-/

namespace ThreeSum.BinarySearch

def upperSearch (f : ℕ → ℤ) (x : ℤ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := (lo + hi) / 2
        if f mid ≤ x then upperSearch f x fuel (mid + 1) hi
        else upperSearch f x fuel lo mid
      else lo

def comparisons (f : ℕ → ℤ) (x : ℤ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := (lo + hi) / 2
        1 + if f mid ≤ x then comparisons f x fuel (mid + 1) hi
            else comparisons f x fuel lo mid
      else 0

theorem comparisons_le (f : ℕ → ℤ) (x : ℤ) (fuel lo hi : ℕ) :
    comparisons f x fuel lo hi ≤ fuel := by
  induction fuel generalizing lo hi with
  | zero => simp [comparisons]
  | succ fuel ih =>
      simp only [comparisons]
      split
      · split
        · have h := ih ((lo + hi) / 2 + 1) hi
          omega
        · have h := ih lo ((lo + hi) / 2)
          omega
      · omega

def Partition (f : ℕ → ℤ) (x : ℤ) (n k : ℕ) : Prop :=
  k ≤ n ∧ (∀ i < k, f i ≤ x) ∧ (∀ i, k ≤ i → i < n → x < f i)

theorem upperSearch_correct (f : ℕ → ℤ) (x : ℤ) (n fuel lo hi : ℕ)
    (hsorted : ∀ i j, i ≤ j → j < n → f i ≤ f j)
    (hlo : lo ≤ hi) (hhi : hi ≤ n) (hwidth : hi - lo < 2 ^ fuel)
    (hlower : ∀ i < lo, f i ≤ x)
    (hupper : ∀ i, hi ≤ i → i < n → x < f i) :
    Partition f x n (upperSearch f x fuel lo hi) := by
  induction fuel generalizing lo hi with
  | zero =>
      have heq : lo = hi := by simp only [Nat.pow_zero] at hwidth; omega
      simpa only [Partition, upperSearch, heq] using And.intro hhi (And.intro (heq ▸ hlower) hupper)
  | succ fuel ih =>
      rw [upperSearch]
      split
      · rename_i hlt
        dsimp only
        let mid := (lo + hi) / 2
        have hmidlo : lo ≤ mid := by dsimp [mid]; omega
        have hmidhi : mid < hi := by dsimp [mid]; omega
        have hpow : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by
          rw [Nat.pow_succ, Nat.mul_comm]
        rw [hpow] at hwidth
        by_cases htest : f mid ≤ x
        · rw [if_pos htest]
          apply ih (mid + 1) hi (by omega) hhi
          · dsimp [mid] at *; omega
          · intro i hi'
            exact le_trans (hsorted i mid (by omega) (by omega)) htest
          · exact hupper
        · rw [if_neg htest]
          apply ih lo mid hmidlo (by omega)
          · dsimp [mid] at *; omega
          · exact hlower
          · intro i hmi hin
            exact lt_of_lt_of_le (by omega : x < f mid) (hsorted mid i hmi hin)
      · rename_i hstop
        have heq : lo = hi := by omega
        simpa only [Partition, heq] using And.intro hhi (And.intro (heq ▸ hlower) hupper)

def upperBound (f : ℕ → ℤ) (n : ℕ) (x : ℤ) : ℕ :=
  upperSearch f x (Nat.log 2 n + 1) 0 n

theorem upperBound_correct (f : ℕ → ℤ) (n : ℕ) (x : ℤ)
    (hsorted : ∀ i j, i ≤ j → j < n → f i ≤ f j) :
    Partition f x n (upperBound f n x) := by
  apply upperSearch_correct f x n (Nat.log 2 n + 1) 0 n hsorted (by omega) (by omega)
  · simpa only [Nat.sub_zero] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  · intro i hi; omega
  · intro i hi hin; omega

theorem upperBound_comparisons (f : ℕ → ℤ) (n : ℕ) (x : ℤ) :
    comparisons f x (Nat.log 2 n + 1) 0 n ≤ Nat.log 2 n + 1 :=
  comparisons_le f x _ _ _

/-- Return the interval containing `x`, with no scan through earlier bands. -/
def locate (lo hi : ℕ → ℤ) (n : ℕ) (x : ℤ) : Option ℕ :=
  let k := upperBound lo n x
  if 0 < k then
    if x ≤ hi (k - 1) then some (k - 1) else none
  else none

theorem locate_sound (lo hi : ℕ → ℤ) (n : ℕ) (x : ℤ)
    (hsorted : ∀ i j, i ≤ j → j < n → lo i ≤ lo j)
    {i : ℕ} (h : locate lo hi n x = some i) :
    i < n ∧ lo i ≤ x ∧ x ≤ hi i := by
  have hp := upperBound_correct lo n x hsorted
  rcases hp with ⟨hkn, hpre, hpost⟩
  unfold locate at h
  dsimp only at h
  split at h
  · rename_i hk
    split at h
    · rename_i hxh
      have heq : upperBound lo n x - 1 = i := Option.some.inj h
      subst i
      exact ⟨by omega, hpre _ (by omega), hxh⟩
    · cases h
  · cases h

theorem locate_complete (lo hi : ℕ → ℤ) (n : ℕ) (x : ℤ)
    (hsorted : ∀ i j, i ≤ j → j < n → lo i ≤ lo j)
    (hseparated : ∀ i j, i < j → j < n → hi i < lo j)
    {i : ℕ} (hin : i < n) (hil : lo i ≤ x) (hih : x ≤ hi i) :
    locate lo hi n x = some i := by
  have hp := upperBound_correct lo n x hsorted
  rcases hp with ⟨hkn, hpre, hpost⟩
  have hik : i < upperBound lo n x := by
    by_contra hh
    have hh' := hpost i (by omega) hin
    omega
  have heq : upperBound lo n x = i + 1 := by
    by_contra hh
    have hnext : i + 1 < upperBound lo n x := by omega
    have hnl := hpre (i + 1) hnext
    have hnh := hseparated i (i + 1) (by omega) (by omega)
    omega
  simp [locate, heq, hih]

end ThreeSum.BinarySearch
