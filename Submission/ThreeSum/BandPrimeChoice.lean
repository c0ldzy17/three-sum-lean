import Submission.ThreeSum.BandWeightedScore

/-!
# A common contracting modulus for the complete band-owner catalog

The same deterministic first-minimum rule is applied to the sum of every
flagged owner's score. These are joint choices for all bands, rather than
independent moduli whose contractions could not be combined.
-/

namespace ThreeSum.BandPrimeChoice

open BandCandidateRows BandWeightedScore Finset
open scoped BigOperators

set_option maxHeartbeats 1400000
set_option maxRecDepth 8000

def candidateScore (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) (i : ℕ) : ℤ :=
  (score primes s (q*primes i) nA nB nC g A B C rs : ℤ)

def chosenIndex (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) : ℕ :=
  LightMinimum.least (candidateScore primes s q nA nB nC g A B C rs) s

def chosenPrime (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) : ℕ :=
  primes (chosenIndex primes s q nA nB nC g A B C rs)

theorem chosenIndex_lt (primes : ℕ → ℕ) {s q nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List Record) (hs : 0 < s) :
    chosenIndex primes s q nA nB nC g A B C rs < s := LightMinimum.least_lt _ hs

theorem chosenPrime_min (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) {i : ℕ} (hi : i < s) :
    score primes s (q*chosenPrime primes s q nA nB nC g A B C rs) nA nB nC g A B C rs ≤
      score primes s (q*primes i) nA nB nC g A B C rs := by
  have hh := LightMinimum.least_value_le (candidateScore primes s q nA nB nC g A B C rs) s i hi
  dsimp only [candidateScore] at hh
  exact_mod_cast hh

theorem chosenPrime_contracts (primes : ℕ → ℕ) (s q nA nB nC g y U : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) (hy : 1 < y)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j)
    (hlo : ∀ i < s, y ≤ primes i)
    (hA : ∀ i < nA, |A i| ≤ (U : ℤ)) (hB : ∀ i < nB, |B i| ≤ (U : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (U : ℤ)) :
    s*score primes s (q*chosenPrime primes s q nA nB nC g A B C rs) nA nB nC g A B C rs ≤
      Nat.log y (3*U)*score primes s q nA nB nC g A B C rs := by
  calc
    _ = ∑ _i ∈ range s,
        score primes s (q*chosenPrime primes s q nA nB nC g A B C rs) nA nB nC g A B C rs := by simp
    _ ≤ ∑ i ∈ range s, score primes s (q*primes i) nA nB nC g A B C rs :=
      sum_le_sum fun i hi => chosenPrime_min primes s q nA nB nC g A B C rs (mem_range.mp hi)
    _ ≤ _ := sum_scores_le_log primes s q nA nB nC g y U A B C rs hy hprime hinj hlo hA hB hC

def modulus (primes : ℕ → ℕ) (s nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) : ℕ → ℕ
  | 0 => 1
  | r+1 =>
    let q := modulus primes s nA nB nC g A B C rs r
    q*chosenPrime primes s q nA nB nC g A B C rs

theorem modulus_bounds (primes : ℕ → ℕ) {s nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List Record) (hs : 0 < s) (y Y r : ℕ)
    (hlo : ∀ i < s, y ≤ primes i) (hhi : ∀ i < s, primes i ≤ Y) :
    y^r ≤ modulus primes s nA nB nC g A B C rs r ∧
      modulus primes s nA nB nC g A B C rs r ≤ Y^r := by
  induction r with
  | zero => simp [modulus]
  | succ r ih =>
    have hidx := chosenIndex_lt (q := modulus primes s nA nB nC g A B C rs r)
      (nA := nA) (nB := nB) (nC := nC) (g := g) primes A B C rs hs
    constructor
    · simpa only [modulus,pow_succ,chosenPrime] using Nat.mul_le_mul ih.1 (hlo _ hidx)
    · simpa only [modulus,pow_succ,chosenPrime] using Nat.mul_le_mul ih.2 (hhi _ hidx)

theorem modulus_pos (primes : ℕ → ℕ) {s nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List Record) (hs : 0 < s)
    (hprime : ∀ i < s, Nat.Prime (primes i)) (r : ℕ) :
    0 < modulus primes s nA nB nC g A B C rs r := by
  have hh := (modulus_bounds (nA := nA) (nB := nB) (nC := nC) (g := g) primes A B C rs hs 1
    (Finset.sup (range s) primes) r
    (fun i hi => (hprime i hi).pos)
    (fun i hi => Finset.le_sup (mem_range.mpr hi))).1
  rw [one_pow] at hh
  omega

theorem modulus_score_bound (primes : ℕ → ℕ) (s nA nB nC g y U r : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) (hy : 1 < y)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j)
    (hlo : ∀ i < s, y ≤ primes i)
    (hA : ∀ i < nA, |A i| ≤ (U : ℤ)) (hB : ∀ i < nB, |B i| ≤ (U : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (U : ℤ)) :
    s^r*score primes s (modulus primes s nA nB nC g A B C rs r) nA nB nC g A B C rs ≤
      (Nat.log y (3*U))^r*score primes s 1 nA nB nC g A B C rs := by
  induction r with
  | zero => simp [modulus]
  | succ r ih =>
    let q := modulus primes s nA nB nC g A B C rs r
    have hs := chosenPrime_contracts primes s q nA nB nC g y U A B C rs hy hprime hinj hlo hA hB hC
    calc
      _ = s^r*(s*score primes s
          (q*chosenPrime primes s q nA nB nC g A B C rs) nA nB nC g A B C rs) := by
        simp only [modulus,q,pow_succ]
        ring
      _ ≤ s^r*(Nat.log y (3*U)*score primes s q nA nB nC g A B C rs) := Nat.mul_le_mul_left _ hs
      _ = Nat.log y (3*U)*(s^r*score primes s q nA nB nC g A B C rs) := by ring
      _ ≤ Nat.log y (3*U)*((Nat.log y (3*U))^r*score primes s 1 nA nB nC g A B C rs) :=
        Nat.mul_le_mul_left _ ih
      _ = _ := by ring

theorem modulus_initial_bound (primes : ℕ → ℕ) (s nA nB nC g y U r : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) (hy : 1 < y)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j)
    (hlo : ∀ i < s, y ≤ primes i)
    (hA : ∀ i < nA, |A i| ≤ (U : ℤ)) (hB : ∀ i < nB, |B i| ≤ (U : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (U : ℤ)) :
    s^r*score primes s (modulus primes s nA nB nC g A B C rs r) nA nB nC g A B C rs ≤
      (Nat.log y (3*U))^r*(rs.length*(s*g^3)) :=
  (modulus_score_bound primes s nA nB nC g y U r A B C rs hy hprime hinj hlo hA hB hC).trans
    (Nat.mul_le_mul_left _ (score_bound primes s 1 nA nB nC g A B C rs hprime hinj))

theorem chosenPrime_congr {primes : ℕ → ℕ} {s q nA nB nC g : ℕ}
    {A A' B B' C C' : ℕ → ℤ} (rs : List Record)
    (hA : ∀ i < nA, A i=A' i) (hB : ∀ i < nB, B i=B' i) (hC : ∀ i < nC, C i=C' i) :
    chosenPrime primes s q nA nB nC g A B C rs=chosenPrime primes s q nA nB nC g A' B' C' rs := by
  have hf : candidateScore primes s q nA nB nC g A B C rs=
      candidateScore primes s q nA nB nC g A' B' C' rs := by
    funext i
    unfold candidateScore
    rw [score_congr rs hA hB hC]
  simp only [chosenPrime,chosenIndex,hf]

theorem modulus_congr {primes : ℕ → ℕ} {s nA nB nC g : ℕ}
    {A A' B B' C C' : ℕ → ℤ} (rs : List Record)
    (hA : ∀ i < nA, A i=A' i) (hB : ∀ i < nB, B i=B' i) (hC : ∀ i < nC, C i=C' i) (r : ℕ) :
    modulus primes s nA nB nC g A B C rs r=modulus primes s nA nB nC g A' B' C' rs r := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [modulus,ih,chosenPrime_congr rs hA hB hC]

end ThreeSum.BandPrimeChoice
