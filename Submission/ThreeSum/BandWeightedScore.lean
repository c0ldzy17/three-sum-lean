import Submission.ThreeSum.BandCandidateRows
import Submission.ThreeSum.BandPartition
import Submission.ThreeSum.LightPrimeChain

/-!
# The aggregate weighted score of physical band-owner candidates

Each flagged owner contributes the score of its three actual truncated
bands. Owner multiplicities are retained. The contraction and initial bound
therefore apply to the same quadratic catalog that the program scans.
-/

namespace ThreeSum.BandWeightedScore

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

def length (n g a : ℕ) : ℕ := min g (n-a*g)

theorem length_le (n g a : ℕ) : length n g a ≤ g := min_le_left _ _

theorem length_eq_partition (n g a : ℕ) :
    length n g a=BandPartition.stop n g a-BandPartition.start g a := by
  unfold length BandPartition.stop BandPartition.start
  rw [Nat.add_mul,Nat.one_mul]
  omega

theorem position_lt {n g a i : ℕ} (hi : i < length n g a) : a*g+i < n := by
  have hh := min_le_right g (n-a*g)
  unfold length at hi
  omega

theorem end_le {n g a : ℕ} (ha : a*g ≤ n) : a*g+length n g a ≤ n := by
  have hh := min_le_right g (n-a*g)
  unfold length
  omega

def block (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (r : Record) : ℕ :=
  if r.flag=1 then
    WeightedScore.score primes s q (length nA g r.a) (length nB g r.b) (length nC g r.c)
      (fun i => A (r.a*g+i)) (fun i => B (r.b*g+i)) (fun i => C (r.c*g+i))
  else 0

def partialScore (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) (k : ℕ) : ℕ :=
  ∑ i ∈ range k, block primes s q nA nB nC g A B C (rs.getD i default)

def score (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) : ℕ :=
  partialScore primes s q nA nB nC g A B C rs rs.length

@[simp] theorem partialScore_zero (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) : partialScore primes s q nA nB nC g A B C rs 0=0 := by
  simp [partialScore]

theorem partialScore_succ (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) (k : ℕ) :
    partialScore primes s q nA nB nC g A B C rs (k+1)=
      partialScore primes s q nA nB nC g A B C rs k+
        block primes s q nA nB nC g A B C (rs.getD k default) := sum_range_succ _ _

theorem block_bound (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (r : Record)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j) :
    block primes s q nA nB nC g A B C r ≤ s*g^3 := by
  unfold block
  split_ifs
  · rw [WeightedScore.score_eq_remaining _ _ _ _ _ _ _ _ _ hprime hinj]
    have hh := WeightedScore.remaining_le primes s q (length nA g r.a)
      (length nB g r.b) (length nC g r.c)
      (fun i => A (r.a*g+i)) (fun i => B (r.b*g+i)) (fun i => C (r.c*g+i)) s
    have hp : length nA g r.a*length nB g r.b*length nC g r.c ≤ g^3 := by
      calc
        _ ≤ g*g*g := Nat.mul_le_mul (Nat.mul_le_mul (length_le ..) (length_le ..)) (length_le ..)
        _ = _ := by ring
    exact hh.trans (Nat.mul_le_mul_left s hp)
  · omega

theorem partialScore_bound (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) (k : ℕ)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j) :
    partialScore primes s q nA nB nC g A B C rs k ≤ k*(s*g^3) := by
  calc
    _ ≤ ∑ _i ∈ range k, s*g^3 := sum_le_sum fun i _ => block_bound primes s q nA nB nC g A B C _ hprime hinj
    _ = _ := by simp

theorem score_bound (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j) :
    score primes s q nA nB nC g A B C rs ≤ rs.length*(s*g^3) :=
  partialScore_bound primes s q nA nB nC g A B C rs rs.length hprime hinj

theorem block_congr {primes : ℕ → ℕ} {s q nA nB nC g : ℕ}
    {A A' B B' C C' : ℕ → ℤ} (r : Record)
    (hA : ∀ i < nA, A i=A' i) (hB : ∀ i < nB, B i=B' i) (hC : ∀ i < nC, C i=C' i) :
    block primes s q nA nB nC g A B C r=block primes s q nA nB nC g A' B' C' r := by
  unfold block
  split_ifs
  · exact LightPrimeMinimum.score_congr
      (fun i hi => hA _ (position_lt hi)) (fun i hi => hB _ (position_lt hi))
      (fun i hi => hC _ (position_lt hi))
  · rfl

theorem score_congr {primes : ℕ → ℕ} {s q nA nB nC g : ℕ}
    {A A' B B' C C' : ℕ → ℤ} (rs : List Record)
    (hA : ∀ i < nA, A i=A' i) (hB : ∀ i < nB, B i=B' i) (hC : ∀ i < nC, C i=C' i) :
    score primes s q nA nB nC g A B C rs=score primes s q nA nB nC g A' B' C' rs := by
  unfold score partialScore
  exact sum_congr rfl fun i _ => block_congr (rs.getD i default) hA hB hC

theorem sum_blocks_le_log (primes : ℕ → ℕ) (s q nA nB nC g y U : ℕ)
    (A B C : ℕ → ℤ) (r : Record) (hy : 1 < y)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j)
    (hlo : ∀ i < s, y ≤ primes i)
    (hA : ∀ i < nA, |A i| ≤ (U : ℤ)) (hB : ∀ i < nB, |B i| ≤ (U : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (U : ℤ)) :
    (∑ i ∈ range s, block primes s (q*primes i) nA nB nC g A B C r) ≤
      Nat.log y (3*U)*block primes s q nA nB nC g A B C r := by
  unfold block
  by_cases hf : r.flag=1
  · simp only [if_pos hf]
    exact LightPrimeChain.sum_scores_le_log primes s q _ _ _ _ _ _ y (3*U) hy hprime hinj hlo
      (LightPrimeChain.difference_bound (fun i hi => hA _ (position_lt hi))
        (fun i hi => hB _ (position_lt hi)) (fun i hi => hC _ (position_lt hi)))
  · simp [hf]

theorem sum_scores_le_log (primes : ℕ → ℕ) (s q nA nB nC g y U : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) (hy : 1 < y)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j)
    (hlo : ∀ i < s, y ≤ primes i)
    (hA : ∀ i < nA, |A i| ≤ (U : ℤ)) (hB : ∀ i < nB, |B i| ≤ (U : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (U : ℤ)) :
    (∑ i ∈ range s, score primes s (q*primes i) nA nB nC g A B C rs) ≤
      Nat.log y (3*U)*score primes s q nA nB nC g A B C rs := by
  unfold score partialScore
  rw [sum_comm,mul_sum]
  exact sum_le_sum fun i _ => sum_blocks_le_log primes s q nA nB nC g y U A B C _
    hy hprime hinj hlo hA hB hC

end ThreeSum.BandWeightedScore
