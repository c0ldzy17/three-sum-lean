import Submission.ThreeSum.LightBandPrimeConstruction
import Submission.ThreeSum.BandRawAScore
import Submission.ThreeSum.ArithmeticStageBounds

/-!
# Finite scale guarantees for the executed physical-owner modulus

These theorems instantiate the previously proved size-only mass bounds with
the common modulus actually constructed from the candidate record array.
The weighted count is over physical A incidences and their own B/C bands.
-/

namespace ThreeSum.BandPrimeScales

open BandCandidateRows Scales BandScales CostLedger

set_option maxHeartbeats 1600000
set_option maxRecDepth 9000

def modulus (n nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List Record) : ℕ :=
  LightBandPrimeConstruction.modulus (primeWindow n) nA nB nC (bandSize n)
    A B C rs (primeDepth radix n)

def score (n q nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List Record) : ℕ :=
  BandWeightedScore.score (LightPrimePool.prime (primeWindow n))
    (LightPrimePool.size (primeWindow n)) q nA nB nC (bandSize n) A B C rs

def physicalMass (n q nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List Record) : ℕ :=
  Arithmetic.weightedFalseCount (BandRawA.allProducts nA nB nC (bandSize n) rs)
    (ModuloCounts.difference (BandRawA.valueAt nA (bandSize n) rs A) B C)
    (Auxiliary.moduli (WeightedScore.auxiliarySet (LightPrimePool.prime (primeWindow n))
      (LightPrimePool.size (primeWindow n)))) q

theorem physicalMass_eq_score (n q nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List Record) :
    physicalMass n q nA nB nC A B C rs=score n q nA nB nC A B C rs :=
  BandRawA.all_weightedFalseCount _ _ _ _ _ _ _ _ _ _ _

theorem modulus_bounds (n nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List Record) :
    primeWindow n^primeDepth radix n ≤ modulus n nA nB nC A B C rs ∧
      modulus n nA nB nC A B C rs ≤ (4*primeWindow n)^primeDepth radix n :=
  LightBandPrimeConstruction.modulus_bounds A B C rs _ (by have := primeWindow_ge_two n; omega)

/-- The integer guard used by the three-lift residue construction. -/
theorem modulus_guard {n nA nB nC : ℕ} (A B C : ℕ → ℤ) (rs : List Record)
    (hR : 4 ≤ radix n) : 4*modulus n nA nB nC A B C rs ≤ radix n :=
  (Nat.mul_le_mul_left 4 (modulus_bounds n nA nB nC A B C rs).2).trans
    (primeDepth_upper radix hR)

theorem modulus_loss (n nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List Record) :
    radix n ≤ primeLoss radix n*modulus n nA nB nC A B C rs :=
  primeDepth_loss_bound radix (modulus_bounds n nA nB nC A B C rs).1

/-- Every candidate and auxiliary product fits the existing arithmetic cap. -/
theorem resource_modulus_bound {n : ℕ} (hR : 4 ≤ radix n) :
    (4*primeWindow n)^(primeDepth radix n+1) ≤ ArithmeticStageBounds.maxMod n := by
  have hh := primeDepth_upper radix hR
  have hp : (4*primeWindow n)^primeDepth radix n ≤ radix n := by omega
  rw [pow_succ]
  exact Nat.mul_le_mul hp (Nat.le_self_pow (by decide : (2 : ℕ) ≠ 0) _)

theorem score_contraction {k n nA nB nC : ℕ} (A B C : ℕ → ℤ) (rs : List Record)
    (hA : ∀ i < nA, |A i| ≤ (n^k : ℤ))
    (hB : ∀ i < nB, |B i| ≤ (n^k : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (n^k : ℤ)) :
    candidateCount n^primeDepth radix n * score n (modulus n nA nB nC A B C rs) nA nB nC A B C rs ≤
      divisorBudget k n^primeDepth radix n * score n 1 nA nB nC A B C rs := by
  have hh := LightBandPrimeConstruction.modulus_score_bound (y := primeWindow n)
    (g := bandSize n) (U := n^k) A B C rs (primeDepth radix n)
    (by have := primeWindow_ge_two n; omega)
    (by simpa only [Nat.cast_pow] using hA)
    (by simpa only [Nat.cast_pow] using hB)
    (by simpa only [Nat.cast_pow] using hC)
  simpa only [LightPrimePool.size_eq_card,candidateCount,divisorBudget,score,modulus] using hh

theorem initial_score_bound {n nA nB nC : ℕ} (A B C : ℕ → ℤ) (rs : List Record)
    (hcount : rs.length ≤ 3*bandCount n^2) :
    score n 1 nA nB nC A B C rs ≤ candidateCount n*MassScales.rawTripleBound n := by
  have hh := BandWeightedScore.score_bound (LightPrimePool.prime (primeWindow n))
    (LightPrimePool.size (primeWindow n)) 1 nA nB nC (bandSize n) A B C rs
    (fun _ hi => (LightPrimePool.prime_spec hi).1)
    (fun _ hi _ hj heq => LightPrimePool.prime_injective hi hj heq)
  calc
    _ ≤ rs.length*(LightPrimePool.size (primeWindow n)*bandSize n^3) := hh
    _ ≤ (3*bandCount n^2)*(LightPrimePool.size (primeWindow n)*bandSize n^3) :=
      Nat.mul_le_mul_right _ hcount
    _ = _ := by rw [LightPrimePool.size_eq_card]; unfold candidateCount MassScales.rawTripleBound; ring

theorem score_loss {k n nA nB nC : ℕ} (A B C : ℕ → ℤ) (rs : List Record)
    (hbudget : divisorBudget k n*primeWindow n ≤
      candidateCount n*(4*(k+2)*(inputBits n+1)))
    (hA : ∀ i < nA, |A i| ≤ (n^k : ℤ))
    (hB : ∀ i < nB, |B i| ≤ (n^k : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (n^k : ℤ)) :
    modulus n nA nB nC A B C rs*score n (modulus n nA nB nC A B C rs) nA nB nC A B C rs ≤
      scoreLoss k n*score n 1 nA nB nC A B C rs := by
  have hpos : 0 < (PrimeDensity.candidates (primeWindow n)).card := by
    rw [← LightPrimePool.size_eq_card]
    exact LightPrimePool.size_pos (by have := primeWindow_ge_two n; omega)
  exact scoreLoss_finite_bound hpos hbudget (score_contraction A B C rs hA hB hC)
    (modulus_bounds n nA nB nC A B C rs).2

/-- The concrete owner-domain false mass has the existing subquadratic
majorant; the baseline uses the quadratic owner catalog and cubic band size. -/
theorem physical_false_mass_le {k n nA nB nC : ℕ} (A B C : ℕ → ℤ) (rs : List Record)
    (hcount : rs.length ≤ 3*bandCount n^2)
    (hbudget : divisorBudget k n*primeWindow n ≤
      candidateCount n*(4*(k+2)*(inputBits n+1)))
    (hA : ∀ i < nA, |A i| ≤ (n^k : ℤ))
    (hB : ∀ i < nB, |B i| ≤ (n^k : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (n^k : ℤ)) :
    (physicalMass n (modulus n nA nB nC A B C rs) nA nB nC A B C rs : ℝ) ≤
      MassScales.falseMajorant k n := by
  rw [physicalMass_eq_score]
  exact MassScales.false_mass_le (score_loss A B C rs hbudget hA hB hC)
    (initial_score_bound A B C rs hcount) (modulus_loss n nA nB nC A B C rs)

/-- The numerical density premise is supplied by the verified prime theorem,
uniformly over all input arrays and candidate records of the given size. -/
theorem physical_false_mass_eventually (k : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List Record),
      rs.length ≤ 3*bandCount n^2 →
      (∀ i < nA, |A i| ≤ (n^k : ℤ)) →
      (∀ i < nB, |B i| ≤ (n^k : ℤ)) →
      (∀ i < nC, |C i| ≤ (n^k : ℤ)) →
      (physicalMass n (modulus n nA nB nC A B C rs) nA nB nC A B C rs : ℝ) ≤
        MassScales.falseMajorant k n := by
  filter_upwards [actual_divisor_budget k] with n hbudget
  intro nA nB nC A B C rs hcount hA hB hC
  exact physical_false_mass_le A B C rs hcount hbudget hA hB hC

end ThreeSum.BandPrimeScales
