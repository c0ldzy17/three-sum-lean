import Submission.ThreeSum.BandPrimeCostBounds
import Submission.ThreeSum.BandRawAFinite
import Submission.ThreeSum.SourceBandCosts

/-!
# The executed common-prime stage at the actual integer schedule

This interface consumes the physical records produced by the band catalog.
It derives every flag, band-start and candidate-count premise from that
catalog, computes the depth and pool, and returns the arithmetic guard and
the finite physical-domain false-mass bound at the actual execution cost.
-/

namespace ThreeSum.LightBandPrimeStage

open Light BandEnumeration BandCandidateRows Scales BandScales CostLedger

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

def finiteMass (n q nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List Record) : ℕ :=
  Arithmetic.weightedFalseCount (BandRawA.finiteAllProducts nA nB nC (bandSize n) rs)
    (fun t => C t.2.2.val-B t.2.1.val-BandRawA.valueAt nA (bandSize n) rs A t.1.val)
    (Auxiliary.moduli (WeightedScore.auxiliarySet (LightPrimePool.prime (primeWindow n))
      (LightPrimePool.size (primeWindow n)))) q

theorem finiteMass_eq_physical (n q nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List Record) :
    finiteMass n q nA nB nC A B C rs=BandPrimeScales.physicalMass n q nA nB nC A B C rs := by
  rw [BandPrimeScales.physicalMass_eq_score]
  exact BandRawA.finiteAll_weightedFalseCount _ _ _ _ _ _ _ _ _ _ _

theorem records_valid {A B C : Family} {nA nB nC g : ℕ}
    (hA : A.size=BandPartition.size nA g)
    (hB : B.size=BandPartition.size nB g)
    (hC : C.size=BandPartition.size nC g) (hg : 0 < g) :
    ∀ r ∈ records A B C, r.flag=1 → r.a*g ≤ nA ∧ r.b*g ≤ nB ∧ r.c*g ≤ nC := by
  intro r hr hf
  obtain ⟨ha,hb,hc,_⟩ := records_sound hr hf
  rw [hA] at ha
  rw [hB] at hb
  rw [hC] at hc
  exact ⟨(BandPartition.start_lt hg ha).le,(BandPartition.start_lt hg hb).le,
    (BandPartition.start_lt hg hc).le⟩

theorem records_count_bound {A B C : Family} {n nA nB nC : ℕ}
    (hA : A.size=BandPartition.size nA (bandSize n))
    (hB : B.size=BandPartition.size nB (bandSize n))
    (hC : C.size=BandPartition.size nC (bandSize n))
    (ha : nA ≤ n) (hb : nB ≤ n) (hc : nC ≤ n) :
    (records A B C).length ≤ 3*bandCount n^2 :=
  count_bound (hA.le.trans (SourceBandCosts.size_le_bandCount ha))
    (hB.le.trans (SourceBandCosts.size_le_bandCount hb))
    (hC.le.trans (SourceBandCosts.size_le_bandCount hc))

abbrev program := LightBandPrimeSetup.program

variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c n nA nB nC k recs free : ℕ}

theorem program_meets (A B C : Family)
    (hA : A.size=BandPartition.size nA (bandSize n))
    (hB : B.size=BandPartition.size nB (bandSize n))
    (hC : C.size=BandPartition.size nC (bandSize n))
    (hn : 0 < n) (hnA : nA ≤ n) (hnB : nB ≤ n) (hnC : nC ≤ n)
    (hR : 4 ≤ radix n)
    (hbudget : divisorBudget k n*primeWindow n ≤ candidateCount n*(4*(k+2)*(inputBits n+1)))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hrecs : recs+4*(records A B C).length ≤ free)
    (hspace : LightBandPrimeSetup.space free (ArithmeticStageBounds.maxMod n) (bandSize n)
      (radix n) (primeWindow n) (n^k) ≤ lim.space)
    (hword : (LightBandPrimeSetup.word (ArithmeticStageBounds.maxMod n) nA nB nC (bandSize n)
      (records A B C).length (radix n) (primeWindow n) (n^k) : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 (ArithmeticStageBounds.maxMod n)+10 ≤ lim.depth)
    (hrecords : Seg μ recs (cells (records A B C)))
    (hvaluesA : ∀ i < nA, |μ (a+i)| ≤ (n^k : ℤ))
    (hvaluesB : ∀ i < nB, |μ (b+i)| ≤ (n^k : ℤ))
    (hvaluesC : ∀ i < nC, |μ (c+i)| ≤ (n^k : ℤ)) :
    Meets lim program 24 d
      [a,b,c,nA,nB,nC,bandSize n,recs,(records A B C).length,radix n,primeWindow n,free] μ
      (BandPrimeCosts.timeBudget k n)
      (fun result ν =>
        result=(BandPrimeScales.modulus n nA nB nC
          (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) (records A B C) : ℤ) ∧
        0 < result ∧ 4*result ≤ (radix n : ℤ) ∧
        SegN ν free (LightPrimePool.values (primeWindow n)) ∧
        (∀ i ≤ primeDepth radix n, ν (free+3*primeWindow n+i)=
          (LightBandPrimeConstruction.modulus (primeWindow n) nA nB nC (bandSize n)
            (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) (records A B C) i : ℤ)) ∧
        (finiteMass n result.toNat nA nB nC
          (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) (records A B C) : ℝ) ≤
            MassScales.falseMajorant k n ∧ Kept μ ν free) := by
  have hcount := records_count_bound hA hB hC hnA hnB hnC
  have hy : 0 < primeWindow n := by have := primeWindow_ge_two n; omega
  have hp := LightBandPrimeSetup.program_meets (d := d) (μ := μ) (a := a) (b := b) (c := c)
    (records A B C) hw hy (bandSize_pos n) ha hb hc hrecs hspace hword hd hrecords
    (fun _ hr => records_flag hr) (records_valid hA hB hC (bandSize_pos n))
    (by simpa only [Nat.cast_pow] using hvaluesA)
    (by simpa only [Nat.cast_pow] using hvaluesB)
    (by simpa only [Nat.cast_pow] using hvaluesC)
    (BandPrimeScales.resource_modulus_bound hR)
  refine hp.mono (BandPrimeCosts.setup_time_le_budget k hn hcount) ?_
  rintro result ν ⟨hresult,hpool,hprefix,hkeep⟩
  have hres : result=(BandPrimeScales.modulus n nA nB nC
      (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) (records A B C) : ℤ) := hresult
  have hpos := BandPrimeChoice.modulus_pos (nA := nA) (nB := nB) (nC := nC) (g := bandSize n)
    (LightPrimePool.prime (primeWindow n))
    (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) (records A B C)
    (LightPrimePool.size_pos hy) (fun _ hi => (LightPrimePool.prime_spec hi).1) (primeDepth radix n)
  have hguard := BandPrimeScales.modulus_guard (nA := nA) (nB := nB) (nC := nC)
    (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) (records A B C) hR
  refine ⟨hres,?_,?_,hpool,hprefix,?_,hkeep⟩
  · rw [hres]
    exact_mod_cast hpos
  · rw [hres]
    exact_mod_cast hguard
  · rw [hres,Int.toNat_natCast,finiteMass_eq_physical]
    exact BandPrimeScales.physical_false_mass_le
      (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) (records A B C)
      hcount hbudget hvaluesA hvaluesB hvaluesC

end ThreeSum.LightBandPrimeStage
