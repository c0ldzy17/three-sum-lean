import Submission.ThreeSum.LightEncodedColorPrime

/-! # Actual finite budgets of the retained common-prime stage -/

namespace ThreeSum.EncodedColorPrimeCosts

open Light Scales BandScales CostLedger ArithmeticStageBounds

theorem core_time_eq (maxMod g R M y U : ℕ) :
    LightEncodedColorPrimeCore.time maxMod g R M y U=
      LightBandPrimeSetup.time maxMod g R M y U+760 := by
  unfold LightEncodedColorPrimeCore.time LightBandPrimeSetup.time LightBandPrimeConstruction.time
  omega

theorem time_eq (maxMod nA nB nC g M y U : ℕ) :
    LightEncodedColorPrime.time maxMod nA nB nC g M y U=
      LightBandPrimeSetup.time maxMod g (LightEncodedColorPrime.count nA nB nC g) M y U+1160 := by
  rw [LightEncodedColorPrime.time,core_time_eq]

theorem space_eq (free maxMod g M y U : ℕ) :
    LightEncodedColorPrimeCore.space free maxMod g M y U=
      LightBandPrimeSetup.space (EncodedColorPrimeData.poolBase free) maxMod g M y U := rfl

theorem count_mono {nA nB nC nA' nB' nC' g : ℕ} (ha : nA ≤ nA') (hb : nB ≤ nB') (hc : nC ≤ nC') :
    LightEncodedColorPrime.count nA nB nC g ≤ LightEncodedColorPrime.count nA' nB' nC' g := by
  have a := BandPartition.size_mono (g := g) ha
  have b := BandPartition.size_mono (g := g) hb
  have c := BandPartition.size_mono (g := g) hc
  unfold LightEncodedColorPrime.count
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul b c) (Nat.mul_le_mul a b)) (Nat.mul_le_mul a c)

theorem word_mono {maxMod nA nB nC nA' nB' nC' g M y U : ℕ}
    (ha : nA ≤ nA') (hb : nB ≤ nB') (hc : nC ≤ nC') :
    LightEncodedColorPrime.word maxMod nA nB nC g M y U ≤
      LightEncodedColorPrime.word maxMod nA' nB' nC' g M y U := by
  have hR := count_mono (g := g) ha hb hc
  have hmul := Nat.mul_le_mul_right (LightPrimePool.size y*g^3) hR
  unfold LightEncodedColorPrime.word LightEncodedColorPrimeCore.word
    LightBandWeightedScore.word LightBandWeightedScoreCell.word
  omega

theorem count_le {nA nB nC n : ℕ} (ha : nA ≤ n) (hb : nB ≤ n) (hc : nC ≤ n) :
    LightEncodedColorPrime.count nA nB nC (bandSize n) ≤ 3*bandCount n^2 := by
  have a := SourceBandCosts.size_le_bandCount ha
  have b := SourceBandCosts.size_le_bandCount hb
  have c := SourceBandCosts.size_le_bandCount hc
  have ab := Nat.mul_le_mul a b
  have ac := Nat.mul_le_mul a c
  have bc := Nat.mul_le_mul b c
  unfold LightEncodedColorPrime.count
  nlinarith

theorem time_le_budget {nA nB nC n : ℕ} (k : ℕ) (hn : 0 < n)
    (ha : nA ≤ n) (hb : nB ≤ n) (hc : nC ≤ n) :
    LightEncodedColorPrime.time (maxMod n) nA nB nC (bandSize n) (radix n) (primeWindow n) (n^k) ≤
      BandPrimeCosts.timeBudget k n+1160 := by
  rw [time_eq]
  exact Nat.add_le_add_right (BandPrimeCosts.setup_time_le_budget k hn (count_le ha hb hc)) 1160

theorem time_mono {maxMod nA nB nC nA' nB' nC' g M y U : ℕ}
    (ha : nA ≤ nA') (hb : nB ≤ nB') (hc : nC ≤ nC') :
    LightEncodedColorPrime.time maxMod nA nB nC g M y U ≤
      LightEncodedColorPrime.time maxMod nA' nB' nC' g M y U := by
  have hR := count_mono (g := g) ha hb hc
  unfold LightEncodedColorPrime.time LightEncodedColorPrimeCore.time LightBandPrimeChain.time
    LightBandPrimeMinimum.time LightBandWeightedScore.time
  gcongr

theorem moduli_pos {A B C : List ℤ} {g y : ℕ} {hg : 0 < g}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hy : 0 < y) (i : ℕ) : 0 < LightEncodedColorPrime.moduli A B C g hg hsA hsB hsC y i :=
  BandPrimeChoice.modulus_pos (LightPrimePool.prime y)
    (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
    (BandRawA.sortedRecords A B C g hg hsA hsB hsC) (LightPrimePool.size_pos hy)
    (fun j hj => (LightPrimePool.prime_spec hj).1) i

theorem scheduled_modulus_eq (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    LightEncodedColorPrime.moduli A B C (bandSize n) (bandSize_pos n) hsA hsB hsC (primeWindow n)
      (LightBandPrimeDepth.depth (radix n) (primeWindow n))=
      BandPrimeScales.modulus n A.length B.length C.length
        (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
        (BandRawA.sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC) := rfl

theorem scheduled_modulus_guard {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hR : 4 ≤ radix n) :
    4*LightEncodedColorPrime.moduli A B C (bandSize n) (bandSize_pos n) hsA hsB hsC (primeWindow n)
      (LightBandPrimeDepth.depth (radix n) (primeWindow n)) ≤ radix n := by
  rw [scheduled_modulus_eq]
  exact BandPrimeScales.modulus_guard _ _ _ _ hR

end ThreeSum.EncodedColorPrimeCosts
