import Submission.ThreeSum.LightModuloCounts

/-!
# Uniform bounds for repeated modular-counting calls

A caller may reserve resources for the largest modulus it will use. These
lemmas relate that reservation to the exact costed program contract.
-/

namespace ThreeSum.ModuloRuntime

open LightModuloCounts KaratsubaInterface

theorem capacity_mono {p q : ℕ} (h : p ≤ q) : capacity p ≤ capacity q := by
  exact Nat.pow_le_pow_right (by decide) (Nat.clog_mono_right 2 h)

theorem karatsuba_time_mono : Monotone LightKaratsuba.time := by
  apply monotone_nat_of_le_succ
  intro k
  rw [LightKaratsuba.time]
  omega

theorem time_mono {p q : ℕ} (h : p ≤ q) (nA nB nC U : ℕ) :
    time p nA nB nC U ≤ time q nA nB nC U := by
  have hc := capacity_mono h
  have hl := Nat.clog_mono_right 2 h
  have ht := karatsuba_time_mono hl
  unfold time LightCapacity.time LightResidueHistogram.time
    LightHistogram.histogramTime LightCyclic.combinedTime
  simp only [Light.fillTime, LightArray.linearTime]
  omega

theorem space_mono {p q : ℕ} (h : p ≤ q) (free N U : ℕ) :
    space free p N U ≤ space free q N U := by
  have hc := capacity_mono h
  unfold space
  omega

theorem word_mono {p q : ℕ} (h : p ≤ q) (N U : ℕ) :
    word p N U ≤ word q N U := by
  have hc := Nat.pow_le_pow_left (capacity_mono h) 3
  have hk : LightKaratsuba.wordBound (capacity p) N ≤
      LightKaratsuba.wordBound (capacity q) N := by
    unfold LightKaratsuba.wordBound
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 128 hc)
  unfold word
  omega

theorem depth_mono {p q : ℕ} (h : p ≤ q) (d : ℕ) :
    d+Nat.clog 2 p+3 ≤ d+Nat.clog 2 q+3 := by
  have hlog := Nat.clog_mono_right 2 h
  omega

/-- Uniform invocation of the actual modular-counting program. -/
theorem meets_bounded {lim : Light.Limits} {P : Light.Program} {d pMain : ℕ}
    (C : LightModuloCounts.Procs P pMain)
    {μ : ℕ → ℤ} {a b c nA nB nC p maxMod N free U : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 0 < p) (hm : p ≤ maxMod)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : space free maxMod N U ≤ lim.space)
    (hword : (word maxMod N U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 maxMod+3 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ)) :
    Light.Meets lim P pMain d [a,b,c,nA,nB,nC,p,N,free] μ
      (time maxMod nA nB nC U)
      (fun r μ' =>
        r = (ModuloCounts.count p nA nB nC
          (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) : ℤ) ∧
          Light.Kept μ μ' free) := by
  apply (C.meets hw hp ha hb hc hnA hnB hnC
    ((space_mono hm free N U).trans hspace)
    ((Int.ofNat_le.mpr (word_mono hm N U)).trans hword)
    ((depth_mono hm d).trans hd) hA hB hC).mono (time_mono hm nA nB nC U)
  intro r μ' hpost
  exact hpost

end ThreeSum.ModuloRuntime
