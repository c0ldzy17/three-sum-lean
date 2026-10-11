import Submission.ThreeSum.EncodedColorWantedCosts
import Submission.ThreeSum.EncodedColorPrimeReadyData

/-! # Uniform budgets for wanted records followed by the shared source banks -/

namespace ThreeSum.EncodedColorStageCosts

open Scales BandScales ArithmeticStageBounds

def incidenceCap (n : ℕ) : ℕ := bandSize n*ColorBandBounds.count n (bandSize n)

def sourceBase (free n M len : ℕ) : ℕ :=
  EncodedColorWantedCosts.sourceBase free M (microHalf (inputBits n)) (blockCount (inputBits n)) len

def time (n P M U len : ℕ) : ℕ :=
  EncodedColorWantedCosts.time P M (microHalf (inputBits n)) (blockCount (inputBits n)) U len+
    EncodedColorSourcesCosts.time n P U M+400

def space (free n P M U len : ℕ) : ℕ :=
  max (EncodedColorWantedCosts.space free P M (microHalf (inputBits n)) (blockCount (inputBits n)) U len)
    (SourceFiniteCosts.space (sourceBase free n M len) n P U M)

def word (n P M U len : ℕ) : ℕ :=
  LightEncodedColorWantedSources.word n P M U len

def depth (n M len : ℕ) : ℕ := LightEncodedColorWantedSources.depth n M len

theorem source_time_mono {n p P U D : ℕ} (hp : p ≤ P) :
    EncodedColorSourcesCosts.time n p U D ≤ EncodedColorSourcesCosts.time n P U D := by
  unfold EncodedColorSourcesCosts.time SourceFiniteCosts.time
  gcongr

theorem source_space_mono {base bound n p P U D : ℕ} (hb : base ≤ bound) (hp : p ≤ P) :
    SourceFiniteCosts.space base n p U D ≤ SourceFiniteCosts.space bound n P U D := by
  unfold SourceFiniteCosts.space
  gcongr

theorem source_word_mono {n p P U D : ℕ} (hp : p ≤ P) :
    SourceFiniteCosts.word n p U D ≤ SourceFiniteCosts.word n P U D := by
  unfold SourceFiniteCosts.word LightSourceControlsHost.word LightSourceBandHost.word
    LightSourceBandPair.word LightSourceBandStep.word LightSourceResidues.word
  gcongr

theorem base_le {free n p M len : ℕ} [NeZero M] {xs : List ℤ} (hlen : xs.length ≤ len) :
    LightEncodedColorFiniteSources.base free n p M xs ≤ sourceBase free n M len :=
  (EncodedColorWantedCosts.sourceBase_le free p M (microHalf (inputBits n))
    (blockCount (inputBits n)) xs).trans (EncodedColorWantedCosts.sourceBase_mono hlen)

theorem time_le {n p P M U len : ℕ} [NeZero M] {xs : List ℤ}
    (hp : p ≤ P) (hlen : xs.length ≤ len) :
    LightEncodedColorWantedSources.time n p M U xs ≤ time n P M U len := by
  have hw := (EncodedColorWantedCosts.time_le p M (microHalf (inputBits n))
    (blockCount (inputBits n)) U xs).trans (EncodedColorWantedCosts.time_mono hp hlen)
  have hs := source_time_mono (n := n) (U := U) (D := M) hp
  unfold LightEncodedColorWantedSources.time time
  omega

theorem space_le {free n p P M U len : ℕ} [NeZero M] {xs : List ℤ}
    (hp : p ≤ P) (hlen : xs.length ≤ len) :
    LightEncodedColorWantedSources.space free n p M U xs ≤ space free n P M U len := by
  have hw := (EncodedColorWantedCosts.space_le free p M (microHalf (inputBits n))
    (blockCount (inputBits n)) U xs).trans (EncodedColorWantedCosts.space_mono hp hlen)
  exact max_le_max hw (source_space_mono (base_le hlen) hp)

theorem word_le {n p P M U len len' : ℕ} (hp : p ≤ P) (hlen : len ≤ len') :
    LightEncodedColorWantedSources.word n p M U len ≤ word n P M U len' :=
  max_le_max (EncodedColorWantedCosts.word_mono hp hlen) (source_word_mono hp)

theorem depth_le {n M len len' : ℕ} (hlen : len ≤ len') :
    LightEncodedColorWantedSources.depth n M len ≤ depth n M len' := by
  unfold depth LightEncodedColorWantedSources.depth
  omega

theorem finish_le {base bound NL NR n : ℕ} (hn : 0 < n)
    (hb : base ≤ bound) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.finish base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤ SourceFiniteCosts.finish bound n := by
  apply (SourceFiniteCosts.finish_le hn hNL hNR).trans
  unfold SourceFiniteCosts.finish
  omega

theorem selected_le_maxMod {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hR : 4 ≤ radix n) : EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC ≤ maxMod n := by
  have hp := EncodedColorPrimeReadyData.selected_guard (A := A) (B := B) (C := C)
    (hsA := hsA) (hsB := hsB) (hsC := hsC) hR
  have hy := primeWindow_ge_two n
  have hm : radix n ≤ maxMod n := by
    unfold maxMod
    exact Nat.le_mul_of_pos_right _ (by positivity)
  omega

end ThreeSum.EncodedColorStageCosts
