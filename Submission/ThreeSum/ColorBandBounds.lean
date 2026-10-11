import Submission.ThreeSum.BandPreprocessingCorrectness

/-! # Uniform band resources for three classes whose lengths sum to n -/

namespace ThreeSum.ColorBandBounds

open BandPartition

set_option maxRecDepth 4000
set_option maxHeartbeats 800000

def count (n g : ℕ) : ℕ := 3*(size n g)^2
def width (n g : ℕ) : ℕ := LightBandEnumeration.width (size n g) (size n g) (size n g)
def time (n g : ℕ) : ℕ :=
  2100*(n+1)*(Nat.clog 2 n+1)+1000*(count n g+n+1)*(width n g+1)+400
def space (work n g : ℕ) : ℕ := work+n+count n g+width n g+1
def word (n g U : ℕ) : ℕ := n+g+2+
  LightBandEnumeration.word (size n g) (size n g) (size n g) U
def depth (n g : ℕ) : ℕ := n+Nat.clog 2 n+width n g+10

theorem count_le {a b c n g : ℕ} (hlen : a+b+c=n) :
    LightBandEnumeration.count (size a g) (size b g) (size c g) ≤ count n g := by
  simpa only [count,hlen] using LightBandPreprocessing.count_square_bound a b c g

theorem width_le {a b c n g : ℕ} (hlen : a+b+c=n) :
    LightBandEnumeration.width (size a g) (size b g) (size c g) ≤ width n g :=
  LightBandEnumeration.width_mono (size_mono (by omega : a ≤ n))
    (size_mono (by omega : b ≤ n)) (size_mono (by omega : c ≤ n))

theorem time_le {a b c n g : ℕ} (hlen : a+b+c=n) :
    LightBandPreprocessing.time a b c g ≤ time n g := by
  have ht := LightBandPreprocessing.time_bound a b c g
  have hc := count_le (g := g) hlen
  have hw := width_le (g := g) hlen
  have hp := Nat.mul_le_mul (Nat.mul_le_mul_left 1000
    (show LightBandEnumeration.count (size a g) (size b g) (size c g)+a+b+c+1 ≤
      count n g+n+1 by omega)) (Nat.add_le_add_right hw 1)
  unfold time
  rw [hlen] at ht
  omega

theorem space_le {a b c n g work : ℕ} (hlen : a+b+c=n) :
    LightBandPreprocessing.space work a b c g ≤ space work n g := by
  have hc := count_le (g := g) hlen
  have hw := width_le (g := g) hlen
  unfold LightBandPreprocessing.space space
  omega

theorem word_le {a b c n g U : ℕ} (hlen : a+b+c=n) :
    LightBandPreprocessing.word a b c g U ≤ word n g U := by
  have ha := size_mono (g := g) (by omega : a ≤ n)
  have hb := size_mono (g := g) (by omega : b ≤ n)
  have hc := size_mono (g := g) (by omega : c ≤ n)
  unfold LightBandPreprocessing.word word LightBandEnumeration.word
  omega

theorem depth_le {a b c n g : ℕ} (hlen : a+b+c=n) :
    LightBandPreprocessing.depth a b c g ≤ depth n g := by
  have hw := width_le (g := g) hlen
  unfold LightBandPreprocessing.depth depth
  rw [hlen]
  omega

end ThreeSum.ColorBandBounds
