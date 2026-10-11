import Submission.ThreeSum.EncodedColorLayout

/-!
# Exact resource formulas for the original-input band and incidence program

These formulas use the existing selected-color layout without changing any
address or procedure. The physical BC, AB, AC owner records and the packed
value, owner, and sorted-position arrays are all included in the extent.
-/

namespace ThreeSum.LightBandRawAResources

open Light EncodedColorLayout

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

def cells (W n g : ℕ) : ℕ :=
  LightBandRawAColor.space (tables 0 n) (vals 0 n g) W n g

theorem space_eq (free W n g : ℕ) :
    LightBandRawAColor.space (tables free n) (vals free n g) W n g=free+cells W n g := by
  unfold cells LightBandRawAColor.space LightColorBands.space ColorBandBounds.space
    LightBandRawA.space LightBandRawA.positionBase LightBandRawA.ownerBase LightBandRawA.capacity
    vals rec tables ce cv be bv ae av class2 class1 class0 colors
  omega

theorem cells_eq (W n g : ℕ) : cells W n g=
    max (19+14*n+ColorBandBounds.count n g+ColorBandBounds.width n g+W)
      (17+13*n+5*ColorBandBounds.count n g+3*g*ColorBandBounds.count n g) := by
  unfold cells LightBandRawAColor.space LightColorBands.space ColorBandBounds.space
    LightBandRawA.space LightBandRawA.positionBase LightBandRawA.ownerBase LightBandRawA.capacity
    vals rec tables ce cv be bv ae av class2 class1 class0 colors
  congr 1 <;> ring

theorem clog_le_self (n : ℕ) : Nat.clog 2 n ≤ n :=
  Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)

theorem count_le (n g : ℕ) : ColorBandBounds.count n g ≤ 3*n^2 :=
  Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (BandPartition.size_le n g) 2)

theorem width_le (n g : ℕ) : ColorBandBounds.width n g ≤ 3*n+1 := by
  have hm := BandPartition.size_le n g
  have hc := clog_le_self (BandPartition.size n g+BandPartition.size n g+BandPartition.size n g+1)
  unfold ColorBandBounds.width LightBandEnumeration.width
  omega

theorem word_le (W n g U : ℕ) :
    LightBandRawAColor.word W n g U ≤ 2^(W+1)+3*n^2+29*n+2*g+9*U+100 := by
  have hm := BandPartition.size_le n g
  have hq := Nat.pow_le_pow_left hm 2
  unfold LightBandRawAColor.word LightColorBands.word ColorBandBounds.word
    LightBandEnumeration.word LightBandRawACatalog.word LightBandCandidates.word
    LightBandRawA.word LightBandEnumeration.count
  nlinarith only [hm,hq]

theorem depth_le (W n g : ℕ) : LightBandRawAColor.depth W n g ≤ W+5*n+21 := by
  have hc := clog_le_self n
  have hw := width_le n g
  unfold LightBandRawAColor.depth LightColorBands.depth ColorBandBounds.depth
  omega

end ThreeSum.LightBandRawAResources
