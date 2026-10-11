import Submission.ThreeSum.EncodedColorPrimeData
import Submission.ThreeSum.LightBandRawAColor

/-! # One compact retained layout for a selected color -/

namespace ThreeSum.EncodedColorLayout

def colors (free : ℕ) : ℕ := free+8
def class0 (free n : ℕ) : ℕ := colors free+n
def class1 (free n : ℕ) : ℕ := class0 free n+n+1
def class2 (free n : ℕ) : ℕ := class1 free n+n+1
def av (free n : ℕ) : ℕ := class2 free n+n+1
def ae (free n : ℕ) : ℕ := av free n+n
def bv (free n : ℕ) : ℕ := ae free n+2+2*n
def be (free n : ℕ) : ℕ := bv free n+n
def cv (free n : ℕ) : ℕ := be free n+2+2*n
def ce (free n : ℕ) : ℕ := cv free n+n
def tables (free n : ℕ) : ℕ := ce free n+2+2*n
def rec (free n g : ℕ) : ℕ := tables free n+ColorBandBounds.count n g
def vals (free n g : ℕ) : ℕ := rec free n g+4*ColorBandBounds.count n g
def normalizedEnd (free n g : ℕ) : ℕ := LightBandRawA.space (vals free n g) (ColorBandBounds.count n g) g
def prime (free n g : ℕ) : ℕ := normalizedEnd free n g+1
def cover (free n g M y : ℕ) : ℕ := EncodedColorPrimeData.nextFree (prime free n g) M y

def normalizedHeads (free n g : ℕ) : List ℤ :=
  [av free n,ae free n,bv free n,be free n,cv free n,ce free n,rec free n g,vals free n g]

theorem normalized_ends_before_count (free n g : ℕ) :
    av free n+n ≤ normalizedEnd free n g ∧ ae free n+2+2*n ≤ normalizedEnd free n g ∧
    bv free n+n ≤ normalizedEnd free n g ∧ be free n+2+2*n ≤ normalizedEnd free n g ∧
    cv free n+n ≤ normalizedEnd free n g ∧ ce free n+2+2*n ≤ normalizedEnd free n g ∧
    tables free n+ColorBandBounds.count n g ≤ normalizedEnd free n g ∧
    rec free n g+4*ColorBandBounds.count n g ≤ normalizedEnd free n g := by
  unfold normalizedEnd LightBandRawA.space LightBandRawA.positionBase LightBandRawA.ownerBase
    LightBandRawA.capacity vals rec tables ce cv be bv ae av
  omega

theorem free_le_normalizedEnd (free n g : ℕ) : free+8 ≤ normalizedEnd free n g := by
  unfold normalizedEnd LightBandRawA.space LightBandRawA.positionBase LightBandRawA.ownerBase
    LightBandRawA.capacity vals rec tables ce cv be bv ae av class2 class1 class0 colors
  omega

theorem normalized_ends (free n g : ℕ) :
    av free n+n ≤ prime free n g ∧ ae free n+2+2*n ≤ prime free n g ∧
    bv free n+n ≤ prime free n g ∧ be free n+2+2*n ≤ prime free n g ∧
    cv free n+n ≤ prime free n g ∧ ce free n+2+2*n ≤ prime free n g ∧
    tables free n+ColorBandBounds.count n g ≤ prime free n g ∧
    rec free n g+4*ColorBandBounds.count n g ≤ prime free n g := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := normalized_ends_before_count free n g
  unfold prime
  omega

theorem free_le_prime (free n g : ℕ) : free+8 ≤ prime free n g := by
  have h := free_le_normalizedEnd free n g
  unfold prime
  omega

theorem prime_le_cover (free n g M y : ℕ) : prime free n g+6 ≤ cover free n g M y := by
  unfold cover EncodedColorPrimeData.nextFree EncodedColorPrimeData.prefixBase EncodedColorPrimeData.poolBase
  omega

theorem normalized_ends_cover (free n g M y : ℕ) :
    av free n+n ≤ cover free n g M y ∧ ae free n+2+2*n ≤ cover free n g M y ∧
    bv free n+n ≤ cover free n g M y ∧ be free n+2+2*n ≤ cover free n g M y ∧
    cv free n+n ≤ cover free n g M y ∧ ce free n+2+2*n ≤ cover free n g M y ∧
    tables free n+ColorBandBounds.count n g ≤ cover free n g M y ∧
    rec free n g+4*ColorBandBounds.count n g ≤ cover free n g M y ∧
    LightBandRawA.space (vals free n g) (ColorBandBounds.count n g) g ≤ cover free n g M y := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := normalized_ends_before_count free n g
  have h := prime_le_cover free n g M y
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ normalizedEnd free n g ≤ _
  unfold prime at h
  omega

end ThreeSum.EncodedColorLayout
