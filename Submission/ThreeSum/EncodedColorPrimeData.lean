import Submission.ThreeSum.LightBandPrimeDepth
import Submission.ThreeSum.LightBandPrimeConstruction

/-! # Retained common-prime metadata for one actual color execution -/

namespace ThreeSum.EncodedColorPrimeData

open Light

def poolBase (free : ℕ) : ℕ := free+6
def prefixBase (free y : ℕ) : ℕ := poolBase free+3*y
def nextFree (free M y : ℕ) : ℕ := prefixBase free y+LightBandPrimeDepth.depth M y+1

def values (free M y p : ℕ) : List ℤ :=
  [p,LightBandPrimeDepth.depth M y,nextFree free M y,poolBase free,LightPrimePool.size y,prefixBase free y]

structure Stored (μ : ℕ → ℤ) (free M y : ℕ) (qs : ℕ → ℕ) : Prop where
  header : Seg μ free (values free M y (qs (LightBandPrimeDepth.depth M y)))
  pool : SegN μ (poolBase free) (LightPrimePool.values y)
  prefixes : ∀ i ≤ LightBandPrimeDepth.depth M y, μ (prefixBase free y+i)=(qs i : ℤ)

theorem Stored.heads_read {μ : ℕ → ℤ} {free M y : ℕ} {qs : ℕ → ℕ} (H : Stored μ free M y qs) :
    μ free=(qs (LightBandPrimeDepth.depth M y) : ℤ) ∧
    μ (free+1)=(LightBandPrimeDepth.depth M y : ℤ) ∧
    μ (free+2)=(nextFree free M y : ℤ) ∧
    μ (free+3)=(poolBase free : ℤ) ∧
    μ (free+4)=(LightPrimePool.size y : ℤ) ∧
    μ (free+5)=(prefixBase free y : ℤ) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa [values] using H.header.getD (i := 0) (by simp [values]) 0
  · simpa [values] using H.header.getD (i := 1) (by simp [values]) 0
  · simpa [values] using H.header.getD (i := 2) (by simp [values]) 0
  · simpa [values] using H.header.getD (i := 3) (by simp [values]) 0
  · simpa [values] using H.header.getD (i := 4) (by simp [values]) 0
  · simpa [values] using H.header.getD (i := 5) (by simp [values]) 0

theorem Stored.of_kept {μ ν : ℕ → ℤ} {free M y bound : ℕ} {qs : ℕ → ℕ}
    (H : Stored μ free M y qs) (K : Kept μ ν bound) (hb : nextFree free M y ≤ bound) :
    Stored ν free M y qs := by
  have hs := LightPrimePool.size_le y
  have hb' : free+6+3*y+LightBandPrimeDepth.depth M y+1 ≤ bound := hb
  refine ⟨?_,?_,?_⟩
  · intro i hi
    have hi' : i < 6 := by simpa only [values,List.length_cons,List.length_nil] using hi
    exact (K _ (by omega)).trans (H.header i hi)
  · apply H.pool.congr
    intro i hi
    have hi' : i < LightPrimePool.size y := by simpa only [LightPrimePool.size,List.length_map] using hi
    exact K _ (by unfold poolBase; omega)
  · intro i hi
    exact (K _ (by unfold prefixBase poolBase; omega)).trans (H.prefixes i hi)

end ThreeSum.EncodedColorPrimeData
