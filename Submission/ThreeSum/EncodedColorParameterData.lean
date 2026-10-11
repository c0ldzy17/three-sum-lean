import Submission.ThreeSum.LightParameterInit
import Submission.ThreeSum.ColorParameters

/-! # Physical control reads for one selected-color workspace -/

namespace ThreeSum.EncodedColorParameterData

open Light Scales BandScales

theorem reads {μ : ℕ → ℤ} {params n : ℕ} (H : Seg μ params (LightParameterInit.values n)) :
    μ params=(inputBits n : ℤ) ∧ μ (params+1)=(microHalf (inputBits n) : ℤ) ∧
    μ (params+3)=(blockCount (inputBits n) : ℤ) ∧ μ (params+4)=(mu n : ℤ) ∧
    μ (params+14)=(radix n : ℤ) ∧ μ (params+17)=(bandSize n : ℤ) ∧
    μ (params+18)=(primeWindow n : ℤ) := by
  have h (i : ℕ) (hi : i < 19) := H.getD (i := i)
    (by simpa [LightParameterInit.values,LightScales.values,LightLocalParameters.values,
      LightLocalCounts.values,LightGlobalSizes.values] using hi) 0
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [LightParameterInit.values,LightScales.values] using h 0 (by omega)
  · simpa [LightParameterInit.values,LightScales.values] using h 1 (by omega)
  · simpa [LightParameterInit.values,LightScales.values] using h 3 (by omega)
  · simpa [LightParameterInit.values,LightScales.values] using h 4 (by omega)
  · simpa [LightParameterInit.values,LightScales.values,LightLocalParameters.values,LightLocalCounts.values,
      LightGlobalSizes.values_scales] using h 14 (by omega)
  · simpa [LightParameterInit.values,LightScales.values,LightLocalParameters.values,LightLocalCounts.values,
      LightGlobalSizes.values_scales] using h 17 (by omega)
  · simpa [LightParameterInit.values,LightScales.values,LightLocalParameters.values,LightLocalCounts.values,
      LightGlobalSizes.values_scales] using h 18 (by omega)

theorem color_reads {μ : ℕ → ℤ} {row W : ℕ} {color : Coloring.Parameter W}
    (H : Seg μ row (ColorParameters.fields color)) :
    μ row=(color.1.1.val : ℤ) ∧ μ (row+1)=(color.1.2.val : ℤ) ∧
    μ (row+2)=((color.2 (false,false)).val : ℤ) ∧ μ (row+3)=((color.2 (false,true)).val : ℤ) ∧
    μ (row+4)=((color.2 (true,false)).val : ℤ) ∧ μ (row+5)=((color.2 (true,true)).val : ℤ) := by
  have h (i : ℕ) (hi : i < 6) := H.getD (i := i) (by simpa [ColorParameters.fields] using hi) 0
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa [ColorParameters.fields] using h 0 (by omega)
  · simpa [ColorParameters.fields] using h 1 (by omega)
  · simpa [ColorParameters.fields] using h 2 (by omega)
  · simpa [ColorParameters.fields] using h 3 (by omega)
  · simpa [ColorParameters.fields] using h 4 (by omega)
  · simpa [ColorParameters.fields] using h 5 (by omega)

end ThreeSum.EncodedColorParameterData
