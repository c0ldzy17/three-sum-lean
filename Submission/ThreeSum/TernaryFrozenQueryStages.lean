import Submission.ThreeSum.TernaryCodeSemantics
import Submission.ThreeSum.TernaryReconstruction

/-! The exact descending coordinate schedule and values consumed by frozen queries. -/

namespace ThreeSum.TernaryFrozenQueryStages

open ThreeSum.TernaryJointType ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction

set_option maxHeartbeats 2000000

def coords (N K : ℕ) : List (Fin N) := ((List.finRange N).take K).reverse

@[simp] theorem coords_zero (N : ℕ) : coords N 0=[] := by simp [coords]

theorem coords_succ {N K : ℕ} (hK : K<N) :
    coords N (K+1)=(⟨K,hK⟩ : Fin N)::coords N K := by
  unfold coords
  rw [List.take_succ_eq_append_getElem (by simpa using hK),List.reverse_append]
  simp [List.getElem_finRange]

theorem coords_length {N K : ℕ} (hK : K≤N) : (coords N K).length=K := by
  simp [coords,Nat.min_eq_left hK]

theorem coords_nodup (N K : ℕ) : (coords N K).Nodup := by
  have hn : ((List.finRange N).take K).Nodup := (List.nodup_finRange N).take
  simpa [coords] using hn

def stageValue {N : ℕ} (K : ℕ) (H : TritWord N→ℤ) : TritWord N→ℤ :=
  frozenInverse (coords N K) H

@[simp] theorem stageValue_zero {N : ℕ} (H : TritWord N→ℤ) : stageValue 0 H=H := by
  simp [stageValue,frozenInverse]

theorem stageValue_succ {N K : ℕ} (hK : K<N) (H : TritWord N→ℤ) (R : TritWord N) :
    stageValue (K+1) H R =
      inverseDigit (fun d => stageValue K H (Function.update R ⟨K,hK⟩ d)) (R ⟨K,hK⟩) := by
  rw [stageValue,coords_succ hK]
  rfl

theorem inverseDigit_abs (f : Fin 3→ℤ) (B : ℤ) (hf : ∀ d, |f d|≤B) (q : Fin 3) :
    |inverseDigit f q|≤4*B := by
  have hB : 0≤B := (abs_nonneg (f 0)).trans (hf 0)
  have hdiff (x y : ℤ) : |x-y|≤|x|+|y| := by
    simpa [sub_eq_add_neg] using abs_add_le x (-y)
  unfold inverseDigit
  split_ifs
  · exact (hf 0).trans (by omega)
  · exact (hdiff (f 1) (f 0)).trans (by linarith [hf 0,hf 1])
  · have hm : |2*f 1|≤2*B := by
      rw [abs_mul]
      norm_num
      linarith [hf 1]
    calc
      |f 2-2*f 1+f 0|≤|f 2-2*f 1|+|f 0| := abs_add_le _ _
      _≤(|f 2|+|2*f 1|)+|f 0| := add_le_add (hdiff _ _) le_rfl
      _≤4*B := by linarith [hf 0,hf 2]

theorem stageValue_abs {N : ℕ} (K : ℕ) (hK : K≤N) (H : TritWord N→ℤ) (U : ℕ)
    (hH : ∀ R, |H R|≤(U : ℤ)) (R : TritWord N) :
    |stageValue K H R|≤((4^K : ℕ) : ℤ)*(U : ℤ) := by
  induction K generalizing R with
  | zero => simpa using hH R
  | succ K ih =>
    have hKN : K<N := by omega
    rw [stageValue_succ hKN]
    have hh := inverseDigit_abs
      (fun d => stageValue K H (Function.update R ⟨K,hKN⟩ d))
      (((4^K : ℕ) : ℤ)*(U : ℤ))
      (fun d => ih (by omega) (Function.update R ⟨K,hKN⟩ d)) (R ⟨K,hKN⟩)
    simpa [pow_succ,Nat.cast_mul,mul_assoc,mul_comm,mul_left_comm] using hh

theorem low_step {N K : ℕ} (hK : K<N) :
    TernaryCodeSemantics.low (⟨K,hK⟩ : Fin N)=2*(N-(K+1)) := by
  unfold TernaryCodeSemantics.low
  change 2*(N-1-K)=2*(N-(K+1))
  congr 1
  omega

theorem high_step {N K : ℕ} (hK : K<N) :
    TernaryCodeSemantics.high (⟨K,hK⟩ : Fin N)=2*(N-(K+1))+1 := by
  rw [TernaryCodeSemantics.high,low_step hK]

end ThreeSum.TernaryFrozenQueryStages
