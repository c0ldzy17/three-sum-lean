import Submission.ThreeSum.TernaryFrozenQueryStages
import Submission.ThreeSum.TernaryTransform
import Submission.ThreeSum.LightTernaryMetadata
import Submission.ThreeSum.LightTernaryPass
import Submission.ThreeSum.LightTernaryInversePass

/-! Exact compact bank indices and stage values for the actual assembly loops. -/
namespace ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 3000000

structure Enumeration (N T n : ℕ) where
  word : ℕ→TritWord N
  mem : ∀ j<n, rank (word j)≤T
  complete : ∀ R : TritWord N, rank R≤T → ∃ j<n, word j=R

def lowerWord {N : ℕ} (R : TritWord N) (i : Fin N) (e : Fin 3) : TritWord N :=
  Function.update R i (min e (R i))

theorem lowerWord_below {N : ℕ} (R : TritWord N) (i : Fin N) (e : Fin 3) :
    Below (lowerWord R i e) R := update_below R i _ (min_le_right _ _)

theorem lowerWord_of_le {N : ℕ} (R : TritWord N) (i : Fin N) (e : Fin 3) (he : e≤R i) :
    lowerWord R i e=Function.update R i e := by simp [lowerWord,min_eq_left he]

theorem lowerWord_zero {N : ℕ} (R : TritWord N) (i : Fin N) :
    lowerWord R i 0=Function.update R i 0 := by
  apply lowerWord_of_le
  exact Fin.zero_le _

theorem min_one (q : Fin 3) : min (1 : Fin 3) q=clampOne q := by
  fin_cases q <;> decide

theorem lowerWord_one {N : ℕ} (R : TritWord N) (i : Fin N) :
    lowerWord R i 1=Function.update R i (clampOne (R i)) := by simp [lowerWord,min_one]

theorem lowerWord_two {N : ℕ} (R : TritWord N) (i : Fin N) : lowerWord R i 2=R := by
  have hm : min (2 : Fin 3) (R i)=R i := by generalize R i=q; fin_cases q <;> decide
  simp [lowerWord,hm]

noncomputable def index {N T n : ℕ} (E : Enumeration N T n) (i : Fin N)
    (e : Fin 3) (j : ℕ) : ℕ :=
  if hj : j<n then Classical.choose (E.complete (lowerWord (E.word j) i e)
    ((rank_mono (lowerWord_below (E.word j) i e)).trans (E.mem j hj))) else 0

theorem index_spec {N T n : ℕ} (E : Enumeration N T n) (i : Fin N)
    (e : Fin 3) (j : ℕ) (hj : j<n) :
    index E i e j<n ∧ E.word (index E i e j)=lowerWord (E.word j) i e := by
  unfold index
  rw [dif_pos hj]
  exact Classical.choose_spec (E.complete _ ((rank_mono (lowerWord_below (E.word j) i e)).trans (E.mem j hj)))

theorem index_update {N T n : ℕ} (E : Enumeration N T n) (i : Fin N)
    (e : Fin 3) (j : ℕ) (hj : j<n) (he : e≤E.word j i) :
    E.word (index E i e j)=Function.update (E.word j) i e :=
  (index_spec E i e j hj).2.trans (lowerWord_of_le _ _ _ he)

theorem index_zero_code {N T n : ℕ} (E : Enumeration N T n) (i : Fin N)
    (j : ℕ) (hj : j<n) :
    address (E.word (index E i 0 j))=
      LightTernaryCodes.zeroCode (2*N) (low i) (high i) (address (E.word j)) := by
  rw [(index_spec E i 0 j hj).2,lowerWord_zero,zeroCode_eq_update]

theorem index_one_code {N T n : ℕ} (E : Enumeration N T n) (i : Fin N)
    (j : ℕ) (hj : j<n) :
    address (E.word (index E i 1 j))=
      LightTernaryCodes.oneCode (2*N) (high i) (address (E.word j)) := by
  rw [(index_spec E i 1 j hj).2,lowerWord_one,oneCode_eq_update]

theorem index_two_code {N T n : ℕ} (E : Enumeration N T n) (i : Fin N)
    (j : ℕ) (hj : j<n) : address (E.word (index E i 2 j))=address (E.word j) := by
  rw [(index_spec E i 2 j hj).2,lowerWord_two]

def forwardStage {N : ℕ} (K : ℕ) (F : TritWord N→ℤ) : TritWord N→ℤ :=
  runZeta (coords N K) F

@[simp] theorem forwardStage_zero {N : ℕ} (F : TritWord N→ℤ) : forwardStage 0 F=F := by
  simp [forwardStage,runZeta]

theorem forwardStage_succ {N K : ℕ} (hK : K<N) (F : TritWord N→ℤ) :
    forwardStage (K+1) F=coordinateZeta ⟨K,hK⟩ (forwardStage K F) := by
  rw [forwardStage,coords_succ hK]
  rfl

theorem zetaDigit_abs (f : Fin 3→ℤ) (B : ℤ) (hf : ∀ d, |f d|≤B) (q : Fin 3) :
    |zetaDigit f q|≤4*B := by
  have hB : 0≤B := (abs_nonneg (f 0)).trans (hf 0)
  unfold zetaDigit
  split_ifs
  · exact (hf 0).trans (by omega)
  · exact (abs_add_le _ _).trans (by linarith [hf 0,hf 1])
  · have hm : |2*f 1|≤2*B := by rw [abs_mul]; norm_num; linarith [hf 1]
    calc
      |f 0+2*f 1+f 2|≤|f 0+2*f 1|+|f 2| := abs_add_le _ _
      _≤(|f 0|+|2*f 1|)+|f 2| := add_le_add (abs_add_le _ _) le_rfl
      _≤4*B := by linarith [hf 0,hf 2]

theorem forwardStage_abs {N : ℕ} (K : ℕ) (hK : K≤N) (F : TritWord N→ℤ) (V : ℕ)
    (hF : ∀ R, |F R|≤(V : ℤ)) (R : TritWord N) :
    |forwardStage K F R|≤((4^K : ℕ) : ℤ)*(V : ℤ) := by
  induction K generalizing R with
  | zero => simpa using hF R
  | succ K ih =>
    have hKN : K<N := by omega
    rw [forwardStage_succ hKN]
    have hh := zetaDigit_abs (fun d => forwardStage K F (Function.update R ⟨K,hKN⟩ d))
      (((4^K : ℕ) : ℤ)*(V : ℤ)) (fun d => ih (by omega) _) (R ⟨K,hKN⟩)
    simpa [coordinateZeta,pow_succ,Nat.cast_mul,mul_assoc,mul_comm,mul_left_comm] using hh

theorem forwardStage_full {N : ℕ} (F : TritWord N→ℤ) :
    forwardStage N F=ThreeSum.TernaryEuler.binomialZeta F := by
  have ht : (List.finRange N).take N=List.finRange N := List.take_of_length_le (by simp)
  exact ThreeSum.TernaryTransform.runZeta_eq_binomialZeta (coords N N) (coords_nodup N N)
    (by simp [coords,ht]) F

end ThreeSum.TernaryBankStageModel
