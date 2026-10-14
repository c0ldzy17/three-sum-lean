import Submission.ThreeSum.LightArray
import Submission.ThreeSum.TernaryQuery

/-!
# Actual RAM kernels for compressed ternary cells

The addresses are arguments computed by the surrounding compact-bank address
procedure. These kernels perform the value reads and exact three-state
arithmetic in the benchmark language, with constant cost. No transform value
is evaluated as an abstract machine operation.
-/

namespace ThreeSum.LightTernaryCell

open Light ThreeSum.TernaryQuery

variable {lim : Limits} {P : Program} {d : ℕ}

/-- Arguments: requested digit and addresses of digit-zero/one/two values. -/
def zetaBody : Stmt :=
  .ite (v 0 =' k 0) (.set 0 (M (v 1)))
    (.ite (v 0 =' k 1) (.set 0 (M (v 1) +' M (v 2)))
      (.set 0 (M (v 1) +' k 2 *' M (v 2) +' M (v 3))))

def inverseBody : Stmt :=
  .ite (v 0 =' k 0) (.set 0 (M (v 1)))
    (.ite (v 0 =' k 1) (.set 0 (M (v 2) -' M (v 1)))
      (.set 0 (M (v 3) -' k 2 *' M (v 2) +' M (v 1))))

def time : ℕ := 80

theorem zeta_meets {p : ℕ} (hp : P[p]? = some zetaBody)
    {μ : ℕ → ℤ} {a0 a1 a2 U : ℕ} (q : Fin 3) (f : Fin 3 → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (h0 : a0 < lim.space) (h1 : a1 < lim.space) (h2 : a2 < lim.space)
    (hr0 : μ a0 = f 0) (hr1 : μ a1 = f 1) (hr2 : μ a2 = f 2)
    (hf : ∀ e, |f e| ≤ U) (hword : 4 * (U : ℤ) + 3 ≤ lim.word) :
    Meets lim P p d [q.val,a0,a1,a2] μ time
      (fun r μ' => r = zetaDigit f q ∧ μ' = μ) := by
  have hb0 := abs_le.mp (hf 0)
  have hb1 := abs_le.mp (hf 1)
  have hb2 := abs_le.mp (hf 2)
  apply Meets.of_body hp
  unfold zetaBody time
  fin_cases q
  · refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by light_side)
    · light_set (f 0) using hr0
      exact ⟨by simp [zetaDigit], rfl⟩
    · exfalso
      exact hc (by simp)
  · refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by light_side)
    · exfalso
      norm_num at hc
    · refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by light_side)
      · light_set (f 0 + f 1) using hr0,hr1
        exact ⟨by simp [zetaDigit], rfl⟩
      · exfalso
        exact hc (by simp)
  · refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by light_side)
    · exfalso
      norm_num at hc
    · refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by light_side)
      · exfalso
        norm_num at hc
      · light_set (f 0 + 2 * f 1 + f 2) using hr0,hr1,hr2
        exact ⟨by simp [zetaDigit, Fin.ext_iff], rfl⟩

theorem inverse_meets {p : ℕ} (hp : P[p]? = some inverseBody)
    {μ : ℕ → ℤ} {a0 a1 a2 U : ℕ} (q : Fin 3) (f : Fin 3 → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (h0 : a0 < lim.space) (h1 : a1 < lim.space) (h2 : a2 < lim.space)
    (hr0 : μ a0 = f 0) (hr1 : μ a1 = f 1) (hr2 : μ a2 = f 2)
    (hf : ∀ e, |f e| ≤ U) (hword : 4 * (U : ℤ) + 3 ≤ lim.word) :
    Meets lim P p d [q.val,a0,a1,a2] μ time
      (fun r μ' => r = inverseDigit f q ∧ μ' = μ) := by
  have hb0 := abs_le.mp (hf 0)
  have hb1 := abs_le.mp (hf 1)
  have hb2 := abs_le.mp (hf 2)
  apply Meets.of_body hp
  unfold inverseBody time
  fin_cases q
  · refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by light_side)
    · light_set (f 0) using hr0
      exact ⟨by simp [inverseDigit], rfl⟩
    · exfalso
      exact hc (by simp)
  · refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by light_side)
    · exfalso
      norm_num at hc
    · refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by light_side)
      · light_set (f 1 - f 0) using hr0,hr1
        exact ⟨by simp [inverseDigit], rfl⟩
      · exfalso
        exact hc (by simp)
  · refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by light_side)
    · exfalso
      norm_num at hc
    · refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by light_side)
      · exfalso
        norm_num at hc
      · light_set (f 2 - 2 * f 1 + f 0) using hr0,hr1,hr2
        exact ⟨by simp [inverseDigit, Fin.ext_iff], rfl⟩

def program : Program := [zetaBody, inverseBody]

theorem program_zeta_meets {μ : ℕ → ℤ} {a0 a1 a2 U : ℕ}
    (q : Fin 3) (f : Fin 3 → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (h0 : a0 < lim.space) (h1 : a1 < lim.space) (h2 : a2 < lim.space)
    (hr0 : μ a0 = f 0) (hr1 : μ a1 = f 1) (hr2 : μ a2 = f 2)
    (hf : ∀ e, |f e| ≤ U) (hword : 4 * (U : ℤ) + 3 ≤ lim.word) :
    Meets lim program 0 d [q.val,a0,a1,a2] μ time
      (fun r μ' => r = zetaDigit f q ∧ μ' = μ) :=
  zeta_meets rfl q f hw h0 h1 h2 hr0 hr1 hr2 hf hword

theorem program_inverse_meets {μ : ℕ → ℤ} {a0 a1 a2 U : ℕ}
    (q : Fin 3) (f : Fin 3 → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (h0 : a0 < lim.space) (h1 : a1 < lim.space) (h2 : a2 < lim.space)
    (hr0 : μ a0 = f 0) (hr1 : μ a1 = f 1) (hr2 : μ a2 = f 2)
    (hf : ∀ e, |f e| ≤ U) (hword : 4 * (U : ℤ) + 3 ≤ lim.word) :
    Meets lim program 1 d [q.val,a0,a1,a2] μ time
      (fun r μ' => r = inverseDigit f q ∧ μ' = μ) :=
  inverse_meets rfl q f hw h0 h1 h2 hr0 hr1 hr2 hf hword

end ThreeSum.LightTernaryCell
