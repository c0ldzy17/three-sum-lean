import Submission.ThreeSum.EncodedColorSourceRetention

/-! # Write the compact selected-color result after all retained source data -/

namespace ThreeSum.LightEncodedColorResult

open Light

def values (prime cover wanted controls bank out len p : ℕ) : List ℤ :=
  [prime,cover,wanted,controls,bank,out+8,len,p]

def body : Stmt :=
  .set 8 (v 5 +' k 8) ;;
  .store (v 5) (v 0) ;;
  .store (v 5 +' k 1) (v 1) ;;
  .store (v 5 +' k 2) (v 2) ;;
  .store (v 5 +' k 3) (v 3) ;;
  .store (v 5 +' k 4) (v 4) ;;
  .store (v 5 +' k 5) (v 8) ;;
  .store (v 5 +' k 6) (v 6) ;;
  .store (v 5 +' k 7) (v 7) ;;
  .set 0 (v 5)

def memory (μ : ℕ → ℤ) (prime cover wanted controls bank out len p : ℕ) : ℕ → ℤ :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update μ out (prime : ℤ))
      (out+1) cover) (out+2) wanted) (out+3) controls) (out+4) bank) (out+5) (out+8)) (out+6) len) (out+7) p

theorem memory_kept (μ : ℕ → ℤ) (prime cover wanted controls bank out len p : ℕ) :
    Kept μ (memory μ prime cover wanted controls bank out len p) out := by
  intro q hq
  unfold memory
  repeat rw [Function.update_of_ne (by omega)]

theorem memory_values (μ : ℕ → ℤ) (prime cover wanted controls bank out len p : ℕ) :
    Seg (memory μ prime cover wanted controls bank out len p) out
      (values prime cover wanted controls bank out len p) := by
  intro i hi
  have hi' : i < 8 := by simpa [values] using hi
  interval_cases i <;> simp [memory,values]

def program : Program := [body]

theorem program_length : program.length=1 := rfl

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain prime cover wanted controls bank out len p : ℕ} {μ : ℕ → ℤ}
    (main : P[pMain]?=some body) (hw : (lim.space : ℤ) ≤ lim.word)
    (hprime : prime ≤ out) (hcover : cover ≤ out) (hwanted : wanted ≤ out)
    (hcontrols : controls ≤ out) (hbank : bank ≤ out)
    (hspace : out+8 ≤ lim.space) (hlen : (len : ℤ) ≤ lim.word) (hp : (p : ℤ) ≤ lim.word) :
    Meets lim P pMain d [prime,cover,wanted,controls,bank,out,len,p] μ 600
      (fun r ν => r=(out : ℤ) ∧ Seg ν out (values prime cover wanted controls bank out len p) ∧ Kept μ ν out) := by
  apply Meets.of_body main
  unfold body
  light_set (out+8 : ℕ)
  light_store out prime
  light_store (out+1) cover
  light_store (out+2) wanted
  light_store (out+3) controls
  light_store (out+4) bank
  light_store (out+5) (out+8 : ℕ)
  light_store (out+6) len
  light_store (out+7) p
  light_set out
  exact ⟨rfl,memory_values μ prime cover wanted controls bank out len p,
    memory_kept μ prime cover wanted controls bank out len p⟩

theorem program_meets {prime cover wanted controls bank out len p : ℕ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hprime : prime ≤ out) (hcover : cover ≤ out) (hwanted : wanted ≤ out)
    (hcontrols : controls ≤ out) (hbank : bank ≤ out)
    (hspace : out+8 ≤ lim.space) (hlen : (len : ℤ) ≤ lim.word) (hp : (p : ℤ) ≤ lim.word) :
    Meets lim program 0 d [prime,cover,wanted,controls,bank,out,len,p] μ 600
      (fun r ν => r=(out : ℤ) ∧ Seg ν out (values prime cover wanted controls bank out len p) ∧ Kept μ ν out) :=
  meets rfl hw hprime hcover hwanted hcontrols hbank hspace hlen hp

end ThreeSum.LightEncodedColorResult
