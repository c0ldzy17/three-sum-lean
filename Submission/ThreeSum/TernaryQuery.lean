import Submission.ThreeSum.TernaryBank

/-!
# Exact ternary binomial transforms

Each coordinate operation accesses exactly the three compressed digit states.
The source coefficients supplied to this transform are factorial weighted.
The inverse is the ordinary binomial difference, so no Boolean-copy table is
constructed or traversed.
-/

namespace ThreeSum.TernaryQuery

open ThreeSum.TernaryJointType
open ThreeSum.TernaryBank

def zetaDigit (f : Fin 3 → ℤ) (d : Fin 3) : ℤ :=
  if d = 0 then f 0 else if d = 1 then f 0 + f 1 else f 0 + 2 * f 1 + f 2

def inverseDigit (f : Fin 3 → ℤ) (d : Fin 3) : ℤ :=
  if d = 0 then f 0 else if d = 1 then f 1 - f 0 else f 2 - 2 * f 1 + f 0

theorem inverseDigit_zetaDigit (f : Fin 3 → ℤ) :
    inverseDigit (zetaDigit f) = f := by
  funext d
  fin_cases d <;> simp [inverseDigit, zetaDigit,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] <;> ring

theorem zetaDigit_inverseDigit (f : Fin 3 → ℤ) :
    zetaDigit (inverseDigit f) = f := by
  funext d
  fin_cases d <;> simp [inverseDigit, zetaDigit,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] <;> ring

def coordinateZeta {N : ℕ} (i : Fin N) (f : TritWord N → ℤ) (R : TritWord N) : ℤ :=
  zetaDigit (fun d => f (Function.update R i d)) (R i)

def coordinateInverse {N : ℕ} (i : Fin N) (f : TritWord N → ℤ)
    (R : TritWord N) : ℤ :=
  inverseDigit (fun d => f (Function.update R i d)) (R i)

theorem coordinateInverse_coordinateZeta {N : ℕ} (i : Fin N)
    (f : TritWord N → ℤ) : coordinateInverse i (coordinateZeta i f) = f := by
  funext R
  unfold coordinateInverse coordinateZeta
  simp only [Function.update_self, Function.update_idem]
  rw [inverseDigit_zetaDigit]
  simp

theorem coordinateZeta_coordinateInverse {N : ℕ} (i : Fin N)
    (f : TritWord N → ℤ) : coordinateZeta i (coordinateInverse i f) = f := by
  funext R
  unfold coordinateZeta coordinateInverse
  simp only [Function.update_self, Function.update_idem]
  rw [zetaDigit_inverseDigit]
  simp

def runZeta {N : ℕ} : List (Fin N) → (TritWord N → ℤ) → (TritWord N → ℤ)
  | [], f => f
  | i :: rest, f => coordinateZeta i (runZeta rest f)

def runInverse {N : ℕ} : List (Fin N) → (TritWord N → ℤ) → (TritWord N → ℤ)
  | [], f => f
  | i :: rest, f => runInverse rest (coordinateInverse i f)

theorem runInverse_runZeta {N : ℕ} (coords : List (Fin N)) (f : TritWord N → ℤ) :
    runInverse coords (runZeta coords f) = f := by
  induction coords with
  | nil => rfl
  | cons i rest ih =>
      simp only [runZeta, runInverse, coordinateInverse_coordinateZeta]
      exact ih

theorem update_below {N : ℕ} (R : TritWord N) (i : Fin N) (d : Fin 3)
    (hd : d ≤ R i) : Below (Function.update R i d) R := by
  intro j
  by_cases h : j = i
  · subst j
    simpa using hd
  · simp [Function.update_of_ne h]

/-- Every read of one compressed coordinate stage stays in the rank bank. -/
theorem coordinate_read_in_bank {N T : ℕ} {R : TritWord N} (hR : R ∈ bank N T)
    (i : Fin N) (d : Fin 3) (hd : d ≤ R i) :
    Function.update R i d ∈ bank N T :=
  bank_downward_closed (update_below R i d hd) hR

/-- No value above the requested digit is used by a coordinate stage. -/
theorem zetaDigit_congr_below (f g : Fin 3 → ℤ) (d : Fin 3)
    (h : ∀ e ≤ d, f e = g e) : zetaDigit f d = zetaDigit g d := by
  fin_cases d
  · simp [zetaDigit, h 0 (by decide)]
  · simp [zetaDigit, h 0 (by decide), h 1 (by decide)]
  · simp [zetaDigit, h 0 (by decide), h 1 (by decide), h 2 (by decide)]

theorem inverseDigit_congr_below (f g : Fin 3 → ℤ) (d : Fin 3)
    (h : ∀ e ≤ d, f e = g e) : inverseDigit f d = inverseDigit g d := by
  fin_cases d
  · simp [inverseDigit, h 0 (by decide)]
  · simp [inverseDigit, h 0 (by decide), h 1 (by decide)]
  · simp [inverseDigit, h 0 (by decide), h 1 (by decide), h 2 (by decide)]

end ThreeSum.TernaryQuery
