import Submission.ThreeSum.TernaryWantedRadix

namespace ThreeSum.TernaryWantedCanonical
open TernaryWantedRadix

/-- Native blocks are consumed from least native position upward; canonical
word addresses append the corresponding word block in this same order. -/
def encode (digits : List ℕ) (R code : ℕ) : List ℕ → ℕ
  | [] => code
  | i::is => encode digits R (code*R+digits.getD i 0) is

def wantedCodes (p : ℤ) (raws : List ℤ) (digits : List ℕ) (j : ℕ)
    (x : ℤ) (code R : ℕ) : List ℕ :=
  (wantedOutputs p raws j x).map (encode digits R code)

@[simp] theorem wantedCodes_length (p : ℤ) (raws : List ℤ) (digits : List ℕ)
    (j : ℕ) (x : ℤ) (code R : ℕ) :
    (wantedCodes p raws digits j x code R).length=(wantedOutputs p raws j x).length := by
  simp [wantedCodes]

theorem wantedCodes_succ (p : ℤ) (raws : List ℤ) (digits : List ℕ)
    (j : ℕ) (x : ℤ) (code R : ℕ) :
    wantedCodes p raws digits (j+1) x code R = (localBucket p raws x).flatMap fun i =>
      wantedCodes p raws digits j ((x-raws.getD i 0)/p) (code*R+digits.getD i 0) R := by
  simp [wantedCodes,wantedOutputs,List.map_flatMap,List.map_map,Function.comp_def,encode]

def codeLimit (N code R j : ℕ) : ℕ := (code+R)*(2*(N+R))^j

theorem codeLimit_base {N code R j : ℕ} (hN : 1 ≤ N) :
    code+R ≤ codeLimit N code R j := by
  unfold codeLimit
  exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))

theorem codeLimit_child {N code R j digit : ℕ} (hN : 1 ≤ N) (hdigit : digit < R) :
    codeLimit N (code*R+digit) R j ≤ codeLimit N code R (j+1) := by
  unfold codeLimit
  rw [pow_succ']
  have h : code*R+digit+R ≤ (code+R)*(2*(N+R)) := by nlinarith
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right ((2*(N+R))^j) h

theorem wantedCodes_bound (p : ℤ) (raws : List ℤ) (digits : List ℕ) (R : ℕ)
    (hN : 1 ≤ raws.length) (hdigits : ∀ i < raws.length, digits.getD i 0 < R) :
    ∀ j x code z, z ∈ wantedCodes p raws digits j x code R →
      z ≤ codeLimit raws.length code R j := by
  intro j
  induction j with
  | zero => intro x code z hz; simp [wantedCodes,wantedOutputs,encode] at hz; subst z; simp [codeLimit]
  | succ j ih =>
    intro x code z hz
    rw [wantedCodes_succ] at hz
    obtain ⟨i,hi,hz⟩ := List.mem_flatMap.mp hz
    exact (ih _ _ _ hz).trans (codeLimit_child hN (hdigits i (mem_localBucket _ _ _ _ |>.mp hi).1))

end ThreeSum.TernaryWantedCanonical
