import Submission.ThreeSum.LightTernaryWantedBatch

namespace ThreeSum.TernaryWantedBatchCount
open LightTernaryWantedBatch TernaryWantedLittleEndian LightTernaryWantedCanonical

def count (p R S J : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ → ℤ) : ℕ → ℕ
  | 0 => 0
  | n+1 => count p R S J raws words maps targets n+
      (wantedCodes (p : ℤ) raws words maps J (targets n) R S 0 1 0 1).length

theorem rows_length (p R S J : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ → ℤ) (positions : ℕ → ℕ) (n : ℕ) :
    (rows p R S J raws words maps targets positions n).length=
      3*count p R S J raws words maps targets n := by
  induction n with
  | zero => simp [rows,count]
  | succ n ih => simp only [rows,List.length_append,rowCells_length,count,ih]; omega

theorem count_le (p R S J C : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ → ℤ) (positions : ℕ → ℕ)
    (hcap : ∀ x, (TernaryWantedRadix.localBucket (p : ℤ) raws x).length≤C) (n : ℕ) :
    count p R S J raws words maps targets n≤n*C^J := by
  have hh := LightTernaryWantedBatch.rows_length_le p R S J C raws words maps targets positions hcap n
  rw [rows_length] at hh
  nlinarith

theorem divide_count (p R S J : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ → ℤ) (positions : ℕ → ℕ) (n : ℕ) :
    (rows p R S J raws words maps targets positions n).length/3=
      count p R S J raws words maps targets n := by
  rw [rows_length,Nat.mul_div_right _ (by decide : 0<3)]

end ThreeSum.TernaryWantedBatchCount
