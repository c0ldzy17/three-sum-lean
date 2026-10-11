import Submission.ThreeSum.BandCandidateRows

/-! # Actual four-cell flagged owner records -/

namespace ThreeSum.LightBandCandidatesCell

open Light BandCandidateRows

set_option maxHeartbeats 1400000
set_option maxRecDepth 6000

def tail (mode : Mode) : Stmt :=
  .store (v 3) (v 4) ;;
  .store (v 3 +' k 1) (match mode with | .bc => v 5 | _ => v 1) ;;
  .store (v 3 +' k 2) (match mode with | .bc => v 1 | .ab => v 2 | .ac => v 5) ;;
  .store (v 3 +' k 3) (match mode with | .ab => v 5 | _ => v 2)

/-- Lookup result, outer coordinate, inner coordinate, output pointer. -/
def body (mode : Mode) : Stmt :=
  .set 4 (k 0) ;;
  .set 5 (k 0) ;;
  .ite (k 0 <' v 0) (.set 4 (k 1) ;; .set 5 (v 0 -' k 1)) .skip ;;
  tail mode

def time : ℕ := 220

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {r i j dst U : ℕ}

theorem meets {pMain : ℕ} (mode : Mode)
    (hmain : P[pMain]?=some (body mode))
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : dst+4 ≤ lim.space)
    (hword : ((U+10 : ℕ) : ℤ) ≤ lim.word)
    (hr : r ≤ U) (hi : i ≤ U) (hj : j ≤ U) :
    Meets lim P pMain d [r,i,j,dst] μ time
      (fun _ ν => Seg ν dst (make mode i j r).cells ∧ SameOutside μ ν dst 4) := by
  have hrWord : (r : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : r ≤ U+10)).trans hword
  have hiWord : (i : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : i ≤ U+10)).trans hword
  have hjWord : (j : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : j ≤ U+10)).trans hword
  have h1Word : (1 : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : 1 ≤ U+10)).trans hword
  have htail (flag z : ℕ) (hflag : flag=if 0 < r then 1 else 0) (hz : z=r-1) :
      Ends lim P d (tail mode) ⟨frame [r,i,j,dst,flag,z],μ⟩ 140
        (fun σ => Seg σ.mem dst (make mode i j r).cells ∧ SameOutside μ σ.mem dst 4) := by
    have hf : flag ≤ 1 := by rw [hflag]; split_ifs <;> omega
    have hzU : z ≤ U := by omega
    have hfWord : (flag : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hf).trans h1Word
    have hzWord : (z : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : z ≤ U+10)).trans hword
    cases mode
    · unfold tail
      light_store dst (flag : ℕ)
      light_store (dst+1) (z : ℕ)
      light_store (dst+2) (i : ℕ)
      light_store (dst+3) (j : ℕ)
      exact ⟨by simp [make,Record.cells,seg_cons,← hflag,← hz,Nat.add_assoc],by light_keep⟩
    · unfold tail
      light_store dst (flag : ℕ)
      light_store (dst+1) (i : ℕ)
      light_store (dst+2) (j : ℕ)
      light_store (dst+3) (z : ℕ)
      exact ⟨by simp [make,Record.cells,seg_cons,← hflag,← hz,Nat.add_assoc],by light_keep⟩
    · unfold tail
      light_store dst (flag : ℕ)
      light_store (dst+1) (i : ℕ)
      light_store (dst+2) (z : ℕ)
      light_store (dst+3) (j : ℕ)
      exact ⟨by simp [make,Record.cells,seg_cons,← hflag,← hz,Nat.add_assoc],by light_keep⟩
  apply Meets.of_body hmain
  unfold body time
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  light_if hp hp : (0 : ℤ) < (r : ℤ)
  · have hrp : 0 < r := by omega
    light_set (1 : ℕ)
    light_set (r-1 : ℕ)
    light_piece (htail 1 (r-1) (by simp [hrp]) rfl)
  · have hr0 : r=0 := by omega
    light_piece (htail 0 0 (by simp [hr0]) (by simp [hr0]))

end ThreeSum.LightBandCandidatesCell
