import Submission.ThreeSum.SourceBucketView

/-!
# Constant-time independent-flag-aware bucket header access

The procedure reads two computed prefix headers and returns the absolute
start address and the selected count. A false endpoint flag returns count
zero. The original arrays, bucket data, and retained transform tables are
preserved when placed before the two output cells.
-/

namespace ThreeSum.LightSourceBucketSelect

open Light SourceBuckets LightHistogram

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

/-- Arguments: offsets, flat index array, residue, independent flag, two-cell
output, residue count, original incidence count. -/
def body : Stmt :=
  .set 7 (M (v 0 +' v 2)) ;;
  .set 8 (M (v 0 +' v 2 +' k 1)) ;;
  .store (v 4) (v 1 +' v 7) ;;
  .ite (v 3 =' k 1)
    (.store (v 4 +' k 1) (v 8 -' v 7))
    (.store (v 4 +' k 1) (k 0))

def countSelected (key : ℕ → ℕ) (N r flag : ℕ) : ℕ :=
  if flag=1 then count key r N else 0

def selected (μ : ℕ → ℤ) (offsets flat r flag : ℕ) : List ℕ :=
  if flag=1 then SourceBucketView.indices μ offsets flat r else []

theorem selected_length {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r flag : ℕ}
    (H : Stored μ key N M offsets flat) (hr : r < M) :
    (selected μ offsets flat r flag).length = countSelected key N r flag := by
  unfold selected countSelected
  split <;> simp only [SourceBucketView.indices_length H hr,List.length_nil]

theorem mem_selected {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r flag i : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M) (hr : r < M) :
    i ∈ selected μ offsets flat r flag ↔ flag=1 ∧ i<N ∧ key i=r := by
  unfold selected
  by_cases hf : flag=1
  · simp only [hf,ite_true,true_and,SourceBucketView.mem_indices H hkey hr]
  · simp only [hf,ite_false,List.not_mem_nil,false_and]

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain : ℕ} (hmain : P[pMain]? = some body)
    {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r flag dst : ℕ}
    (H : Stored μ key N M offsets flat)
    (hw : (lim.space : ℤ) ≤ lim.word) (hoffsets : offsets+M+1 ≤ dst)
    (hflat : flat+N ≤ dst) (hspace : dst+2 ≤ lim.space)
    (hkey : ∀ i < N, key i < M) (hr : r < M) (_hflag : flag ≤ 1) :
    Meets lim P pMain d [offsets,flat,r,flag,dst,M,N] μ 120
      (fun _ ν => ν dst = ((flat+offset key N r : ℕ) : ℤ) ∧
        ν (dst+1) = (countSelected key N r flag : ℤ) ∧ SameOutside μ ν dst 2) := by
  have hread0 := H.offsets r (Nat.le_of_lt hr)
  have hread1 : μ (offsets+r+1) = (offset key N (r+1) : ℤ) := by
    simpa only [Nat.add_assoc] using H.offsets (r+1) (by omega)
  have haddr : ((offsets : ℤ)+(r : ℤ)+1).toNat = offsets+r+1 := by
    simpa only [Nat.cast_add,Nat.cast_one] using Int.toNat_natCast (offsets+r+1)
  have hstart := offset_le hkey (Nat.le_of_lt hr)
  have hstop := offset_le hkey (show r+1 ≤ M by omega)
  have hcnt := count_le key r N
  have hNWord : (N : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show N ≤ lim.space by omega)).trans hw
  have hstartWord := (Int.ofNat_le.mpr hstart).trans hNWord
  have hstopWord := (Int.ofNat_le.mpr hstop).trans hNWord
  have hcntWord := (Int.ofNat_le.mpr hcnt).trans hNWord
  have haddrWord : ((flat+offset key N r : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show flat+offset key N r ≤ lim.space by omega)).trans hw
  have hdiff : (offset key N (r+1) : ℤ)-(offset key N r : ℤ) = (count key r N : ℤ) := by
    rw [offset_succ,Nat.cast_add]
    ring
  apply Meets.of_body hmain
  unfold body
  light_set (offset key N r : ℕ) using hread0
  light_set (offset key N (r+1) : ℕ) using hread1,haddr
  light_store dst (flat+offset key N r : ℕ)
  light_if hy hn : (flag : ℤ)=1
  · have he : flag=1 := by exact_mod_cast hy
    light_store (dst+1) (count key r N : ℕ) using hdiff
    dsimp only
    refine ⟨?_,?_,?_⟩
    · rw [Function.update_of_ne (by omega),Function.update_self]
    · simp only [Function.update_self,countSelected,he,ite_true]
    · intro a ha
      rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
  · have he : flag≠1 := by exact_mod_cast hn
    light_store (dst+1) (0 : ℕ)
    dsimp only
    refine ⟨?_,?_,?_⟩
    · rw [Function.update_of_ne (by omega),Function.update_self]
    · simp only [Function.update_self,countSelected,he,ite_false,Nat.cast_zero]
    · intro a ha
      rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]

def program : Program := [body]

end ThreeSum.LightSourceBucketSelect
