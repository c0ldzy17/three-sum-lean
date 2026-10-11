import Submission.ThreeSum.LightArray
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# A checked Boolean inner product

The local-cover search uses this literal memory scan to count targets
covered by a candidate and still active. No set-cardinality oracle is an
instruction of the program.
-/

namespace ThreeSum.LightBooleanDot

open Light Finset
open scoped BigOperators

def dot (f g : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ range n, f i * g i

theorem dot_zero (f g : ℕ → ℕ) : dot f g 0 = 0 := by simp [dot]

theorem dot_succ (f g : ℕ → ℕ) (j : ℕ) :
    dot f g (j+1) = dot f g j + f j*g j := sum_range_succ _ _

theorem dot_le (f g : ℕ → ℕ) {n j : ℕ}
    (hf : ∀ i < n, f i ≤ 1) (hg : ∀ i < n, g i ≤ 1) (hj : j ≤ n) :
    dot f g j ≤ j := by
  unfold dot
  calc
    _ ≤ ∑ _i ∈ range j, 1 := by
      apply sum_le_sum
      intro i hi
      have hin : i < n := (mem_range.mp hi).trans_le hj
      exact (Nat.mul_le_mul (hf i hin) (hg i hin)).trans (by decide)
    _ = j := by simp

def loopBody : Stmt :=
  .set 3 (v 3 +' M (v 0 +' v 4) *' M (v 1 +' v 4))

def body : Stmt :=
  .set 3 (k 0) ;;
  .for 4 (v 2) loopBody ;;
  .set 0 (v 3)

def time (n : ℕ) : ℕ := 32*n+20

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {p : ℕ} (hp : P[p]? = some body)
    {μ : ℕ → ℤ} {srcA srcB n : ℕ} (f g : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hA : srcA+n ≤ lim.space) (hB : srcB+n ≤ lim.space)
    (hreadA : ∀ i < n, μ (srcA+i) = (f i : ℤ))
    (hreadB : ∀ i < n, μ (srcB+i) = (g i : ℤ))
    (hf : ∀ i < n, f i ≤ 1) (hg : ∀ i < n, g i ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim P p d [srcA,srcB,n] μ (time n)
      (fun r μ' => r = (dot f g n : ℤ) ∧ μ' = μ) := by
  apply Meets.of_body hp
  unfold body time
  light_set 0
  refine Ends.pieceThen (Ends.for (T := 32*n+6)
    (Q := fun σ => σ = ⟨frame [(srcA : ℤ),srcB,n,dot f g n,n],μ⟩)
    (fun j σ => σ = ⟨frame [(srcA : ℤ),srcB,n,dot f g j,j],μ⟩)
    n 24 ?_ ?_ ?_ ?_ (hT := by light_time)) ?_
  · simp [dot_zero,update_frame_setLocal]
  · rintro j _ hj _ rfl
    have ha := hreadA j hj
    have hb := hreadB j hj
    have hf' := hf j hj
    have hg' := hg j hj
    have hm : f j*g j ≤ 1 := (Nat.mul_le_mul hf' hg').trans (by decide)
    have hmZ : (f j : ℤ)*g j ≤ 1 := by exact_mod_cast hm
    have hn : (0 : ℤ) ≤ (f j : ℤ)*g j := by positivity
    have hs := dot_le f g hf hg (j := j+1) (by omega)
    have hsZ : (dot f g (j+1) : ℤ) ≤ lim.word := by
      have hsn : dot f g (j+1) ≤ lim.space := by omega
      exact (by exact_mod_cast hsn : (dot f g (j+1) : ℤ) ≤ lim.space).trans hw
    have hsCast : (dot f g j : ℤ)+(f j : ℤ)*g j = dot f g (j+1) := by
      simp [dot_succ]
    unfold loopBody
    refine Ends.setLast ?_ (hs := by light_side [ha,hb,hsCast]) (hT := by light_time)
    simp [ha,hb,hsCast,update_frame_setLocal]
  · intro σ hcounter hshape
    exact hshape
  · rintro j _ hj _ rfl
    light_side
  · intro σ hshape
    rw [hshape]
    light_set (dot f g n)
    exact ⟨rfl,rfl⟩

def program : Program := [body]

theorem program_meets
    {μ : ℕ → ℤ} {srcA srcB n : ℕ} (f g : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hA : srcA+n ≤ lim.space) (hB : srcB+n ≤ lim.space)
    (hreadA : ∀ i < n, μ (srcA+i) = (f i : ℤ))
    (hreadB : ∀ i < n, μ (srcB+i) = (g i : ℤ))
    (hf : ∀ i < n, f i ≤ 1) (hg : ∀ i < n, g i ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim program 0 d [srcA,srcB,n] μ (time n)
      (fun r μ' => r = (dot f g n : ℤ) ∧ μ' = μ) :=
  meets rfl f g hw hA hB hreadA hreadB hf hg hword

end ThreeSum.LightBooleanDot
