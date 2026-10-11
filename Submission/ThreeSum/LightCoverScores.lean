import Submission.ThreeSum.LightBooleanDot
import Submission.ThreeSum.LightMinimum

/-!
# Computing all local-cover candidate scores

The input is a row-major Boolean cover matrix and an active-target vector.
This literal loop calls the checked Boolean scan once per row and stores
the negative count. A subsequent minimum scan selects the first maximum.
-/

namespace ThreeSum.LightCoverScores

open Light

def score (matrix : ℕ → ℕ → ℕ) (active : ℕ → ℕ) (cols row : ℕ) : ℕ :=
  LightBooleanDot.dot (matrix row) active cols

def body (pDot : ℕ) : Stmt :=
  .for 5 (v 4) (
    .call pDot [v 0 +' v 5 *' v 3,v 1,v 3] 6 ;;
    .store (v 2 +' v 5) (k 0 -' v 6))

def time (rows cols : ℕ) : ℕ := rows*(LightBooleanDot.time cols+70)+6

def Inv (μ : ℕ → ℤ) (matrix : ℕ → ℕ → ℕ) (active : ℕ → ℕ)
    (src activePtr dst rows cols i : ℕ) (σ : State) : Prop :=
  ∃ (v : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [src,activePtr,dst,cols,rows,i,v],μ'⟩ ∧
    (∀ j < i, μ' (dst+j) = -(score matrix active cols j : ℤ)) ∧
    SameOutside μ μ' dst rows

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain pDot : ℕ}
    (hmain : P[pMain]? = some (body pDot))
    (hdot : P[pDot]? = some LightBooleanDot.body)
    {μ : ℕ → ℤ} {src activePtr dst rows cols : ℕ}
    (matrix : ℕ → ℕ → ℕ) (active : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hsrc : src+rows*cols ≤ dst) (hactive : activePtr+cols ≤ dst)
    (hspace : dst+rows ≤ lim.space)
    (hread : ∀ i < rows, ∀ j < cols, μ (src+i*cols+j) = (matrix i j : ℤ))
    (hreadActive : ∀ j < cols, μ (activePtr+j) = (active j : ℤ))
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1)
    (hactiveValue : ∀ j < cols, active j ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim P pMain d [src,activePtr,dst,cols,rows] μ (time rows cols)
      (fun _ μ' => (∀ i < rows, μ' (dst+i) = -(score matrix active cols i : ℤ)) ∧
        SameOutside μ μ' dst rows) := by
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ matrix active src activePtr dst rows cols)
    rows (LightBooleanDot.time cols+62) ?_ ?_ ?_ ?_
  · refine ⟨0,μ,?_,?_,SameOutside.refl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : State))
        ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro j hj
      omega
  · rintro i _ hi _ ⟨v,μ',rfl,written,kept⟩
    have himul : (i+1)*cols ≤ rows*cols := Nat.mul_le_mul_right cols (by omega)
    have hrow : src+i*cols+cols ≤ dst := by nlinarith
    have hrowRead : ∀ j < cols, μ' (src+i*cols+j) = (matrix i j : ℤ) := by
      intro j hj
      rw [kept _ (by omega)]
      exact hread i hi j hj
    have hactRead : ∀ j < cols, μ' (activePtr+j) = (active j : ℤ) := by
      intro j hj
      rw [kept _ (by omega)]
      exact hreadActive j hj
    have hrowSpace : src+i*cols+cols ≤ lim.space := by omega
    have hactiveSpace : activePtr+cols ≤ lim.space := by omega
    have hmul : ((i*cols : ℕ) : ℤ) ≤ lim.word := by
      have hh : i*cols ≤ lim.space := by omega
      exact (by exact_mod_cast hh : ((i*cols : ℕ) : ℤ) ≤ lim.space).trans hw
    have haddr : ((src : ℤ)+(i : ℤ)*cols).toNat = src+i*cols := by
      rw [← Nat.cast_mul,← Nat.cast_add,Int.toNat_natCast]
    have hcall := LightBooleanDot.meets (d := d+1) (μ := μ')
      (srcA := src+i*cols) (srcB := activePtr) (n := cols)
      hdot (matrix i) active hw hrowSpace hactiveSpace hrowRead hactRead
      (hmatrix i hi) hactiveValue hword
    have hs : score matrix active cols i ≤ cols :=
      LightBooleanDot.dot_le (matrix i) active (hmatrix i hi) hactiveValue le_rfl
    have hsZ : (score matrix active cols i : ℤ) ≤ lim.word := by
      have hh : score matrix active cols i ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (score matrix active cols i : ℤ) ≤ lim.space).trans hw
    have hsDotZ : (LightBooleanDot.dot (matrix i) active cols : ℤ) ≤ lim.word := hsZ
    light_call hcall using haddr,LightBooleanDot.time,score with r μ₁ ⟨hr,hmem⟩
    subst μ₁
    light_store (dst+i) (-(score matrix active cols i : ℤ)) using hr,score,LightBooleanDot.time
    refine ⟨by simp,r,Function.update μ' (dst+i) (-(score matrix active cols i : ℤ)),
      by simp [update_frame_setLocal],?_,?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega)]
        exact written j hj
      · simp
    · exact kept.update ⟨by omega,by omega⟩ _
  · rintro _ _ ⟨v,μ',rfl,written,kept⟩
    exact ⟨written,kept⟩
  · rintro i _ _ _ ⟨v,μ',rfl,_,_⟩
    simp

def program : Program := [body 1,LightBooleanDot.body]

theorem program_meets
    {μ : ℕ → ℤ} {src activePtr dst rows cols : ℕ}
    (matrix : ℕ → ℕ → ℕ) (active : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hsrc : src+rows*cols ≤ dst) (hactive : activePtr+cols ≤ dst)
    (hspace : dst+rows ≤ lim.space)
    (hread : ∀ i < rows, ∀ j < cols, μ (src+i*cols+j) = (matrix i j : ℤ))
    (hreadActive : ∀ j < cols, μ (activePtr+j) = (active j : ℤ))
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1)
    (hactiveValue : ∀ j < cols, active j ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim program 0 d [src,activePtr,dst,cols,rows] μ (time rows cols)
      (fun _ μ' => (∀ i < rows, μ' (dst+i) = -(score matrix active cols i : ℤ)) ∧
        SameOutside μ μ' dst rows) :=
  meets rfl rfl matrix active hw hd hsrc hactive hspace hread hreadActive hmatrix hactiveValue hword

end ThreeSum.LightCoverScores
