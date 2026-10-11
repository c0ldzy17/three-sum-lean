import Submission.ThreeSum.LightCoverScores
import Submission.ThreeSum.IndexedGreedy

/-! # Actual first-maximum candidate selection from a Boolean cover matrix -/

namespace ThreeSum.LightCoverSelect

open Light

def body (pScores pMinimum : ℕ) : Stmt :=
  .call pScores [v 0,v 1,v 2,v 4,v 3] 5 ;;
  .call pMinimum [v 2,v 3] 0

def time (rows cols : ℕ) : ℕ :=
  LightCoverScores.time rows cols+LightMinimum.time rows+60

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain pScores pDot pMinimum : ℕ}
    (hmain : P[pMain]? = some (body pScores pMinimum))
    (hscores : P[pScores]? = some (LightCoverScores.body pDot))
    (hdot : P[pDot]? = some LightBooleanDot.body)
    (hminimum : P[pMinimum]? = some LightMinimum.body)
    {μ : ℕ → ℤ} {src activePtr work rows cols : ℕ}
    (matrix : ℕ → ℕ → ℕ) (active : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hrows : 0 < rows)
    (hsrc : src+rows*cols ≤ work) (hactive : activePtr+cols ≤ work)
    (hspace : work+rows ≤ lim.space)
    (hread : ∀ i < rows, ∀ j < cols, μ (src+i*cols+j) = (matrix i j : ℤ))
    (hreadActive : ∀ j < cols, μ (activePtr+j) = (active j : ℤ))
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1)
    (hactiveValue : ∀ j < cols, active j ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim P pMain d [src,activePtr,work,rows,cols] μ (time rows cols)
      (fun r μ' =>
        r = (LightMinimum.least (fun i => -(LightCoverScores.score matrix active cols i : ℤ)) rows : ℤ) ∧
        SameOutside μ μ' work rows) := by
  apply Meets.of_body hmain
  unfold body time
  have hc := LightCoverScores.meets (d := d+1) (μ := μ)
    (src := src) (activePtr := activePtr) (dst := work) (rows := rows) (cols := cols)
    hscores hdot matrix active hw hd hsrc hactive hspace hread hreadActive hmatrix hactiveValue hword
  light_call hc using LightCoverScores.time,LightBooleanDot.time,LightMinimum.time
    with v μ₁ ⟨written,kept⟩
  have hm := LightMinimum.meets (d := d+1) (μ := μ₁) (src := work) (n := rows)
    hminimum (fun i => -(LightCoverScores.score matrix active cols i : ℤ))
    hw hrows hspace written
  light_call hm using LightCoverScores.time,LightBooleanDot.time,LightMinimum.time
    with r μ₂ ⟨hr,hmem⟩
  subst μ₂
  exact ⟨hr,kept⟩

structure Procs (P : Program) (pMain : ℕ) where
  pScores : ℕ
  pDot : ℕ
  pMinimum : ℕ
  main : P[pMain]? = some (body pScores pMinimum)
  scores : P[pScores]? = some (LightCoverScores.body pDot)
  dot : P[pDot]? = some LightBooleanDot.body
  minimum : P[pMinimum]? = some LightMinimum.body

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {src activePtr work rows cols : ℕ}
    (matrix : ℕ → ℕ → ℕ) (active : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hrows : 0 < rows)
    (hsrc : src+rows*cols ≤ work) (hactive : activePtr+cols ≤ work)
    (hspace : work+rows ≤ lim.space)
    (hread : ∀ i < rows, ∀ j < cols, μ (src+i*cols+j) = (matrix i j : ℤ))
    (hreadActive : ∀ j < cols, μ (activePtr+j) = (active j : ℤ))
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1)
    (hactiveValue : ∀ j < cols, active j ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim P pMain d [src,activePtr,work,rows,cols] μ (time rows cols)
      (fun r μ' =>
        r = (LightMinimum.least (fun i => -(LightCoverScores.score matrix active cols i : ℤ)) rows : ℤ) ∧
        SameOutside μ μ' work rows) :=
  LightCoverSelect.meets S.main S.scores S.dot S.minimum matrix active hw hd hrows
    hsrc hactive hspace hread hreadActive hmatrix hactiveValue hword

def program : Program :=
  [body 1 3,LightCoverScores.body 2,LightBooleanDot.body,LightMinimum.body]

theorem program_meets
    {μ : ℕ → ℤ} {src activePtr work rows cols : ℕ}
    (matrix : ℕ → ℕ → ℕ) (active : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hrows : 0 < rows)
    (hsrc : src+rows*cols ≤ work) (hactive : activePtr+cols ≤ work)
    (hspace : work+rows ≤ lim.space)
    (hread : ∀ i < rows, ∀ j < cols, μ (src+i*cols+j) = (matrix i j : ℤ))
    (hreadActive : ∀ j < cols, μ (activePtr+j) = (active j : ℤ))
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1)
    (hactiveValue : ∀ j < cols, active j ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim program 0 d [src,activePtr,work,rows,cols] μ (time rows cols)
      (fun r μ' =>
        r = (LightMinimum.least (fun i => -(LightCoverScores.score matrix active cols i : ℤ)) rows : ℤ) ∧
        SameOutside μ μ' work rows) :=
  meets rfl rfl rfl rfl matrix active hw hd hrows hsrc hactive hspace hread hreadActive
    hmatrix hactiveValue hword

end ThreeSum.LightCoverSelect
