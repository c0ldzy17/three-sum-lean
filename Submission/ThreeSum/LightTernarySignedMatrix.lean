import Submission.ThreeSum.LightTernarySignedRow

/-!
# Actual matrices of original signed source rows

The loop reads every original source occurrence and writes its complete
signed digit row, including the two source tags. Equal input values remain
separate rows. Each call executes the logarithmic binary division routine.
-/

namespace ThreeSum.LightTernarySignedMatrix

open Light TernarySignedDigits TernarySignedReduction

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

/-- False selects the left source; true selects the right source. -/
def raw (right : Bool) (U radix J : ℕ) (x : ℤ) : Coordinate J → ℤ :=
  if right then rightRaw U radix J x else leftRaw U radix J x

/-- Arguments: original source, occurrence count, magnitude bound,
coordinate count, radix, matrix destination, division workspace. -/
def body (right : Bool) (pRow : ℕ) : Stmt :=
  .for 7 (v 1) (
    .call pRow [M (v 0 +' v 7),
      (if right then k 2 *' v 2 else v 2),
      (if right then k 1 else k 0 -' k 1),v 3,v 4,
      v 5 +' v 7 *' (v 3 +' k 2),v 6,
      k (if right then 0 else 1),k (if right then 1 else 0)] 8)

def time (n J U : ℕ) : ℕ := n*(LightTernarySignedRow.time J (3*U)+200)+20
def word (U radix J : ℕ) : ℕ := LightTernarySignedRow.word (3*U) radix J
def space (work U : ℕ) : ℕ := LightTernarySignedRow.space work (3*U)

def Rows (μ : ℕ → ℤ) (dst n J : ℕ) (f : ℕ → Coordinate J → ℤ) : Prop :=
  ∀ i < n, LightTernarySignedRow.Row μ (dst+i*(J+2)) J (f i)

theorem row_keep {μ ν : ℕ → ℤ} {a dst J : ℕ} {f : Coordinate J → ℤ}
    (hrow : LightTernarySignedRow.Row μ a J f) (hkeep : Kept μ ν dst)
    (hsep : a+J+2 ≤ dst) : LightTernarySignedRow.Row ν a J f := by
  rcases hrow with ⟨hd,h0,h1⟩
  refine ⟨?_,(hkeep _ (by omega)).trans h0,(hkeep _ (by omega)).trans h1⟩
  intro j
  exact (hkeep _ (by omega)).trans (hd j)

structure Procs (P : Program) (pMain : ℕ) (right : Bool) where
  pRow : ℕ
  row : LightTernarySignedRow.Procs P pRow
  main : P[pMain]? = some (body right pRow)

def Inv (right : Bool) (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (src n U J radix dst work i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [src,n,U,J,radix,dst,work,i,r],ν⟩ ∧
    Rows ν dst i J (fun j => raw right U radix J (f j)) ∧ Kept μ ν dst

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} {right : Bool} (C : Procs P pMain right)
    {μ : ℕ → ℤ} {src n U J radix dst work : ℕ} (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+3 < lim.depth)
    (hb : 1 ≤ radix) (hsrc : src+n ≤ dst) (hsep : dst+n*(J+2) ≤ work)
    (hspace : space work U ≤ lim.space) (hword : (word U radix J : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src+i) = f i) (hvalues : ∀ i < n, |f i| ≤ (U : ℤ)) :
    Meets lim P pMain d [src,n,U,J,radix,dst,work] μ (time n J U)
      (fun _ ν => Rows ν dst n J (fun i => raw right U radix J (f i)) ∧ Kept μ ν dst) := by
  have hwork : work ≤ lim.space := by
    unfold space LightTernarySignedRow.space LightOutputDecodeDigits.space at hspace
    omega
  have hUWord : (2*U : ℕ) ≤ word U radix J := by
    unfold word LightTernarySignedRow.word LightOutputDecodeDigits.word
    omega
  have hU : ((2*U : ℕ) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hUWord).trans hword
  have hJWord : J+2 ≤ word U radix J := by
    unfold word LightTernarySignedRow.word LightOutputDecodeDigits.word
    omega
  have hJ : ((J+2 : ℕ) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hJWord).trans hword
  apply Meets.of_body C.main
  unfold body time
  refine Ends.for (Inv right μ f src n U J radix dst work) n
    (LightTernarySignedRow.time J (3*U)+190) ?start ?round ?done ?bound
    (hT := by light_time)
  case start =>
    refine ⟨0,μ,?_,?_,SameOn.refl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : State))
        ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro i hi
      omega
  case round =>
    rintro i _ hi _ ⟨r,ν,rfl,written,kept⟩
    have hstep : (i+1)*(J+2) ≤ n*(J+2) :=
      Nat.mul_le_mul_right (J+2) (by omega)
    have hrowEnd : dst+i*(J+2)+J+2 ≤ work := by
      rw [Nat.add_mul] at hstep
      simp only [Nat.one_mul] at hstep
      omega
    have hcell : ν (src+i) = f i := (kept _ (by omega)).trans (hread i hi)
    have hval := hvalues i hi
    have hval' := abs_le.mp hval
    have haddrMul : i*(J+2) ≤ lim.space := by omega
    have haddrMul' : (i : ℤ)*((J : ℤ)+2) ≤ lim.word := by
      exact (by exact_mod_cast haddrMul : (i : ℤ)*((J : ℤ)+2) ≤ lim.space).trans hw
    have haddrMulNonneg : (0 : ℤ) ≤ (i : ℤ)*((J : ℤ)+2) := by positivity
    have hrowAddr : (dst : ℤ)+(i : ℤ)*((J : ℤ)+2) ≤ lim.word := by
      have hh : dst+i*(J+2) ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (dst : ℤ)+(i : ℤ)*((J : ℤ)+2) ≤ lim.space).trans hw
    have haddrEq : ((dst+i*(J+2) : ℕ) : ℤ) =
        (dst : ℤ)+(i : ℤ)*((J : ℤ)+2) := by push_cast; rfl
    have hcall :
        Meets lim P C.pRow (d+1)
          [f i,(if right then 2*U else U),(if right then 1 else -1),J,radix,
            dst+i*(J+2),work,(if right then 0 else 1),(if right then 1 else 0)]
          ν (LightTernarySignedRow.time J (3*U))
          (fun _ ν' => LightTernarySignedRow.Row ν' (dst+i*(J+2)) J
            (raw right U radix J (f i)) ∧ Kept ν ν' (dst+i*(J+2))) := by
      cases right
      · exact C.row.left_meets hw (by omega) hb hval hrowEnd hspace hword
      · exact C.row.right_meets hw (by omega) hb hval hrowEnd hspace hword
    cases right <;>
      light_call hcall using hcell,haddrEq,raw,LightTernarySignedRow.time with s ν' ⟨stored,kept'⟩
    all_goals
      refine ⟨by simp,s,ν',by simp [update_frame_setLocal],?_,?_⟩
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · apply row_keep (written j hj) kept'
          have hbefore : (j+1)*(J+2) ≤ i*(J+2) :=
            Nat.mul_le_mul_right (J+2) (by omega)
          rw [Nat.add_mul] at hbefore
          simp only [Nat.one_mul] at hbefore
          omega
        · exact stored
      · intro a ha
        exact (kept' a (by omega)).trans (kept a ha)
  case done =>
    rintro _ _ ⟨r,ν,rfl,written,kept⟩
    exact ⟨written,kept⟩
  case bound =>
    rintro i _ _ _ ⟨r,ν,rfl,_,_⟩
    light_side

theorem Procs.left_meets {pMain : ℕ} (C : Procs P pMain false)
    {μ : ℕ → ℤ} {src n U J radix dst work : ℕ} (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+3 < lim.depth)
    (hb : 1 ≤ radix) (hsrc : src+n ≤ dst) (hsep : dst+n*(J+2) ≤ work)
    (hspace : space work U ≤ lim.space) (hword : (word U radix J : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src+i) = f i) (hvalues : ∀ i < n, |f i| ≤ (U : ℤ)) :
    Meets lim P pMain d [src,n,U,J,radix,dst,work] μ (time n J U)
      (fun _ ν => Rows ν dst n J (fun i => leftRaw U radix J (f i)) ∧ Kept μ ν dst) :=
  C.meets f hw hd hb hsrc hsep hspace hword hread hvalues

theorem Procs.right_meets {pMain : ℕ} (C : Procs P pMain true)
    {μ : ℕ → ℤ} {src n U J radix dst work : ℕ} (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+3 < lim.depth)
    (hb : 1 ≤ radix) (hsrc : src+n ≤ dst) (hsep : dst+n*(J+2) ≤ work)
    (hspace : space work U ≤ lim.space) (hword : (word U radix J : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src+i) = f i) (hvalues : ∀ i < n, |f i| ≤ (U : ℤ)) :
    Meets lim P pMain d [src,n,U,J,radix,dst,work] μ (time n J U)
      (fun _ ν => Rows ν dst n J (fun i => rightRaw U radix J (f i)) ∧ Kept μ ν dst) :=
  C.meets f hw hd hb hsrc hsep hspace hword hread hvalues

def program (right : Bool) : Program :=
  [body right 1,LightTernarySignedRow.body 2,LightOutputDecodeDigits.body 3,
    LightOutputDecodeDivide.body]

def procs (right : Bool) : Procs (program right) 0 right :=
  ⟨1,⟨2,3,rfl,rfl,rfl⟩,rfl⟩

theorem time_bound (n J U : ℕ) :
    time n J U ≤ 600*n*(J+1)*(Nat.log 2 (3*U+1)+2)+20 := by
  have hlog : 2 ≤ Nat.log 2 (3*U+1)+2 := by omega
  have hlogJ := Nat.mul_le_mul_left J hlog
  have hrow : LightTernarySignedRow.time J (3*U)+200 ≤
      600*(J+1)*(Nat.log 2 (3*U+1)+2) := by
    unfold LightTernarySignedRow.time LightOutputDecodeDigits.time LightOutputDecodeDivide.budget
    nlinarith
  have hh := Nat.mul_le_mul_left n hrow
  unfold time
  nlinarith

end ThreeSum.LightTernarySignedMatrix
