import Submission.ThreeSum.LightTernaryCarryApply

/-! Original signed requester initialization composed with literal carry cells. -/
namespace ThreeSum.LightTernaryOriginalRequester
open Light TernarySignedDigits TernarySignedReduction

def body (pRow pApply : ℕ) : Stmt :=
  .call pRow [v 0,v 1,k 1,v 3,v 2,v 4,v 6,k 1,k 1] 7 ;;
  .call pApply [v 4,v 5,v 3,v 2] 0

def time (J U : ℕ) : ℕ :=
  LightTernarySignedRow.time J (3*U)+LightTernaryCarryApply.time J+80

structure Procs (P : Program) (pMain : ℕ) where
  pRow : ℕ
  pApply : ℕ
  pLinear : ℕ
  row : LightTernarySignedRow.Procs P pRow
  correction : P[pApply]?=some (LightTernaryCarryApply.body pLinear)
  linear : P[pLinear]?=some LightArray.linearBody
  main : P[pMain]?=some (body pRow pApply)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ→ℤ} {U radix J dst carry work : ℕ} (a : ℤ) (c : CarryWord J)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+3<lim.depth) (hb : 1<radix)
    (hA : |a|≤(U : ℤ)) (hcarryBefore : carry+J+1≤dst) (hsep : dst+J+2≤work)
    (hspace : LightTernarySignedRow.space work (3*U)≤lim.space)
    (hword : (LightTernarySignedRow.word (3*U) radix J : ℤ)≤lim.word)
    (hcarry : ∀ k≤J, μ (carry+k)=carryAt c (J-k)) :
    Meets lim P pMain d [a,U,radix,J,dst,carry,work] μ (time J U)
      (fun _ ν => LightTernarySignedRow.Row ν dst J (requesterRaw U radix J a c) ∧
        Kept μ ν dst) := by
  have hs := shiftOne_cast hA
  have hbounds := abs_le.mp hA
  have hU : (0 : ℤ)≤U := by positivity
  have hv : shiftOne U a≤3*U := by exact_mod_cast (by omega : (shiftOne U a : ℤ)≤3*U)
  have hwork : work≤lim.space := by
    unfold LightTernarySignedRow.space LightOutputDecodeDigits.space at hspace
    omega
  have hB : (4*(radix : ℤ)+8)≤lim.word := by
    have hh : 4*radix+8≤LightTernarySignedRow.word (3*U) radix J := by
      unfold LightTernarySignedRow.word LightOutputDecodeDigits.word
      omega
    have hhZ : 4*(radix : ℤ)+8≤(LightTernarySignedRow.word (3*U) radix J : ℤ) := by
      exact_mod_cast hh
    exact hhZ.trans hword
  apply Meets.of_body S.main
  unfold body time
  light_call (S.row.meets (d := d+1) (μ := μ) (J := J) (radix := radix)
    (dst := dst) (work := work) (V := 3*U) (value := shiftOne U a)
    (offset := U) (x := a) (sign := (1 : ℤ)) (tag0 := (1 : ℤ)) (tag1 := (1 : ℤ))
    hw (by omega) hb.le hv (by omega) (hA.trans (by omega)) (by omega)
    (by norm_num) (by norm_num) (by norm_num) hsep hspace hword)
    using LightTernarySignedRow.time,LightTernaryCarryApply.time
      with r ν ⟨hread,ht0,ht1,hkeep1⟩
  have hcRead : ∀ k≤J, ν (carry+k)=carryAt c (J-k) := by
    intro k hk
    rw [hkeep1 _ (by omega),hcarry k hk]
  have hARead : ∀ k<J, ν (dst+k)=(digit radix (shiftOne U a) (J-1-k) : ℤ) := by
    intro k hk
    rw [hread k hk,one_mul]
    have hj : J-1-k<J := by omega
    have he := OutputDecodeOrder.indices_getD_reverse radix J (shiftOne U a) hj
    rw [show J-1-(J-1-k)=k by omega] at he
    rw [he]
    rfl
  light_call (LightTernaryCarryApply.meets (d := d+1) (μ := ν)
    (U := U) (radix := radix) (J := J) (dst := dst) (carry := carry)
    S.correction S.linear a c hw (by omega) hb (Or.inl hcarryBefore)
    (by omega) hB hARead hcRead ht0 ht1)
    using LightTernarySignedRow.time,LightTernaryCarryApply.time
      with r' ξ ⟨hrow,hkeep2⟩
  refine ⟨hrow,?_⟩
  intro i hi
  exact (hkeep2 i hi).trans (hkeep1 i hi)

def program : Program :=
  [body 1 4,LightTernarySignedRow.body 2,LightOutputDecodeDigits.body 3,
    LightOutputDecodeDivide.body,LightTernaryCarryApply.body 5,LightArray.linearBody]

def procs : Procs program 0 where
  pRow := 1
  pApply := 4
  pLinear := 5
  row := ⟨2,3,rfl,rfl,rfl⟩
  correction := rfl
  linear := rfl
  main := rfl

end ThreeSum.LightTernaryOriginalRequester
