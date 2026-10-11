import Submission.ThreeSum.LightOutputDecodeDigits

/-!
# Actual big-endian occurrence-vector array

The finite loop decodes each physical bank index once, using the verified
logarithmic quotient routine. Its contiguous rows contain exactly J radix
digits. The shared source catalog consumes these rows without supplying an
enumeration oracle or running a loop over output subsets.
-/

namespace ThreeSum.LightSourceOccurrenceArray

open Light OutputDecodeOrder

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def body (pDigits : ℕ) : Stmt :=
  .for 5 (v 0) (
    .call pDigits [v 5,v 1,v 2,v 3 +' v 5 *' v 1,v 4] 6)

def time (N J : ℕ) : ℕ := N*(LightOutputDecodeDigits.time J N+150)+10

def Inv (μ : ℕ → ℤ) (N J m dst work i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [N,J,m,dst,work,i,r],ν⟩ ∧
    (∀ j < i, ∀ s < J, ν (dst+j*J+s)=((indices m J j).getD s 0 : ℤ)) ∧
    Kept μ ν dst

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain pDigits pDivide : ℕ}
    (hmain : P[pMain]?=some (body pDigits))
    (hdigits : P[pDigits]?=some (LightOutputDecodeDigits.body pDivide))
    (hdivide : P[pDivide]?=some LightOutputDecodeDivide.body)
    {μ : ℕ → ℤ} {N J m dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth) (hm : 1 ≤ m)
    (hsep : dst+N*J ≤ work) (hspace : LightOutputDecodeDigits.space work N ≤ lim.space)
    (hword : (LightOutputDecodeDigits.word N m J : ℤ) ≤ lim.word) :
    Meets lim P pMain d [N,J,m,dst,work] μ (time N J) (fun _ ν =>
      (∀ i < N, ∀ j < J, ν (dst+i*J+j)=((indices m J i).getD j 0 : ℤ)) ∧ Kept μ ν dst) := by
  have hwork : work ≤ lim.space := by unfold LightOutputDecodeDigits.space at hspace; omega
  have hNword : (N : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show N ≤ LightOutputDecodeDigits.word N m J by
      unfold LightOutputDecodeDigits.word; omega)).trans hword
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ N J m dst work) N (LightOutputDecodeDigits.time J N+142)
    ?start ?round ?done ?bound
  case start =>
    refine ⟨0,μ,?_,?_,fun _ _ => rfl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : State))
        ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro j hj; omega
  case round =>
    rintro i _ hi _ ⟨r,ν,rfl,written,kept⟩
    have hrow : dst+i*J+J ≤ work := by
      have hb := Nat.mul_le_mul_right J (show i+1 ≤ N by omega)
      nlinarith
    have hprod : (i : ℤ)*(J : ℤ) ≤ lim.word :=
      (by exact_mod_cast (show i*J ≤ lim.space by omega) :
        (i : ℤ)*(J : ℤ) ≤ lim.space).trans hw
    have hprodNonneg : (0 : ℤ) ≤ (i : ℤ)*(J : ℤ) := by positivity
    have hrun := LightOutputDecodeDigits.meets (d := d+1) (μ := ν)
      (k := i) (J := J) (m := m) (dst := dst+i*J) (work := work) (V := N)
      hdigits hdivide hw (by omega) hm (by omega) hrow hspace hword
    light_call hrun with s ν' ⟨_,row,kept'⟩
    refine ⟨by simp,s,ν',by simp [update_frame_setLocal],?_,?_⟩
    · intro j hj q hq
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · have hb := Nat.mul_le_mul_right J (show j+1 ≤ i by omega)
        exact (kept' _ (by nlinarith)).trans (written j hj q hq)
      · exact row q hq
    · intro a ha
      exact (kept' a (by omega)).trans (kept a ha)
  case done =>
    rintro _ _ ⟨r,ν,rfl,written,kept⟩
    exact ⟨written,kept⟩
  case bound =>
    rintro i _ _ _ ⟨r,ν,rfl,_,_⟩
    simp

def program : Program := [body 1,LightOutputDecodeDigits.body 2,LightOutputDecodeDivide.body]

theorem program_meets {μ : ℕ → ℤ} {N J m dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth) (hm : 1 ≤ m)
    (hsep : dst+N*J ≤ work) (hspace : LightOutputDecodeDigits.space work N ≤ lim.space)
    (hword : (LightOutputDecodeDigits.word N m J : ℤ) ≤ lim.word) :
    Meets lim program 0 d [N,J,m,dst,work] μ (time N J) (fun _ ν =>
      (∀ i < N, ∀ j < J, ν (dst+i*J+j)=((indices m J i).getD j 0 : ℤ)) ∧ Kept μ ν dst) :=
  meets rfl rfl rfl hw hd hm hsep hspace hword

theorem program_length : program.length=3 := rfl

theorem time_bound (N J : ℕ) :
    time N J ≤ 300*(N+1)*(J+1)*(Nat.log 2 (N+1)+2) := by
  have hlog : 2 ≤ Nat.log 2 (N+1)+2 := by omega
  have hinner : J*(100*(Nat.log 2 (N+1)+2)+100)+30+150 ≤
      300*(J+1)*(Nat.log 2 (N+1)+2) := by
    have hscale := Nat.mul_le_mul_left J hlog
    nlinarith
  have hc : 10 ≤ 300*(J+1)*(Nat.log 2 (N+1)+2) := by nlinarith
  unfold time LightOutputDecodeDigits.time LightOutputDecodeDivide.budget
  calc
    _ ≤ N*(300*(J+1)*(Nat.log 2 (N+1)+2))+10 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left N hinner) 10
    _ ≤ (N+1)*(300*(J+1)*(Nat.log 2 (N+1)+2)) := by nlinarith
    _ = _ := by ring

end ThreeSum.LightSourceOccurrenceArray
