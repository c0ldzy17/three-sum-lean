import Submission.ThreeSum.LightOutputDecodeDigits
import Submission.ThreeSum.TernaryCarryCode
import Submission.ThreeSum.LightNatPower

/-!
# Executed binary carry-code table

The ordinary Light program below enumerates integer codes. Each row contains
a terminal zero, the actual big-endian quotient digits, and an executed
initial-zero test returned as its result. Little-endian carry coordinates use the reverse address
`dst + J - j`. The decoder is the checked binary-division program.
-/

namespace ThreeSum.LightTernaryCarryCodes

open Light TernarySignedDigits

set_option maxHeartbeats 2400000
set_option maxRecDepth 9000

def initial (J q : ℕ) : ℕ := if J=0 then 0 else digit 2 q 0
def accepted (J q : ℕ) : ℕ := if initial J q=0 then 1 else 0

def Row (ν : ℕ → ℤ) (dst J q : ℕ) : Prop :=
  ν dst=0 ∧
  (∀ j<J, ν (dst+J-j)=(digit 2 q j : ℤ))

def rowBody (pDecode : ℕ) : Stmt :=
  .call pDecode [v 0,v 1,k 2,v 2 +' k 1,v 3] 4 ;;
  .store (v 2) (k 0) ;;
  .ite (M (v 2 +' v 1) =' k 0)
    (.set 0 (k 1))
    (.set 0 (k 0))

def rowTime (J V : ℕ) : ℕ := LightOutputDecodeDigits.time J V+100
def word (J V : ℕ) : ℕ := LightOutputDecodeDigits.word V 2 J+100
def space (work V : ℕ) : ℕ := LightOutputDecodeDigits.space work V

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}

theorem row_meets {pRow pDecode pDivide q J dst work V : ℕ}
    (hrow : P[pRow]?=some (rowBody pDecode))
    (hdecode : P[pDecode]?=some (LightOutputDecodeDigits.body pDivide))
    (hdivide : P[pDivide]?=some LightOutputDecodeDivide.body)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hq : q ≤ V) (hsep : dst+J+1 ≤ work)
    (hspace : space work V ≤ lim.space)
    (hword : (word J V : ℤ) ≤ lim.word) :
    Meets lim P pRow d [q,J,dst,work] μ (rowTime J V)
      (fun r ν => r=(accepted J q : ℤ) ∧ Row ν dst J q ∧ Kept μ ν dst) := by
  have hword' : (LightOutputDecodeDigits.word V 2 J : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word; omega)).trans hword
  have h1Word : (1 : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word; omega : 1≤word J V)).trans hword
  have hwork : work≤lim.space := by
    unfold space LightOutputDecodeDigits.space at hspace; omega
  have hqWord : (q : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (hq.trans (by unfold word LightOutputDecodeDigits.word; omega))).trans hword
  have hJWord : (J : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (by unfold word LightOutputDecodeDigits.word; omega : J≤word J V)).trans hword
  have h2Word : (2 : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (by unfold word LightOutputDecodeDigits.word; omega : 2≤word J V)).trans hword
  apply Meets.of_body hrow
  unfold rowBody rowTime
  light_call (LightOutputDecodeDigits.meets (d := d+1) (k := q) (J := J)
    (m := 2) (dst := dst+1) (work := work) (V := V)
    hdecode hdivide hw (by omega) (by decide) hq (by omega) hspace hword')
    with r ν ⟨hr,hbits,hkeep⟩
  light_store dst (0 : ℕ)
  have hbits' : ∀ j<J, Function.update ν dst 0 (dst+J-j)=(digit 2 q j : ℤ) := by
    intro j hj
    rw [Function.update_of_ne (by omega)]
    have he := hbits (J-1-j) (by omega)
    rw [OutputDecodeOrder.indices_getD_reverse 2 J q hj] at he
    have ha : dst+1+(J-1-j)=dst+J-j := by omega
    simpa only [ha,digit,quotient] using he
  have hread : Function.update ν dst 0 (dst+J)=(initial J q : ℤ) := by
    by_cases hJ : J=0
    · simp [hJ,initial]
    · simpa [initial,hJ] using hbits' 0 (by omega)
  light_if hy hn : (initial J q : ℤ)=0 using hread
  · have he : initial J q=0 := by exact_mod_cast hy
    light_set (1 : ℕ)
    refine ⟨by simp [accepted,he],⟨by simp,hbits'⟩,?_⟩
    intro a ha
    change Function.update ν dst 0 a=μ a
    rw [Function.update_of_ne (by omega),hkeep _ (by omega)]
  · have he : initial J q≠0 := by exact_mod_cast hn
    light_set (0 : ℕ)
    refine ⟨by simp [accepted,he],⟨by simp,hbits'⟩,?_⟩
    intro a ha
    change Function.update ν dst 0 a=μ a
    rw [Function.update_of_ne (by omega),hkeep _ (by omega)]

theorem initial_eq_digit {J q : ℕ} (hq : q<2^J) : initial J q=digit 2 q 0 := by
  by_cases hJ : J=0
  · subst J
    have hq0 : q=0 := by simpa using hq
    simp [initial,hq0,digit,quotient]
  · simp [initial,hJ]

theorem accepted_iff {J q : ℕ} (hq : q<2^J) :
    accepted J q=1 ↔ digit 2 q 0=0 := by
  simp [accepted,initial_eq_digit hq]

def tableBody (pRow : ℕ) : Stmt :=
  .for 4 (v 0)
    (.call pRow [v 4,v 1,v 2 +' v 4 *' (v 1 +' k 1),v 3] 5) ;;
  .set 0 (v 0)

def tableTime (Q J : ℕ) : ℕ := Q*(rowTime J Q+100)+30

def Table (ν : ℕ → ℤ) (dst J Q : ℕ) : Prop :=
  ∀ q<Q, Row ν (dst+q*(J+1)) J q

def TableInv (μ : ℕ → ℤ) (Q J dst work i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [Q,J,dst,work,i,r],ν⟩ ∧ Table ν dst J i ∧ Kept μ ν dst

theorem table_meets {pTable pRow pDecode pDivide Q J dst work : ℕ}
    (htable : P[pTable]?=some (tableBody pRow))
    (hrow : P[pRow]?=some (rowBody pDecode))
    (hdecode : P[pDecode]?=some (LightOutputDecodeDigits.body pDivide))
    (hdivide : P[pDivide]?=some LightOutputDecodeDivide.body)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+3<lim.depth)
    (hsep : dst+Q*(J+1)≤work)
    (hspace : space work Q≤lim.space)
    (hword : (word J Q : ℤ)≤lim.word) :
    Meets lim P pTable d [Q,J,dst,work] μ (tableTime Q J)
      (fun r ν => r=(Q : ℤ) ∧ Table ν dst J Q ∧ Kept μ ν dst) := by
  have hwork : work≤lim.space := by
    unfold space LightOutputDecodeDigits.space at hspace; omega
  have hQWord : (Q : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (by unfold word LightOutputDecodeDigits.word; omega : Q≤word J Q)).trans hword
  have hJWord : (J : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (by unfold word LightOutputDecodeDigits.word; omega : J≤word J Q)).trans hword
  have h1Word : (1 : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (by unfold word LightOutputDecodeDigits.word; omega : 1≤word J Q)).trans hword
  have hJ1Word : (J : ℤ)+1≤lim.word := by
    have hh : ((J+1 : ℕ) : ℤ)≤(word J Q : ℤ) :=
      Int.ofNat_le.mpr (by unfold word LightOutputDecodeDigits.word; omega)
    exact_mod_cast hh.trans hword
  apply Meets.of_body htable
  unfold tableBody tableTime
  refine Ends.pieceThen (Ends.for
    (T := Q*(rowTime J Q+100)+10)
    (Q := TableInv μ Q J dst work Q) (TableInv μ Q J dst work) Q
    (rowTime J Q+80) ?start ?round ?done ?bound) ?finish
  case start =>
    refine ⟨0,μ,?_,?_,SameOn.refl⟩
    · simp only [update_frame_setLocal]
      exact congrArg (fun loc => (⟨loc,μ⟩ : State))
        (frame_append_zeros [(Q : ℤ),J,dst,work,0] 1).symm
    · intro q hq; omega
  case round =>
    rintro i _ hi _ ⟨r,ν,rfl,hrows,hkeep⟩
    have hstride : (i+1)*(J+1)≤Q*(J+1) :=
      Nat.mul_le_mul_right (J+1) (by omega)
    have hlast : dst+i*(J+1)+J+1≤work := by
      simp only [Nat.add_mul,one_mul] at hstride
      omega
    have hprod : i*(J+1)≤lim.space := by omega
    have hprodWord : (i : ℤ)*((J : ℤ)+1)≤lim.word := by
      exact_mod_cast ((Int.ofNat_le.mpr hprod).trans hw)
    have hprodNonneg : (0 : ℤ)≤(i : ℤ)*((J : ℤ)+1) := by positivity
    have haddrWord : (dst : ℤ)+(i : ℤ)*((J : ℤ)+1)≤lim.word := by
      exact_mod_cast ((Int.ofNat_le.mpr (show dst+i*(J+1)≤lim.space by omega)).trans hw)
    light_call (row_meets (d := d+1) (q := i) (J := J)
      (dst := dst+i*(J+1)) (work := work) (V := Q)
      hrow hdecode hdivide hw (by omega) (by omega) hlast hspace hword)
      with ret ξ ⟨hret,hnew,hpres⟩
    refine ⟨by simp,ret,ξ,by simp [update_frame_setLocal],?_,?_⟩
    · intro q hq
      rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | rfl
      · have hstrideq : (q+1)*(J+1) ≤ i * (J+1) :=
          Nat.mul_le_mul_right (J+1) (by omega)
        simp only [Nat.add_mul,one_mul] at hstrideq
        have hold := hrows q hq
        refine ⟨?_,?_⟩
        · rw [hpres _ (by omega)]
          exact hold.1
        · intro j hj
          rw [hpres _ (by omega)]
          exact hold.2 j hj
      · exact hnew
    · intro a ha
      rw [hpres _ (by omega),hkeep _ ha]
  case done =>
    rintro _ _ ⟨r,ν,rfl,hrows,hkeep⟩
    exact ⟨r,ν,rfl,hrows,hkeep⟩
  case bound =>
    rintro i _ hi _ ⟨r,ν,rfl,_,_⟩
    light_side
  case finish =>
    rintro _ ⟨r,ν,rfl,hrows,hkeep⟩
    light_set (Q : ℕ)
    exact ⟨rfl,hrows,hkeep⟩

def body (pPower pTable : ℕ) : Stmt :=
  .call pPower [k 2,v 0] 3 ;;
  .call pTable [v 3,v 0,v 1,v 2] 4 ;;
  .set 0 (v 3)

def time (J : ℕ) : ℕ :=
  LightNatPower.time J+tableTime (2^J) J+100

theorem meets {pMain pPower pTable pRow pDecode pDivide J dst work : ℕ}
    (hmain : P[pMain]?=some (body pPower pTable))
    (hpower : P[pPower]?=some LightNatPower.body)
    (htable : P[pTable]?=some (tableBody pRow))
    (hrow : P[pRow]?=some (rowBody pDecode))
    (hdecode : P[pDecode]?=some (LightOutputDecodeDigits.body pDivide))
    (hdivide : P[pDivide]?=some LightOutputDecodeDivide.body)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+4<lim.depth)
    (hsep : dst+2^J*(J+1)≤work)
    (hspace : space work (2^J)≤lim.space)
    (hword : (word J (2^J) : ℤ)≤lim.word) :
    Meets lim P pMain d [J,dst,work] μ (time J)
      (fun r ν => r=(2^J : ℕ) ∧ Table ν dst J (2^J) ∧ Kept μ ν dst) := by
  have hwork : work≤lim.space := by
    unfold space LightOutputDecodeDigits.space at hspace; omega
  have hQWord : ((2^J : ℕ) : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (by unfold word LightOutputDecodeDigits.word; omega : 2^J≤word J (2^J))).trans hword
  have hJWord : (J : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (by unfold word LightOutputDecodeDigits.word; omega : J≤word J (2^J))).trans hword
  have h2Word : (2 : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (by unfold word LightOutputDecodeDigits.word; omega : 2≤word J (2^J))).trans hword
  have hpow (i : ℕ) (hi : i≤J) : ((2^i : ℕ) : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) hi)).trans hQWord
  apply Meets.of_body hmain
  unfold body time
  light_call (LightNatPower.meets (d := d+1) hpower μ hJWord hpow)
    with Q ν ⟨hQ,hmem⟩
  subst ν
  light_call (table_meets (d := d+1) (Q := 2^J) (J := J)
    (dst := dst) (work := work) htable hrow hdecode hdivide hw (by omega)
    hsep hspace hword) using hQ
    with ret ξ ⟨hret,hrows,hkeep⟩
  light_set (2^J : ℕ) using hQ
  exact ⟨rfl,hrows,hkeep⟩

def program : Program :=
  [body 1 2,LightNatPower.body,tableBody 3,rowBody 4,
    LightOutputDecodeDigits.body 5,LightOutputDecodeDivide.body]

theorem program_meets {J dst work : ℕ}
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+4<lim.depth)
    (hsep : dst+2^J*(J+1)≤work)
    (hspace : space work (2^J)≤lim.space)
    (hword : (word J (2^J) : ℤ)≤lim.word) :
    Meets lim program 0 d [J,dst,work] μ (time J)
      (fun r ν => r=(2^J : ℕ) ∧ Table ν dst J (2^J) ∧ Kept μ ν dst) :=
  meets rfl rfl rfl rfl rfl rfl hw hd hsep hspace hword

theorem row_carry_read {ν : ℕ → ℤ} {dst J q : ℕ}
    (h : Row ν dst J q) (i : Fin (J+1)) :
    ν (dst+J-i.val)=((TernaryCarryCode.carryFromCode J q i).val : ℤ) := by
  by_cases hi : i.val<J
  · simpa only [TernaryCarryCode.carryFromCode,dif_pos hi] using h.2 i.val hi
  · have he : i.val=J := by omega
    simp only [TernaryCarryCode.carryFromCode,dif_neg hi]
    simpa only [he,Nat.add_sub_cancel,Fin.val_zero,Int.natCast_zero] using h.1

theorem table_covers {ν : ℕ → ℤ} {dst J : ℕ}
    (h : Table ν dst J (2^J)) {c : CarryWord J}
    (hc : ValidCarry c) :
    ∃ q<2^J, accepted J q=1 ∧ ∀ i : Fin (J+1),
      ν (dst+q*(J+1)+J-i.val)=((c i).val : ℤ) := by
  refine ⟨TernaryCarryCode.codeOfCarry c,TernaryCarryCode.codeOfCarry_lt c,?_,?_⟩
  · exact (accepted_iff (TernaryCarryCode.codeOfCarry_lt c)).mpr
      (TernaryCarryCode.codeOfCarry_initial hc)
  · intro i
    have hr := row_carry_read (h _ (TernaryCarryCode.codeOfCarry_lt c)) i
    rw [TernaryCarryCode.carryFromCode_code hc] at hr
    exact hr

theorem log_code_bound (J : ℕ) : Nat.log 2 (2^J+1)≤J+1 := by
  have hp : 1≤2^J := Nat.one_le_pow J 2 (by decide)
  have he : 2^J+1≤2^(J+1) := by rw [pow_succ]; omega
  have hl := Nat.log_mono_right (b := 2) he
  simpa only [Nat.log_pow (by decide : 1<(2 : ℕ))] using hl

theorem time_bound (J : ℕ) : time J≤2000*2^J*(J+2)^2 := by
  have hlog := log_code_bound J
  have hmul := Nat.mul_le_mul_left J hlog
  have hrow : rowTime J (2^J)+100≤1000*(J+2)^2 := by
    unfold rowTime LightOutputDecodeDigits.time LightOutputDecodeDivide.budget
    nlinarith
  have hQ : 1≤2^J := Nat.one_le_pow J 2 (by decide)
  have ht := Nat.mul_le_mul_left (2^J) hrow
  have hlow : 20*J+150≤1000*(J+2)^2 := by nlinarith
  have hscale := Nat.mul_le_mul_right (1000*(J+2)^2) hQ
  unfold time tableTime LightNatPower.time
  nlinarith

theorem space_bound (work J : ℕ) : space work (2^J)≤work+J+3 := by
  have hh := log_code_bound J
  unfold space LightOutputDecodeDigits.space
  omega

end ThreeSum.LightTernaryCarryCodes
