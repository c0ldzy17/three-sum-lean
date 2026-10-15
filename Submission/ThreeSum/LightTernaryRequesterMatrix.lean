import Submission.ThreeSum.LightTernaryOriginalRequester
import Submission.ThreeSum.LightTernaryCarryCodes
import Submission.ThreeSum.LightTernarySignedMatrix
import Submission.ThreeSum.TernarySignedLayout

/-! Executed original-position × literal-carry requester matrix. -/
namespace ThreeSum.LightTernaryRequesterMatrix
open Light TernarySignedDigits TernarySignedReduction
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000

/-- Inner arguments: source,U,J,radix,carry,Q,positions,matrix,work,i. -/
def round (pRequester : ℕ) : Stmt :=
  .store (v 6 +' v 9 *' v 5 +' v 10) (v 9) ;;
  .call pRequester [M (v 0 +' v 9),v 1,v 3,v 2,
    v 7 +' (v 9 *' v 5 +' v 10) *' (v 2 +' k 2),
    v 4 +' v 10 *' (v 2 +' k 1),v 8] 11

def innerBody (pRequester : ℕ) : Stmt := .for 10 (v 5) (round pRequester)

/-- Outer arguments: source,n,U,J,radix,carry,Q,positions,matrix,work. -/
def body (pInner : ℕ) : Stmt :=
  .for 10 (v 1) (.call pInner [v 0,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10] 11)

def innerTime (Q J U : ℕ) : ℕ := Q*(LightTernaryOriginalRequester.time J U+300)+30

def time (n Q J U : ℕ) : ℕ := n*(innerTime Q J U+200)+30

def Entries (μ : ℕ → ℤ) (positions matrix J Q len U radix : ℕ) (f : ℕ → ℤ) : Prop :=
  ∀ r<len,
    LightTernarySignedRow.Row μ (matrix+r*(J+2)) J
      (requesterRaw U radix J (f (r/Q)) (TernaryCarryCode.carryFromCode J (r%Q))) ∧
    μ (positions+r)=(r/Q : ℕ)

structure Procs (P : Program) (main : ℕ) where
  inner : ℕ
  requester : ℕ
  mainBody : P[main]?=some (body inner)
  innerBody : P[inner]?=some (innerBody requester)
  requesterProcs : LightTernaryOriginalRequester.Procs P requester

variable {lim : Limits} {P : Program} {depth : ℕ}

theorem carry_read {μ : ℕ → ℤ} {carry J Q q : ℕ}
    (H : LightTernaryCarryCodes.Table μ carry J Q) (hq : q<Q) :
    ∀k≤J, μ (carry+q*(J+1)+k)=carryAt (TernaryCarryCode.carryFromCode J q) (J-k) := by
  intro k hk
  have hrow := H q hq
  by_cases hz : k=0
  · subst k
    simpa [carryAt,TernaryCarryCode.carryFromCode] using hrow.1
  · have hj : J-k<J := by omega
    have hh := hrow.2 (J-k) hj
    have he : carry+q*(J+1)+J-(J-k)=carry+q*(J+1)+k := by omega
    rw [he] at hh
    simpa [carryAt,TernaryCarryCode.carryFromCode,hj,show J-k<J+1 by omega] using hh

def InnerInv (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (src U J radix carry Q positions matrix work i j : ℕ) (σ : State) : Prop :=
  ∃ result : ℤ, ∃ ν : ℕ → ℤ,
    σ=⟨frame [src,U,J,radix,carry,Q,positions,matrix,work,i,j,result],ν⟩ ∧
    Entries ν positions matrix J Q (i*Q+j) U radix f ∧ Kept μ ν positions

theorem Procs.inner_meets {main : ℕ} (S : Procs P main)
    {src n U J radix carry Q positions matrix work i : ℕ} (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+4<lim.depth)
    (hb : 1<radix) (hQ : 0<Q) (hi : i<n)
    (hsrc : src+n≤positions) (hcarry : carry+Q*(J+1)≤positions)
    (hpos : positions+n*Q≤matrix) (hmat : matrix+n*Q*(J+2)≤work)
    (hspace : LightTernarySignedRow.space work (3*U)≤lim.space)
    (hword : (LightTernarySignedRow.word (3*U) radix J : ℤ)≤lim.word)
    (hread : ∀a<n, μ (src+a)=f a) (hvalues : ∀a<n, |f a|≤(U : ℤ))
    (hCarries : LightTernaryCarryCodes.Table μ carry J Q)
    (hOld : Entries μ positions matrix J Q (i*Q) U radix f) :
    Meets lim P S.inner depth [src,U,J,radix,carry,Q,positions,matrix,work,i] μ
      (innerTime Q J U)
      (fun _ ν => Entries ν positions matrix J Q ((i+1)*Q) U radix f ∧ Kept μ ν positions) := by
  have hwsp : work≤lim.space := by
    unfold LightTernarySignedRow.space LightOutputDecodeDigits.space at hspace; omega
  have hJWord : ((J+2 : ℕ) : ℤ)≤lim.word := by
    have hh : J+2≤LightTernarySignedRow.word (3*U) radix J := by
      unfold LightTernarySignedRow.word LightOutputDecodeDigits.word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hQle : Q≤Q*(J+1) := Nat.le_mul_of_pos_right Q (by omega)
  have hQword : (Q : ℤ)≤lim.word := (Int.ofNat_le.mpr (show Q≤lim.space by omega)).trans hw
  have hSmallWord := hword
  unfold LightTernarySignedRow.word LightOutputDecodeDigits.word at hSmallWord
  have hn : n≤n*Q := Nat.le_mul_of_pos_right n hQ
  have hiQ : (i+1)*Q≤n*Q := Nat.mul_le_mul_right Q (by omega)
  have hiWord : (i : ℤ)≤lim.word := (Int.ofNat_le.mpr (show i≤lim.space by omega)).trans hw
  have hval := hvalues i hi
  have hvalBounds := abs_le.mp hval
  apply Meets.of_body S.innerBody
  unfold LightTernaryRequesterMatrix.innerBody innerTime
  refine Ends.for (InnerInv μ f src U J radix carry Q positions matrix work i) Q
    (LightTernaryOriginalRequester.time J U+280) ?start ?round ?done ?bound (hT := by light_time)
  case start =>
    refine ⟨0,μ,?_,?_,SameOn.refl⟩
    · simp only [update_frame_setLocal]
      exact congrArg (fun loc => (⟨loc,μ⟩ : State)) (frame_append_zeros _ 1).symm
    · simpa using hOld
  case round =>
    rintro j _ hj _ ⟨result,ν,rfl,hEntries,hKeep⟩
    let r := i*Q+j
    have hr : r<n*Q := by dsimp [r]; nlinarith
    have hdiv : r/Q=i := by
      dsimp only [r]
      rw [Nat.add_comm,Nat.add_mul_div_right _ _ hQ,Nat.div_eq_of_lt hj,Nat.zero_add]
    have hmod : r%Q=j := by simp [r,Nat.add_mod,Nat.mod_eq_of_lt hj]
    have hrowEnd : matrix+r*(J+2)+J+2≤work := by
      have hh := Nat.mul_le_mul_right (J+2) (show r+1≤n*Q by omega)
      rw [Nat.add_mul] at hh; simp only [one_mul] at hh; omega
    have hrOffset : (i : ℤ)*Q+j≤lim.word := by
      exact_mod_cast ((Int.ofNat_le.mpr (show i*Q+j≤lim.space by dsimp [r] at hr; omega)).trans hw)
    have hiQWord : (i : ℤ)*Q≤lim.word := by omega
    have hposWord : (positions : ℤ)+(i : ℤ)*Q+j≤lim.word := by
      exact_mod_cast ((Int.ofNat_le.mpr (show positions+i*Q+j≤lim.space by dsimp [r] at hr; omega)).trans hw)
    unfold round
    light_store (positions+r) (i : ℕ) using r
    let ξ := Function.update ν (positions+r) (i : ℤ)
    have hOldRows : Entries ξ positions matrix J Q r U radix f := by
      intro s hs
      rcases hEntries s (by dsimp [r] at hs; exact hs) with ⟨hrow,hp⟩
      refine ⟨?_,?_⟩
      · rcases hrow with ⟨hv,h0,h1⟩
        refine ⟨?_,?_,?_⟩
        · intro k
          dsimp [ξ]
          rw [Function.update_of_ne (by have := k.isLt; omega)]
          exact hv k
        · dsimp [ξ]; rw [Function.update_of_ne (by omega)]; exact h0
        · dsimp [ξ]; rw [Function.update_of_ne (by omega)]; exact h1
      · dsimp [ξ]; rw [Function.update_of_ne (by omega)]; exact hp
    have hcell : ξ (src+i)=f i := by
      dsimp [ξ]
      rw [Function.update_of_ne (by omega),hKeep _ (by omega),hread i hi]
    have hcRead : ∀k≤J, ξ (carry+j*(J+1)+k)=carryAt (TernaryCarryCode.carryFromCode J j) (J-k) := by
      intro k hk
      have hcB : carry+j*(J+1)+k<positions := by
        have hh := Nat.mul_le_mul_right (J+1) (show j+1≤Q by omega)
        rw [Nat.add_mul] at hh; simp only [one_mul] at hh; omega
      dsimp [ξ]
      rw [Function.update_of_ne (by omega),hKeep _ hcB]
      exact carry_read hCarries hj k hk
    have hrowMul : (i : ℤ)*Q+j≥0 := by positivity
    have hrowAddr : (matrix : ℤ)+((i : ℤ)*Q+j)*((J : ℤ)+2)≤lim.word := by
      exact_mod_cast ((Int.ofNat_le.mpr (show matrix+(i*Q+j)*(J+2)≤lim.space by dsimp [r] at hrowEnd; omega)).trans hw)
    have hrowProd : ((i : ℤ)*Q+j)*((J : ℤ)+2)≤lim.word := by omega
    have hcEnd : carry+j*(J+1)+J+1≤matrix+r*(J+2) := by
      have hh := Nat.mul_le_mul_right (J+1) (show j+1≤Q by omega)
      rw [Nat.add_mul] at hh; simp only [one_mul] at hh; omega
    have hcAddr : (carry : ℤ)+(j : ℤ)*((J : ℤ)+1)≤lim.word := by
      exact_mod_cast ((Int.ofNat_le.mpr (show carry+j*(J+1)≤lim.space by omega)).trans hw)
    have hcProd : (j : ℤ)*((J : ℤ)+1)≤lim.word := by omega
    have hrowProdNonneg : 0≤((i : ℤ)*Q+j)*((J : ℤ)+2) := by positivity
    have hcProdNonneg : 0≤(j : ℤ)*((J : ℤ)+1) := by positivity
    have hcall := S.requesterProcs.meets (d := depth+1) (μ := ξ) (U := U) (radix := radix) (J := J)
      (dst := matrix+r*(J+2)) (carry := carry+j*(J+1)) (work := work)
      (f i) (TernaryCarryCode.carryFromCode J j) hw (by omega) hb hval hcEnd hrowEnd hspace hword hcRead
    have hcell' := hcell
    dsimp only [ξ,r] at hcell'
    light_call hcall using r,hcell' with ret η ⟨hNew,hPres⟩
    refine ⟨by simp,ret,η,by simp [update_frame_setLocal],?_,?_⟩
    · intro s hs
      change s<r+1 at hs
      rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
      · rcases hOldRows s hs with ⟨hrow,hp⟩
        refine ⟨LightTernarySignedMatrix.row_keep hrow hPres ?_,?_⟩
        · have hh := Nat.mul_le_mul_right (J+2) (show s+1≤r by omega)
          rw [Nat.add_mul] at hh; simp only [one_mul] at hh; omega
        · exact (hPres _ (by omega)).trans hp
      · refine ⟨?_,?_⟩
        · simpa only [hdiv,hmod] using hNew
        · rw [hPres _ (by omega)]
          simp [ξ,hdiv]
    · intro x hx
      rw [hPres x (by omega)]
      change ξ x=μ x
      dsimp [ξ]
      rw [Function.update_of_ne (by omega),hKeep x hx]
  case done =>
    rintro _ _ ⟨r,ν,rfl,H,K⟩
    exact ⟨by simpa only [Nat.add_mul,one_mul] using H,K⟩
  case bound => rintro j _ hj _ ⟨r,ν,rfl,H,K⟩; light_side


def Inv (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (src n U J radix carry Q positions matrix work i : ℕ) (σ : State) : Prop :=
  ∃ result : ℤ, ∃ ν : ℕ → ℤ,
    σ=⟨frame [src,n,U,J,radix,carry,Q,positions,matrix,work,i,result],ν⟩ ∧
    Entries ν positions matrix J Q (i*Q) U radix f ∧ Kept μ ν positions

theorem Procs.meets {main : ℕ} (S : Procs P main)
    {src n U J radix carry Q positions matrix work : ℕ} (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+5<lim.depth)
    (hb : 1<radix) (hQ : 0<Q)
    (hsrc : src+n≤positions) (hcarry : carry+Q*(J+1)≤positions)
    (hpos : positions+n*Q≤matrix) (hmat : matrix+n*Q*(J+2)≤work)
    (hspace : LightTernarySignedRow.space work (3*U)≤lim.space)
    (hword : (LightTernarySignedRow.word (3*U) radix J : ℤ)≤lim.word)
    (hread : ∀a<n, μ (src+a)=f a) (hvalues : ∀a<n, |f a|≤(U : ℤ))
    (hCarries : LightTernaryCarryCodes.Table μ carry J Q) :
    Meets lim P main depth [src,n,U,J,radix,carry,Q,positions,matrix,work] μ
      (time n Q J U)
      (fun _ ν => Entries ν positions matrix J Q (n*Q) U radix f ∧ Kept μ ν positions) := by
  have hwsp : work≤lim.space := by
    unfold LightTernarySignedRow.space LightOutputDecodeDigits.space at hspace; omega
  have hQle : Q≤Q*(J+1) := Nat.le_mul_of_pos_right Q (by omega)
  have hn : n≤n*Q := Nat.le_mul_of_pos_right n hQ
  have hSmallWord := hword
  unfold LightTernarySignedRow.word LightOutputDecodeDigits.word at hSmallWord
  apply Meets.of_body S.mainBody
  unfold body time
  refine Ends.for (Inv μ f src n U J radix carry Q positions matrix work) n
    (innerTime Q J U+180) ?start ?round ?done ?bound (hT := by light_time)
  case start =>
    refine ⟨0,μ,?_,?_,SameOn.refl⟩
    · simp only [update_frame_setLocal]
      exact congrArg (fun loc => (⟨loc,μ⟩ : State)) (frame_append_zeros _ 1).symm
    · intro r hr; simp at hr
  case round =>
    rintro i _ hi _ ⟨result,ν,rfl,H,K⟩
    have hread' : ∀a<n, ν (src+a)=f a := by
      intro a ha; rw [K _ (by omega),hread a ha]
    have hCarries' : LightTernaryCarryCodes.Table ν carry J Q := by
      intro q hq
      rcases hCarries q hq with ⟨h0,hbits⟩
      have hEnd : carry+q*(J+1)+J+1≤positions := by
        have hh := Nat.mul_le_mul_right (J+1) (show q+1≤Q by omega)
        rw [Nat.add_mul] at hh; simp only [one_mul] at hh; omega
      refine ⟨?_,?_⟩
      · rw [K _ (by omega)]; exact h0
      · intro j hj
        rw [K _ (by omega)]; exact hbits j hj
    have hcall := S.inner_meets (depth := depth+1) (n := n) ν f hw (by omega) hb hQ hi
      hsrc hcarry hpos hmat hspace hword hread' hvalues hCarries' H
    light_call hcall with ret ξ ⟨hEntries,hKeep⟩
    exact ⟨by simp,ret,ξ,by simp [update_frame_setLocal],hEntries,fun x hx => (hKeep x hx).trans (K x hx)⟩
  case done => rintro _ _ ⟨r,ν,rfl,H,K⟩; exact ⟨H,K⟩
  case bound => rintro i _ hi _ ⟨r,ν,rfl,H,K⟩; light_side

/-- Every valid carry and original position has its literal emitted row. -/
theorem entries_complete {μ : ℕ → ℤ} {positions matrix J n U radix : ℕ} {f : ℕ → ℤ}
    (H : Entries μ positions matrix J (2^J) (n*2^J) U radix f)
    {i : ℕ} (hi : i<n) (c : CarryWord J) (hc : ValidCarry c) :
    ∃r<n*2^J, LightTernarySignedRow.Row μ (matrix+r*(J+2)) J (requesterRaw U radix J (f i) c) ∧
      μ (positions+r)=(i : ℤ) := by
  let q := TernaryCarryCode.codeOfCarry c
  have hq : q<2^J := TernaryCarryCode.codeOfCarry_lt c
  have hQ : 0<2^J := pow_pos (by decide) _
  let r := i*2^J+q
  have hr : r<n*2^J := by dsimp [r]; nlinarith
  have hdiv : r/(2^J)=i := by
    dsimp only [r]
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hQ,Nat.div_eq_of_lt hq,Nat.zero_add]
  have hmod : r%(2^J)=q := by simp [r,Nat.add_mod,Nat.mod_eq_of_lt hq]
  refine ⟨r,hr,?_⟩
  have hecarry : TernaryCarryCode.carryFromCode J q=c := TernaryCarryCode.carryFromCode_code hc
  simpa only [hdiv,hmod,hecarry] using H r hr

def program : Program := LightTernaryOriginalRequester.program++[innerBody 0,body 6]

@[simp] theorem program_length : program.length=8 := rfl

def procs : Procs program 7 where
  inner := 6
  requester := 0
  mainBody := rfl
  innerBody := rfl
  requesterProcs := {
    pRow := 1,pApply := 4,pLinear := 5,
    row := ⟨2,3,rfl,rfl,rfl⟩,
    correction := rfl,linear := rfl,main := rfl }


theorem time_bound (n Q J U : ℕ) :
    time n Q J U≤1000*n*Q*(J+1)*(Nat.log 2 (3*U+1)+2)+230*n+30 := by
  have hlog : 2≤Nat.log 2 (3*U+1)+2 := by omega
  have hrow : LightTernaryOriginalRequester.time J U+300≤
      1000*(J+1)*(Nat.log 2 (3*U+1)+2) := by
    unfold LightTernaryOriginalRequester.time LightTernarySignedRow.time
      LightOutputDecodeDigits.time LightOutputDecodeDivide.budget LightTernaryCarryApply.time LightArray.linearTime
    nlinarith
  have h := Nat.mul_le_mul_left n (Nat.mul_le_mul_left Q hrow)
  unfold time innerTime
  nlinarith


/-- Literal row-major features in the same physical coordinate order as both source matrices. -/
def value (U radix J Q : ℕ) (f : ℕ → ℤ) (row coordinate : ℕ) : ℤ :=
  TernarySignedLayout.feature
    (requesterRaw U radix J (f (row/Q)) (TernaryCarryCode.carryFromCode J (row%Q)))
    (TernarySignedLayout.offset J coordinate)

theorem entries_read {μ : ℕ → ℤ} {positions matrix J Q len U radix : ℕ} {f : ℕ → ℤ}
    (H : Entries μ positions matrix J Q len U radix f) :
    (∀row<len, ∀coordinate<J+2,
      μ (matrix+row*(J+2)+coordinate)=value U radix J Q f row coordinate) ∧
      (∀row<len, μ (positions+row)=(row/Q : ℕ)) := by
  refine ⟨?_,fun row hr => (H row hr).2⟩
  intro row hr coordinate hc
  exact TernarySignedLayout.row_physical_read (H row hr).1 hc

end ThreeSum.LightTernaryRequesterMatrix
