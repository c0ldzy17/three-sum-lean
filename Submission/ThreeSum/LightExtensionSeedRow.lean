import Submission.ThreeSum.LightCoefficientDecode

namespace ThreeSum.LightExtensionSeedRow
open Light
set_option maxHeartbeats 2000000

def trajectory (mul : ℕ → ℕ → ℕ) (x y : ℕ) : ℕ → ℕ
  | 0 => y
  | i+1 => mul (trajectory mul x y i) x

theorem trajectory_lt (mul : ℕ → ℕ → ℕ) {q x y : ℕ}
    (hx : x<q) (hy : y<q) (hm : ∀ a<q, ∀ b<q, mul a b<q) (i : ℕ) :
    trajectory mul x y i<q := by
  induction i with
  | zero => exact hy
  | succ i hi => exact hm _ hi x hx

def roundBody (pDigit : ℕ) : Stmt :=
  .call pDigit [v 7,k 1,v 2] 9 ;;
  .store (v 5 +' v 8) (v 9) ;;
  .set 7 (M (v 0 +' v 7 *' v 1 +' v 3))

def body (pDigit : ℕ) : Stmt :=
  .set 7 (v 4) ;; .for 8 (v 6) (roundBody pDigit) ;; .set 0 (v 7)

def time (len q : ℕ) : ℕ := len*(LightRadixDigit.time q+100)+30

def word (len q p : ℕ) : ℕ := 10*(q*q+q+p+len+10)

def Inv (μ : ℕ → ℤ) (table q p x y dst len : ℕ) (mul : ℕ → ℕ → ℕ)
    (i : ℕ) (σ : State) : Prop :=
  ∃ (old : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [table,q,p,x,y,dst,len,trajectory mul x y i,i,old],ν⟩ ∧
    (∀ j < i, ν (dst+j)=(((trajectory mul x y j)%p : ℕ) : ℤ)) ∧ SameOutside μ ν dst len

variable {lim : Limits} {P : Program} {depth : ℕ}

theorem meets {proc pDigit pDivide table q p x y dst len : ℕ}
    (hp : P[proc]?=some (body pDigit))
    (hdigit : P[pDigit]?=some (LightRadixDigit.body pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (μ : ℕ → ℤ) (mul : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+1<lim.depth)
    (hx : x<q) (hy : y<q) (hmod : 0<p)
    (htable : table+q*q≤dst) (hspace : dst+len≤lim.space)
    (hread : ∀ a<q, ∀ b<q, μ (table+a*q+b)=(mul a b : ℤ))
    (hmul : ∀ a<q, ∀ b<q, mul a b<q)
    (hword : (word len q p : ℤ)≤lim.word) :
    Meets lim P proc depth [table,q,p,x,y,dst,len] μ (time len q)
      (fun z ν => z=(trajectory mul x y len : ℤ) ∧
        (∀ i<len, ν (dst+i)=(((trajectory mul x y i)%p : ℕ) : ℤ)) ∧ SameOutside μ ν dst len) := by
  have hb (z : ℕ) (hz : z≤word len q p) : (z : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr hz).trans hword
  have hqWord := hb q (by unfold word; omega)
  have hpWord := hb p (by unfold word; omega)
  have hyWord := hb y (by unfold word; omega)
  have hxWord := hb x (by unfold word; omega)
  have h1 : (1 : ℤ)≤lim.word := by unfold word at hword; omega
  have hrun (i : ℕ) : trajectory mul x y i<q := trajectory_lt mul hx hy hmul i
  have hrunWord (i : ℕ) : (trajectory mul x y i : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (Nat.le_of_lt (hrun i))).trans hqWord
  apply Meets.of_body hp
  unfold body time
  light_set (y : ℕ)
  refine Ends.pieceThen (Ends.for
    (T := len*(LightRadixDigit.time q+100)+6)
    (Q := Inv μ table q p x y dst len mul len)
    (Inv μ table q p x y dst len mul) len (LightRadixDigit.time q+90)
    ?start ?round ?done ?bound) ?finish
  case start =>
    refine ⟨0,μ,?_,?_,SameOutside.refl⟩
    · simp only [trajectory]
      exact congrArg (fun loc => (⟨loc,μ⟩ : State))
        ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro i hi; omega
  case round =>
    rintro i _ hi _ ⟨old,ν,rfl,written,kept⟩
    have hz := hrun i
    have hzWord := hrunWord i
    have hnext := hrunWord (i+1)
    have hm : trajectory mul x y i*q+x<q*q := by nlinarith
    have hprod : trajectory mul x y i*q≤q*q := by nlinarith
    have hprodWord := hb (trajectory mul x y i*q) (by unfold word; omega)
    have hread' : ν (table+trajectory mul x y i*q+x)=(trajectory mul x y (i+1) : ℤ) := by
      rw [kept _ (Or.inl (by omega)),hread _ hz x hx]
      rfl
    have hcallWord : (LightRadixDigit.word (trajectory mul x y i) 1 p : ℤ)≤lim.word := by
      apply hb
      unfold LightRadixDigit.word word
      omega
    have htime : LightRadixDigit.time (trajectory mul x y i)≤LightRadixDigit.time q := by
      unfold LightRadixDigit.time
      omega
    have hrem := Nat.mod_lt (trajectory mul x y i) hmod
    have hremWord := (Int.ofNat_le.mpr (Nat.le_of_lt hrem)).trans hpWord
    unfold roundBody
    light_call (LightRadixDigit.meets (d := depth+1) (k := trajectory mul x y i) (b := 1) (p := p)
      hdigit hdivide ν (by omega) hcallWord)
      using LightRadixDigit.time with val ν₁ ⟨hval,hν₁⟩
    subst ν₁
    have hv : val=(((trajectory mul x y i)%p : ℕ) : ℤ) := by simpa using hval
    light_store (dst+i) ((trajectory mul x y i)%p : ℕ) using hv,LightRadixDigit.time
    have haddr : ((table : ℤ)+(trajectory mul x y i : ℤ)*(q : ℤ)+(x : ℤ)).toNat=
        table+trajectory mul x y i*q+x := by norm_cast
    have hread'' (value : ℤ) : Function.update ν (dst+i) value
        (table+trajectory mul x y i*q+x)=(trajectory mul x y (i+1) : ℤ) := by
      rw [Function.update_of_ne (by omega),hread']
    light_set (trajectory mul x y (i+1) : ℕ) using haddr,hread'',LightRadixDigit.time
    refine ⟨by simp,val,Function.update ν (dst+i) (((trajectory mul x y i)%p : ℕ) : ℤ),
      by simp [update_frame_setLocal],?_,kept.update ⟨by omega,by omega⟩ _⟩
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Function.update_of_ne (by omega)]
      exact written j hj
    · simp
  case done => rintro _ _ h; exact h
  case bound => rintro i _ _ _ ⟨old,ν,rfl,_,_⟩; light_side
  case finish =>
    rintro _ ⟨old,ν,rfl,written,kept⟩
    have hz := hrunWord len
    light_set (trajectory mul x y len : ℕ)
    exact ⟨rfl,written,kept⟩

def program : Program := [body 1,LightRadixDigit.body 2,LightSmallDivide.body]

end ThreeSum.LightExtensionSeedRow
