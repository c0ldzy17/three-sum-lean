import Submission.ThreeSum.LightPolynomialCoefficient

namespace ThreeSum.LightPolynomialProductCheck
open Light
set_option maxHeartbeats 2000000
noncomputable local instance (Q : Prop) : Decidable Q := Classical.propDecidable Q

abbrev coefficient := LightPolynomialCoefficient.coefficient

def Valid (p : ℕ) (f g expected : ℕ → ℕ) (n m len : ℕ) : Prop :=
  ∀ k<len, expected k=coefficient p f g n m k

theorem valid_succ (p : ℕ) (f g expected : ℕ → ℕ) (n m len : ℕ) :
    Valid p f g expected n m (len+1) ↔
      Valid p f g expected n m len ∧ expected len=coefficient p f g n m len := by
  constructor
  · intro h; exact ⟨fun k hk => h k (by omega),h len (by omega)⟩
  · rintro ⟨h,he⟩ k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact h k hk
    · exact he

noncomputable def flag (p : ℕ) (f g expected : ℕ → ℕ) (n m len : ℕ) : ℤ :=
  if Valid p f g expected n m len then 1 else 0

theorem flag_zero (p : ℕ) (f g expected : ℕ → ℕ) (n m : ℕ) :
    flag p f g expected n m 0=1 := by simp [flag,Valid]

theorem flag_bounds (p : ℕ) (f g expected : ℕ → ℕ) (n m len : ℕ) :
    0≤flag p f g expected n m len ∧ flag p f g expected n m len≤1 := by
  unfold flag
  split_ifs <;> omega

def roundBody (pCoefficient : ℕ) : Stmt :=
  .call pCoefficient [v 0,v 1,v 3,v 4,v 8,v 6] 9 ;;
  .ite (.eq (v 9) (M (v 2 +' v 8))) .skip (.set 7 (k 0))

def body (pCoefficient : ℕ) : Stmt :=
  .set 7 (k 1) ;; .for 8 (v 5) (roundBody pCoefficient) ;; .set 0 (v 7)

def time (n p len : ℕ) : ℕ := len*(LightPolynomialCoefficient.reducedTime n p+100)+30

def Inv (μ : ℕ → ℤ) (srcA srcB dst n m len p : ℕ) (f g expected : ℕ → ℕ)
    (i : ℕ) (σ : State) : Prop :=
  ∃ r : ℤ, σ=⟨frame [srcA,srcB,dst,n,m,len,p,flag p f g expected n m i,i,r],μ⟩

variable {lim : Limits} {P : Program} {depth : ℕ}

theorem meets {proc pCoefficient pRaw pDigit pDivide srcA srcB dst n m len p : ℕ}
    (hp : P[proc]?=some (body pCoefficient))
    (hcoeff : P[pCoefficient]?=some (LightPolynomialCoefficient.reducedBody pRaw pDigit))
    (hraw : P[pRaw]?=some LightPolynomialCoefficient.body)
    (hdigit : P[pDigit]?=some (LightRadixDigit.body pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (μ : ℕ → ℤ) (f g expected : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+2<lim.depth)
    (hA : srcA+n≤lim.space) (hB : srcB+m≤lim.space) (hD : dst+len≤lim.space)
    (hreadA : ∀ i<n, μ (srcA+i)=(f i : ℤ))
    (hreadB : ∀ i<m, μ (srcB+i)=(g i : ℤ))
    (hreadD : ∀ i<len, μ (dst+i)=(expected i : ℤ))
    (hf : ∀ i<n, f i<p) (hg : ∀ i<m, g i<p)
    (hword : ((20*((n+1)*(p+1)^2+len+m+10) : ℕ) : ℤ)≤lim.word) :
    Meets lim P proc depth [srcA,srcB,dst,n,m,len,p] μ (time n p len)
      (fun r ν => r=flag p f g expected n m len ∧ ν=μ) := by
  have hpp : (p : ℤ)≤lim.word := by
    have hh : p≤20*((n+1)*(p+1)^2+len+m+10) := by nlinarith
    exact (Int.ofNat_le.mpr hh).trans hword
  have hone : (1 : ℤ)≤lim.word := by omega
  apply Meets.of_body hp
  unfold body time
  light_set (1 : ℕ)
  refine Ends.pieceThen (Ends.for
    (T := len*(LightPolynomialCoefficient.reducedTime n p+100)+6)
    (Q := Inv μ srcA srcB dst n m len p f g expected len)
    (Inv μ srcA srcB dst n m len p f g expected) len
    (LightPolynomialCoefficient.reducedTime n p+90) ?start ?round ?done ?bound) ?finish
  case start =>
    refine ⟨0,?_⟩
    simp only [flag_zero]
    exact congrArg (fun loc => (⟨loc,μ⟩ : State))
      ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
  case round =>
    rintro j _ hj _ ⟨old,rfl⟩
    have hwordJ : ((20*((n+1)*(p+1)^2+j+m+10) : ℕ) : ℤ)≤lim.word := by omega
    have hbudget : (coefficient p f g n m j : ℤ)≤lim.word := by
      have hh : coefficient p f g n m j≤LightPolynomialCoefficient.rawCoefficient f g n m j := Nat.mod_le _ _
      have hb := LightPolynomialCoefficient.raw_bound f g hf hg (j := n) le_rfl (k := j)
      have hfit : n*p^2≤20*((n+1)*(p+1)^2+len+m+10) := by
        have hh : n*p^2≤(n+1)*(p+1)^2 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) 2)
        omega
      exact (Int.ofNat_le.mpr (hh.trans (hb.trans hfit))).trans hword
    have hflags := flag_bounds p f g expected n m j
    have hflags' := flag_bounds p f g expected n m (j+1)
    have hread := hreadD j hj
    unfold roundBody
    light_call (LightPolynomialCoefficient.reduced_meets (depth := depth+1)
      hcoeff hraw hdigit hdivide μ f g hw (by omega) hA hB hreadA hreadB hf hg hwordJ)
      using LightPolynomialCoefficient.reducedTime with result ν ⟨hresult,hν⟩
    subst ν
    subst result
    refine Ends.iteLast ?_ ?_ (by light_side [hread]) (by light_time)
    · intro heq
      have he : expected j=coefficient p f g n m j := by
        have hh : (coefficient p f g n m j : ℤ)=(expected j : ℤ) := by simpa [hread] using heq
        exact_mod_cast hh.symm
      have hflag : flag p f g expected n m (j+1)=flag p f g expected n m j := by
        simp [flag,valid_succ,he]
      exact Ends.skip ⟨by simp,(coefficient p f g n m j : ℤ),by simp [hflag,update_frame_setLocal]⟩
    · intro hneq
      have he : expected j≠coefficient p f g n m j := by
        intro he
        apply hneq
        simp [hread,he]
      have hflag : flag p f g expected n m (j+1)=0 := by simp [flag,valid_succ,he]
      light_set (0 : ℕ)
      exact ⟨by simp,(coefficient p f g n m j : ℤ),by simp [hflag,update_frame_setLocal]⟩
  case done => rintro _ _ h; exact h
  case bound => rintro j _ _ _ ⟨r,rfl⟩; light_side
  case finish =>
    rintro _ ⟨r,rfl⟩
    have hf := flag_bounds p f g expected n m len
    light_set (flag p f g expected n m len)
    exact ⟨rfl,rfl⟩

end ThreeSum.LightPolynomialProductCheck
