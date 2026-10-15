import Submission.ThreeSum.LightPolynomialQuotientCheck

namespace ThreeSum.LightExtensionQuotientPredicate
open Light
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000

structure Layout where
  p : ℕ
  dim : ℕ
  powers : ℕ
  a : ℕ
  b : ℕ
  modulus : ℕ
  h : ℕ
  remainder : ℕ
  productWork : ℕ
  sumWork : ℕ

-- The structure fields are ordinary runtime header words.
def header (C : Layout) : List ℤ :=
  [C.p,C.dim,C.powers,C.a,C.b,C.modulus,C.h,C.remainder,C.productWork,C.sumWork]

def get (offset : ℕ) : Expr := M (v 2 +' k offset)

def body (pDecode pCore : ℕ) : Stmt :=
  .call pDecode [get 1,get 0,v 0,get 2,k 0,k 1,get 6,get 1] 3 ;;
  .call pDecode [k 2 *' get 1,get 0,v 1,get 2,k 0,k 1,get 7,k 2 *' get 1] 3 ;;
  .call pCore [get 3,get 4,get 6,get 5,get 7,get 1,get 0,get 8,get 9] 0

def time (d p u v : ℕ) : ℕ := LightCoefficientDecode.time d u+
  LightCoefficientDecode.time (2*d) v+LightPolynomialQuotientCheck.time d p+500

def word (d p u v : ℕ) : ℕ := LightCoefficientDecode.word d p u 0 1+
  LightCoefficientDecode.word (2*d) p v 0 1+LightPolynomialQuotientCheck.word d p+100

theorem time_mono {d p u v U V : ℕ} (hu : u≤U) (hv : v≤V) :
    time d p u v≤time d p U V := by
  unfold time LightCoefficientDecode.time LightRadixDigit.time
  gcongr

theorem word_mono {d p u v U V : ℕ} (hu : u≤U) (hv : v≤V) :
    word d p u v≤word d p U V := by
  unfold word LightCoefficientDecode.word
  omega

def digits (p code : ℕ) (i : ℕ) : ℕ := LightCoefficientDecode.digit p code i

noncomputable def result (C : Layout) (x y f : ℕ → ℕ) (u v : ℕ) : ℤ :=
  LightPolynomialProductCheck.flag C.p x y
    (LightPolynomialQuotientCheck.expected C.p C.dim (digits C.p u) f (digits C.p v))
    C.dim C.dim (2*C.dim)

structure Procs (P : Program) (main : ℕ) where
  decode : ℕ
  digit : ℕ
  divide : ℕ
  core : ℕ
  mainBody : P[main]?=some (body decode core)
  decodeBody : P[decode]?=some (LightCoefficientDecode.body digit)
  digitBody : P[digit]?=some (LightRadixDigit.body divide)
  divideBody : P[divide]?=some LightSmallDivide.body
  coreProcs : LightPolynomialQuotientCheck.Procs P core

variable {lim : Limits} {P : Program} {depth : ℕ}

theorem header_kept {C : Layout} {μ ν : ℕ → ℤ} {ctx keep : ℕ}
    (H : Seg μ ctx (header C)) (hctx : ctx+10≤keep) (hkeep : Kept μ ν keep) :
    Seg ν ctx (header C) := by
  intro i hi
  have hi' : i<10 := by simpa [header] using hi
  rw [hkeep _ (by omega)]
  exact H i hi

theorem Procs.meets {main ctx u v : ℕ} (S : Procs P main) (C : Layout)
    (μ : ℕ → ℤ) (x y f : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+4<lim.depth) (hp : 1<C.p)
    (H : Seg μ ctx (header C)) (hctx : ctx+10≤C.h)
    (hpowers : C.powers+(2*C.dim+1)≤C.h)
    (hpowRead : ∀ e≤2*C.dim, μ (C.powers+e)=((C.p^e : ℕ) : ℤ))
    (ha : C.a+C.dim≤C.h) (hb : C.b+C.dim≤C.h)
    (hf : C.modulus+(C.dim+1)≤C.h)
    (hh : C.h+C.dim≤C.remainder) (hr : C.remainder+2*C.dim≤C.productWork)
    (hprod : C.productWork+2*C.dim≤C.sumWork)
    (hspace : C.sumWork+2*C.dim≤lim.space)
    (hxRead : ∀ i<C.dim, μ (C.a+i)=(x i : ℤ))
    (hyRead : ∀ i<C.dim, μ (C.b+i)=(y i : ℤ))
    (hfRead : ∀ i<C.dim+1, μ (C.modulus+i)=(f i : ℤ))
    (hxBound : ∀ i<C.dim, x i<C.p) (hyBound : ∀ i<C.dim, y i<C.p)
    (hfBound : ∀ i<C.dim+1, f i<C.p)
    (hword : (word C.dim C.p u v : ℤ)≤lim.word) :
    Meets lim P main depth [u,v,ctx] μ (time C.dim C.p u v)
      (fun z ν => z=result C x y f u v ∧ Kept μ ν C.h) := by
  have h0 := H 0 (by simp [header])
  have h1 := H 1 (by simp [header])
  have h2 := H 2 (by simp [header])
  have h3 := H 3 (by simp [header])
  have h4 := H 4 (by simp [header])
  have h5 := H 5 (by simp [header])
  have h6 := H 6 (by simp [header])
  have h7 := H 7 (by simp [header])
  have h8 := H 8 (by simp [header])
  have h9 := H 9 (by simp [header])
  simp only [header,List.getElem_cons_zero,List.getElem_cons_succ,Nat.add_zero] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hwH : (LightCoefficientDecode.word C.dim C.p u 0 1 : ℤ)≤lim.word := by unfold word at hword; omega
  have hwR : (LightCoefficientDecode.word (2*C.dim) C.p v 0 1 : ℤ)≤lim.word := by unfold word at hword; omega
  have hwCore : (LightPolynomialQuotientCheck.word C.dim C.p : ℤ)≤lim.word := by unfold word at hword; omega
  have hu : (u : ℤ)≤lim.word := by unfold LightCoefficientDecode.word at hwH; omega
  have hv : (v : ℤ)≤lim.word := by unfold LightCoefficientDecode.word at hwR; omega
  have h2d : (2*(C.dim : ℤ))≤lim.word := by unfold LightCoefficientDecode.word at hwR; omega
  have hpWord : (C.p : ℤ)≤lim.word := by unfold LightCoefficientDecode.word at hwR; omega
  have hdWord : (C.dim : ℤ)≤lim.word := by unfold LightCoefficientDecode.word at hwH; omega
  have htwo : (2 : ℤ)≤lim.word := by unfold word at hword; omega
  have headerAddress (i : ℕ) : ((ctx : ℤ)+(i : ℤ)).toNat=ctx+i := by omega
  have ha0 : ((ctx : ℤ)+0).toNat=ctx+0 := by omega
  have ha1 : ((ctx : ℤ)+1).toNat=ctx+1 := by omega
  have ha2 : ((ctx : ℤ)+2).toNat=ctx+2 := by omega
  have ha3 : ((ctx : ℤ)+3).toNat=ctx+3 := by omega
  have ha4 : ((ctx : ℤ)+4).toNat=ctx+4 := by omega
  have ha5 : ((ctx : ℤ)+5).toNat=ctx+5 := by omega
  have ha6 : ((ctx : ℤ)+6).toNat=ctx+6 := by omega
  have ha7 : ((ctx : ℤ)+7).toNat=ctx+7 := by omega
  have ha8 : ((ctx : ℤ)+8).toNat=ctx+8 := by omega
  have ha9 : ((ctx : ℤ)+9).toNat=ctx+9 := by omega
  apply Meets.of_body S.mainBody
  unfold body time
  light_call (LightCoefficientDecode.meets (d := depth+1) (W := C.dim) (p := C.p) (k := u)
    (powers := C.powers) (start := 0) (stride := 1) (dst := C.h) (n := C.dim)
    S.decodeBody S.digitBody S.divideBody hw (by omega) (by omega) (by omega) (by omega)
    (Or.inl (by omega)) hwH (by intro i hi; omega) (fun e he => hpowRead e (by omega)))
    using get,headerAddress,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,ha8,ha9,h0,h1,h2,h6,LightCoefficientDecode.time,LightPolynomialQuotientCheck.time
    with z₁ μ₁ ⟨hValues,keep₁⟩
  have keepH : Kept μ μ₁ C.h := fun a ha => keep₁ a (Or.inl ha)
  have H₁ := header_kept H hctx keepH
  have hh0 := H₁ 0 (by simp [header])
  have hh1 := H₁ 1 (by simp [header])
  have hh2 := H₁ 2 (by simp [header])
  have hh7 := H₁ 7 (by simp [header])
  simp only [header,List.getElem_cons_zero,List.getElem_cons_succ,Nat.add_zero] at hh0 hh1 hh2 hh7
  have pow₁ (e : ℕ) (he : e≤2*C.dim) : μ₁ (C.powers+e)=((C.p^e : ℕ) : ℤ) :=
    (keepH _ (by omega)).trans (hpowRead e he)
  light_call (LightCoefficientDecode.meets (d := depth+1) (W := 2*C.dim) (p := C.p) (k := v)
    (powers := C.powers) (start := 0) (stride := 1) (dst := C.remainder) (n := 2*C.dim)
    S.decodeBody S.digitBody S.divideBody hw (by omega) (by omega) (by omega) (by omega)
    (Or.inl (by omega)) hwR (by intro i hi; omega) pow₁)
    using get,headerAddress,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,ha8,ha9,hh0,hh1,hh2,hh7,LightCoefficientDecode.time,LightPolynomialQuotientCheck.time
    with z₂ μ₂ ⟨rValues,keep₂⟩
  have keepR : Kept μ₁ μ₂ C.h := fun a ha => keep₂ a (Or.inl (by omega))
  have H₂ := header_kept H₁ hctx keepR
  have hhh0 := H₂ 0 (by simp [header])
  have hhh1 := H₂ 1 (by simp [header])
  have hhh3 := H₂ 3 (by simp [header])
  have hhh4 := H₂ 4 (by simp [header])
  have hhh5 := H₂ 5 (by simp [header])
  have hhh6 := H₂ 6 (by simp [header])
  have hhh7 := H₂ 7 (by simp [header])
  have hhh8 := H₂ 8 (by simp [header])
  have hhh9 := H₂ 9 (by simp [header])
  simp only [header,List.getElem_cons_zero,List.getElem_cons_succ,Nat.add_zero] at hhh0 hhh1 hhh3 hhh4 hhh5 hhh6 hhh7 hhh8 hhh9
  have x₂ (i : ℕ) (hi : i<C.dim) : μ₂ (C.a+i)=(x i : ℤ) :=
    (keepR _ (by omega)).trans ((keepH _ (by omega)).trans (hxRead i hi))
  have y₂ (i : ℕ) (hi : i<C.dim) : μ₂ (C.b+i)=(y i : ℤ) :=
    (keepR _ (by omega)).trans ((keepH _ (by omega)).trans (hyRead i hi))
  have f₂ (i : ℕ) (hi : i<C.dim+1) : μ₂ (C.modulus+i)=(f i : ℤ) :=
    (keepR _ (by omega)).trans ((keepH _ (by omega)).trans (hfRead i hi))
  have h₂ (i : ℕ) (hi : i<C.dim) : μ₂ (C.h+i)=(digits C.p u i : ℤ) := by
    rw [keep₂ _ (Or.inl (by omega))]
    simpa [digits] using hValues i hi
  have r₂ (i : ℕ) (hi : i<2*C.dim) : μ₂ (C.remainder+i)=(digits C.p v i : ℤ) := by
    simpa [digits] using rValues i hi
  have digBound (code i : ℕ) : digits C.p code i<C.p := Nat.mod_lt _ (by omega)
  light_call (S.coreProcs.meets (depth := depth+1) μ₂ x y (digits C.p u) f (digits C.p v)
    hw (by omega) hp (by omega) (by omega) (by omega) (by omega) hr hprod hspace
    x₂ y₂ h₂ f₂ r₂ hxBound hyBound (fun i _ => digBound u i) hfBound
    (fun i _ => digBound v i) hwCore)
    using get,headerAddress,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,ha8,ha9,hhh0,hhh1,hhh3,hhh4,hhh5,hhh6,hhh7,hhh8,hhh9,
      LightCoefficientDecode.time,LightPolynomialQuotientCheck.time
    with z ν ⟨hz,hkeep⟩
  refine ⟨hz,?_⟩
  intro a ha
  change ν a=μ a
  rw [hkeep _ (by omega),keepR _ ha,keepH _ ha]

/-- Closed eleven-procedure implementation, including every arithmetic helper. -/
def program : Program :=
  [body 1 4, LightCoefficientDecode.body 2,LightRadixDigit.body 3,LightSmallDivide.body,
    LightPolynomialQuotientCheck.body 5 6 7,LightPolynomialProductArray.body 8,
    LightPrimeAddArray.body 10,LightPolynomialProductCheck.body 8,
    LightPolynomialCoefficient.reducedBody 9 2,LightPolynomialCoefficient.body,
    LightPrimeCoefficient.mulAddBody 3]

def procs : Procs program 0 where
  decode := 1
  digit := 2
  divide := 3
  core := 4
  mainBody := rfl
  decodeBody := rfl
  digitBody := rfl
  divideBody := rfl
  coreProcs := {
    product := 5, add := 6, check := 7, coefficient := 8, raw := 9,
    digit := 2, divide := 3, mulAdd := 10,
    mainBody := rfl,productBody := rfl,addBody := rfl,checkBody := rfl,
    coefficientBody := rfl,rawBody := rfl,digitBody := rfl,divideBody := rfl,mulAddBody := rfl }

end ThreeSum.LightExtensionQuotientPredicate
