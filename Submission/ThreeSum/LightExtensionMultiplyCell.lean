import Submission.ThreeSum.LightExtensionQuotientSearch

noncomputable section
namespace ThreeSum.LightExtensionMultiplyCell
open Light LightExtensionQuotientPredicate
set_option maxHeartbeats 4000000
set_option maxRecDepth 6000
noncomputable local instance (Q : Prop) : Decidable Q := Classical.propDecidable Q

/-- Arguments are x,y,context,p,dimension,powers,left,right,q. -/
def body (pDecode pSearch pDigit : ℕ) : Stmt :=
  .call pDecode [v 4,v 3,v 0,v 5,k 0,k 1,v 6,v 4] 9 ;;
  .call pDecode [v 4,v 3,v 1,v 5,k 0,k 1,v 7,v 4] 9 ;;
  .call pSearch [v 8,v 2] 9 ;;
  .call pDigit [v 9 -' k 1,k 1,v 8] 0

def searchTime (C : Layout) (q : ℕ) : ℕ :=
  q*q*(LightExtensionQuotientPredicate.time C.dim C.p q q+200)+100

def time (C : Layout) (q : ℕ) : ℕ :=
  2*LightCoefficientDecode.time C.dim q+searchTime C q+LightRadixDigit.time (q*q)+500

def word (C : Layout) (q ctx : ℕ) : ℕ :=
  LightCoefficientDecode.word C.dim C.p q 0 1+
  LightExtensionQuotientPredicate.word C.dim C.p q q+
  LightRadixDigit.word (q*q) 1 q+q*q+q+ctx+100

variable {lim : Limits} {P : Program} {depth : ℕ}

theorem meets {proc pDecode pSearch pDigit pDivide ctx q x y : ℕ}
    (C : Layout) (hmain : P[proc]?=some (body pDecode pSearch pDigit))
    (hdecode : P[pDecode]?=some (LightCoefficientDecode.body pDigit))
    (hdigit : P[pDigit]?=some (LightRadixDigit.body pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (μ : ℕ → ℤ) (f : ℕ → ℕ) (mul : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth+7 < lim.depth)
    (hp : 1 < C.p) (hq : 0 < q) (hx : x < q) (hy : y < q)
    (H : Seg μ ctx (header C)) (hctx : ctx+10 ≤ C.a)
    (hpow : C.powers+(2*C.dim+1) ≤ C.a)
    (hmod : C.modulus+(C.dim+1) ≤ C.a)
    (hab : C.a+C.dim ≤ C.b) (hbh : C.b+C.dim ≤ C.h)
    (hh : C.h+C.dim ≤ C.remainder) (hr : C.remainder+2*C.dim ≤ C.productWork)
    (hprod : C.productWork+2*C.dim ≤ C.sumWork)
    (hspace : C.sumWork+2*C.dim ≤ lim.space)
    (hpowRead : ∀ i ≤ 2*C.dim, μ (C.powers+i)=((C.p^i : ℕ) : ℤ))
    (hfRead : ∀ i < C.dim+1, μ (C.modulus+i)=(f i : ℤ))
    (hfBound : ∀ i < C.dim+1, f i < C.p)
    (hword : (word C q ctx : ℤ) ≤ lim.word)
    (hspec : ∀ a < q, ∀ b < q,
      let z := LightPairSearch.first (LightPairSearch.goodCode q
        (LightExtensionQuotientSearch.good C (digits C.p a) (digits C.p b) f)) (q*q)
      0 < z ∧ z ≤ q*q ∧ (z-1)%q=mul a b)
    (hsearch : ∀ ν, Seg ν ctx (header C) →
      (∀ i ≤ 2*C.dim, ν (C.powers+i)=((C.p^i : ℕ) : ℤ)) →
      (∀ i < C.dim, ν (C.a+i)=(digits C.p x i : ℤ)) →
      (∀ i < C.dim, ν (C.b+i)=(digits C.p y i : ℤ)) →
      (∀ i < C.dim+1, ν (C.modulus+i)=(f i : ℤ)) →
      Meets lim P pSearch (depth+1) [q,ctx] ν (searchTime C q)
        (fun z ξ => z=(LightPairSearch.first (LightPairSearch.goodCode q
          (LightExtensionQuotientSearch.good C (digits C.p x) (digits C.p y) f)) (q*q) : ℤ) ∧
          Kept ν ξ C.h)) :
    Meets lim P proc depth [x,y,ctx,C.p,C.dim,C.powers,C.a,C.b,q] μ (time C q)
      (fun z ν => z=(mul x y : ℤ) ∧ Kept μ ν C.a) := by
  have hbudget (n : ℕ) (hn : n ≤ word C q ctx) : (n : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hn).trans hword
  have hdword : (LightCoefficientDecode.word C.dim C.p q 0 1 : ℤ) ≤ lim.word :=
    hbudget _ (by unfold word; omega)
  have hwx : (LightCoefficientDecode.word C.dim C.p x 0 1 : ℤ) ≤ lim.word := by
    apply hbudget; unfold word LightCoefficientDecode.word; omega
  have hwy : (LightCoefficientDecode.word C.dim C.p y 0 1 : ℤ) ≤ lim.word := by
    apply hbudget; unfold word LightCoefficientDecode.word; omega
  have hs := hspec x hx y hy
  let z := LightPairSearch.first (LightPairSearch.goodCode q
    (LightExtensionQuotientSearch.good C (digits C.p x) (digits C.p y) f)) (q*q)
  have hzpos : 0 < z := hs.1
  have hzle : z ≤ q*q := hs.2.1
  have hzmod : (z-1)%q=mul x y := hs.2.2
  have hzw : ((z : ℕ) : ℤ) ≤ lim.word := hbudget _ (by unfold word; omega)
  have hzmw : (LightRadixDigit.word (z-1) 1 q : ℤ) ≤ lim.word := by
    apply hbudget; unfold word LightRadixDigit.word; omega
  have hdecx := LightCoefficientDecode.meets (d := depth+1) (W := C.dim) (p := C.p)
    (k := x) (powers := C.powers) (start := 0) (stride := 1) (dst := C.a) (n := C.dim)
    hdecode hdigit hdivide hw (by omega) (by omega) (by omega) (by omega)
    (Or.inl (by omega)) hwx (by intro i hi; omega) (fun i hi => hpowRead i (by omega))
  have hdecTime (k : ℕ) (hk : k ≤ q) : LightCoefficientDecode.time C.dim k ≤ LightCoefficientDecode.time C.dim q := by
    unfold LightCoefficientDecode.time LightRadixDigit.time
    gcongr
  apply Meets.of_body hmain
  unfold body time
  light_call (hdecx.mono_time (hdecTime x hx.le)) using LightCoefficientDecode.time,LightRadixDigit.time,pow_two
    with X μ₁ ⟨hxValues,keep₁⟩
  have k1 : Kept μ μ₁ C.a := fun a ha => keep₁ a (Or.inl ha)
  have pow₁ (i : ℕ) (hi : i ≤ 2*C.dim) := (k1 _ (by omega)).trans (hpowRead i hi)
  light_call ((LightCoefficientDecode.meets (d := depth+1) (W := C.dim) (p := C.p)
    (k := y) (powers := C.powers) (start := 0) (stride := 1) (dst := C.b) (n := C.dim)
    hdecode hdigit hdivide hw (by omega) (by omega) (by omega) (by omega)
    (Or.inl (by omega)) hwy (by intro i hi; omega) (fun i hi => pow₁ i (by omega))).mono_time (hdecTime y hy.le))
    using LightCoefficientDecode.time,LightRadixDigit.time,pow_two
    with Y μ₂ ⟨hyValues,keep₂⟩
  have k2 : Kept μ₁ μ₂ C.b := fun a ha => keep₂ a (Or.inl ha)
  have H₂ := header_kept (header_kept H hctx k1) (by omega) k2
  have pow₂ (i : ℕ) (hi : i ≤ 2*C.dim) := (k2 _ (by omega)).trans (pow₁ i hi)
  have x₂ (i : ℕ) (hi : i < C.dim) : μ₂ (C.a+i)=(digits C.p x i : ℤ) := by
    rw [k2 _ (by omega)]; simpa [digits] using hxValues i hi
  have y₂ (i : ℕ) (hi : i < C.dim) : μ₂ (C.b+i)=(digits C.p y i : ℤ) := by
    simpa [digits] using hyValues i hi
  have f₂ (i : ℕ) (hi : i < C.dim+1) :=
    (k2 _ (by omega)).trans ((k1 _ (by omega)).trans (hfRead i hi))
  light_call (hsearch μ₂ H₂ pow₂ x₂ y₂ f₂) using searchTime
    with Z μ₃ ⟨hZ,keep₃⟩
  have hZ' : Z=(z : ℤ) := hZ
  subst Z
  have hsub : (z : ℤ)-1=((z-1 : ℕ) : ℤ) := by omega
  light_call (LightRadixDigit.meets (d := depth+1) (k := z-1) (b := 1) (p := q)
    hdigit hdivide μ₃ (by omega) hzmw)
    using hsub,LightRadixDigit.time,hzle,pow_two
    with R ν ⟨hR,hν⟩
  subst ν
  refine ⟨?_,?_⟩
  · simpa [hzmod] using hR
  · intro a ha
    exact (keep₃ a (by omega)).trans ((k2 a (by omega)).trans (k1 a ha))

/-- The complete quotient search and all arithmetic procedures are included. -/
def program : Program := LightExtensionQuotientSearch.program++[body 1 12 2]

theorem program_meets {ctx q x y : ℕ} (C : Layout)
    (μ : ℕ → ℤ) (f : ℕ → ℕ) (mul : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth+7 < lim.depth)
    (hp : 1 < C.p) (hq : 0 < q) (hx : x < q) (hy : y < q)
    (H : Seg μ ctx (header C)) (hctx : ctx+10 ≤ C.a)
    (hpow : C.powers+(2*C.dim+1) ≤ C.a)
    (hmod : C.modulus+(C.dim+1) ≤ C.a)
    (hab : C.a+C.dim ≤ C.b) (hbh : C.b+C.dim ≤ C.h)
    (hh : C.h+C.dim ≤ C.remainder) (hr : C.remainder+2*C.dim ≤ C.productWork)
    (hprod : C.productWork+2*C.dim ≤ C.sumWork)
    (hspace : C.sumWork+2*C.dim ≤ lim.space)
    (hpowRead : ∀ i ≤ 2*C.dim, μ (C.powers+i)=((C.p^i : ℕ) : ℤ))
    (hfRead : ∀ i < C.dim+1, μ (C.modulus+i)=(f i : ℤ))
    (hfBound : ∀ i < C.dim+1, f i < C.p)
    (hword : (word C q ctx : ℤ) ≤ lim.word)
    (hspec : ∀ a < q, ∀ b < q,
      let z := LightPairSearch.first (LightPairSearch.goodCode q
        (LightExtensionQuotientSearch.good C (digits C.p a) (digits C.p b) f)) (q*q)
      0 < z ∧ z ≤ q*q ∧ (z-1)%q=mul a b)
 :
    Meets lim program 13 depth [x,y,ctx,C.p,C.dim,C.powers,C.a,C.b,q] μ (time C q)
      (fun z ν => z=(mul x y : ℤ) ∧ Kept μ ν C.a) := by
  apply meets C rfl rfl rfl rfl μ f mul hw hd hp hq hx hy H hctx hpow hmod
    hab hbh hh hr hprod hspace hpowRead hfRead hfBound hword hspec
  intro ν Hν hpowν hxν hyν hfν
  have hsw : (LightExtensionQuotientPredicate.word C.dim C.p q q : ℤ) ≤ lim.word := by
    unfold word at hword; omega
  have hsearchw : ((q*q+q+ctx+20 : ℕ) : ℤ) ≤ lim.word := by
    unfold word at hword; omega
  have digBound (code i : ℕ) : digits C.p code i < C.p := Nat.mod_lt _ (by omega)
  exact (LightExtensionQuotientSearch.program_meets C ν (digits C.p x) (digits C.p y) f hw
    (by omega) hq hp Hν (by omega) (by omega) hpowν (by omega) hbh (by omega)
    hh hr hprod hspace hxν hyν hfν (fun i _ => digBound x i)
    (fun i _ => digBound y i) hfBound hsw hsearchw).append [body 1 12 2]

end ThreeSum.LightExtensionMultiplyCell
