import Submission.ThreeSum.LightPolynomialProductArray
import Submission.ThreeSum.LightPolynomialProductCheck
import Submission.ThreeSum.LightPrimeAddArray

namespace ThreeSum.LightPolynomialQuotientCheck
open Light
set_option maxHeartbeats 3000000

/-- Check `x*y = h*f+r` coefficient by coefficient over Fp. -/
def body (pProduct pAdd pCheck : ℕ) : Stmt :=
  .set 9 (k 2 *' v 5) ;;
  .call pProduct [v 2,v 3,v 5,v 5 +' k 1,v 9,v 6,v 7] 10 ;;
  .call pAdd [v 7,v 4,v 8,v 9,v 6] 10 ;;
  .call pCheck [v 0,v 1,v 8,v 5,v 5,v 9,v 6] 0

def expected (p d : ℕ) (h f r : ℕ → ℕ) (i : ℕ) : ℕ :=
  (LightPolynomialCoefficient.coefficient p h f d (d+1) i+r i)%p

def time (d p : ℕ) : ℕ := LightPolynomialProductArray.time d p (2*d)+
  LightPrimeAddArray.time (2*d) p+LightPolynomialProductCheck.time d p (2*d)+100

def word (d p : ℕ) : ℕ := 100*((d+2)*(p+1)^2+4*d+p+20)

structure Procs (P : Program) (main : ℕ) where
  product : ℕ
  add : ℕ
  check : ℕ
  coefficient : ℕ
  raw : ℕ
  digit : ℕ
  divide : ℕ
  mulAdd : ℕ
  mainBody : P[main]?=some (body product add check)
  productBody : P[product]?=some (LightPolynomialProductArray.body coefficient)
  addBody : P[add]?=some (LightPrimeAddArray.body mulAdd)
  checkBody : P[check]?=some (LightPolynomialProductCheck.body coefficient)
  coefficientBody : P[coefficient]?=some (LightPolynomialCoefficient.reducedBody raw digit)
  rawBody : P[raw]?=some LightPolynomialCoefficient.body
  digitBody : P[digit]?=some (LightRadixDigit.body divide)
  divideBody : P[divide]?=some LightSmallDivide.body
  mulAddBody : P[mulAdd]?=some (LightPrimeCoefficient.mulAddBody divide)

variable {lim : Limits} {P : Program} {depth : ℕ}

theorem Procs.meets {main aBase bBase hBase fBase rBase productWork sumWork d p : ℕ}
    (S : Procs P main) (μ : ℕ → ℤ) (x y h f r : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+3<lim.depth) (hp : 1<p)
    (ha : aBase+d≤productWork) (hb : bBase+d≤productWork)
    (hh : hBase+d≤productWork) (hf : fBase+(d+1)≤productWork)
    (hr : rBase+2*d≤productWork) (hprod : productWork+2*d≤sumWork)
    (hspace : sumWork+2*d≤lim.space)
    (hxRead : ∀ i<d, μ (aBase+i)=(x i : ℤ))
    (hyRead : ∀ i<d, μ (bBase+i)=(y i : ℤ))
    (hhRead : ∀ i<d, μ (hBase+i)=(h i : ℤ))
    (hfRead : ∀ i<d+1, μ (fBase+i)=(f i : ℤ))
    (hrRead : ∀ i<2*d, μ (rBase+i)=(r i : ℤ))
    (hxBound : ∀ i<d, x i<p) (hyBound : ∀ i<d, y i<p)
    (hhBound : ∀ i<d, h i<p) (hfBound : ∀ i<d+1, f i<p)
    (hrBound : ∀ i<2*d, r i<p)
    (hword : (word d p : ℤ)≤lim.word) :
    Meets lim P main depth [aBase,bBase,hBase,fBase,rBase,d,p,productWork,sumWork] μ (time d p)
      (fun z ν => z=LightPolynomialProductCheck.flag p x y (expected p d h f r) d d (2*d) ∧
        Kept μ ν productWork) := by
  have hbudget (z : ℕ) (hz : z≤word d p) : (z : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr hz).trans hword
  have hcommon : 20*((d+1)*(p+1)^2+2*d+(d+1)+10)≤word d p := by
    unfold word
    have hpow := Nat.zero_le ((p+1)^2)
    nlinarith
  have hwprod := hbudget _ hcommon
  have hwcheck := hbudget (20*((d+1)*(p+1)^2+2*d+d+10)) (by omega)
  have hwadd : (LightPrimeCoefficient.word p : ℤ)≤lim.word := by
    apply hbudget
    unfold LightPrimeCoefficient.word word
    have hh : (p+1)^2≤(d+2)*(p+1)^2 := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith
  have hdWord := hbudget d (by unfold word; omega)
  have htwoDWord := hbudget (2*d) (by unfold word; omega)
  have hpWord := hbudget p (by unfold word; omega)
  have hsuccWord := hbudget (d+1) (by unfold word; omega)
  have h2 : (2 : ℤ)≤lim.word := hbudget 2 (by unfold word; omega)
  apply Meets.of_body S.mainBody
  unfold body time
  light_set (2*d : ℕ) using LightPolynomialProductArray.time,LightPrimeAddArray.time,LightPolynomialProductCheck.time
  light_call (LightPolynomialProductArray.meets (depth := depth+1)
    S.productBody S.coefficientBody S.rawBody S.digitBody S.divideBody μ h f hw (by omega)
    hh hf (by omega) hhRead hfRead hhBound hfBound hwprod)
    using LightPolynomialProductArray.time,LightPrimeAddArray.time,LightPolynomialProductCheck.time
    with v₁ μ₁ ⟨productValues,keep₁⟩
  have rValues (i : ℕ) (hi : i<2*d) : μ₁ (rBase+i)=(r i : ℤ) :=
    (keep₁ _ (Or.inl (by omega))).trans (hrRead i hi)
  have productBound (i : ℕ) (_hi : i<2*d) :
      LightPolynomialCoefficient.coefficient p h f d (d+1) i<p := Nat.mod_lt _ (by omega)
  light_call (LightPrimeAddArray.meets (depth := depth+1)
    S.addBody S.mulAddBody S.divideBody μ₁
    (fun i => LightPolynomialCoefficient.coefficient p h f d (d+1) i) r hw (by omega) hp
    hprod (by omega) hspace productValues rValues productBound hrBound hwadd)
    using LightPolynomialProductArray.time,LightPrimeAddArray.time,LightPolynomialProductCheck.time
    with v₂ μ₂ ⟨sumValues,keep₂⟩
  have xValues (i : ℕ) (hi : i<d) : μ₂ (aBase+i)=(x i : ℤ) := by
    rw [keep₂ _ (Or.inl (by omega)),keep₁ _ (Or.inl (by omega)),hxRead i hi]
  have yValues (i : ℕ) (hi : i<d) : μ₂ (bBase+i)=(y i : ℤ) := by
    rw [keep₂ _ (Or.inl (by omega)),keep₁ _ (Or.inl (by omega)),hyRead i hi]
  have expectedValues (i : ℕ) (hi : i<2*d) : μ₂ (sumWork+i)=(expected p d h f r i : ℤ) := sumValues i hi
  light_call (LightPolynomialProductCheck.meets (depth := depth+1)
    S.checkBody S.coefficientBody S.rawBody S.digitBody S.divideBody μ₂ x y (expected p d h f r)
    hw (by omega) (by omega) (by omega) hspace xValues yValues expectedValues hxBound hyBound hwcheck)
    using LightPolynomialProductArray.time,LightPrimeAddArray.time,LightPolynomialProductCheck.time
    with z ν ⟨hz,hν⟩
  subst ν
  refine ⟨hz,?_⟩
  intro i hi
  change μ₂ i=μ i
  rw [keep₂ _ (Or.inl (by omega)),keep₁ _ (Or.inl hi)]

end ThreeSum.LightPolynomialQuotientCheck
