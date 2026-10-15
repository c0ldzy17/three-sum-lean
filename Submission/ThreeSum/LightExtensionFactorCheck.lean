import Submission.ThreeSum.LightPolynomialProductCheck
import Submission.ThreeSum.LightCoefficientDecode

namespace ThreeSum.LightExtensionFactorCheck
open Light
set_option maxHeartbeats 2000000

/-- Decode two monic factor codes, then compare their full product to the
candidate polynomial.  The caller supplies the actual candidate coefficients. -/
def body (pDecode pCheck : ℕ) : Stmt :=
  .set 9 (k 2 *' v 3) ;;
  .call pDecode [v 9,v 2,v 0,v 5,k 0,k 1,v 7,v 9] 10 ;;
  .call pDecode [v 9,v 2,v 1,v 5,k 0,k 1,v 8,v 9] 10 ;;
  .call pCheck [v 7,v 8,v 6,v 4 +' k 1,v 3 -' v 4 +' k 1,v 9,v 2] 0

def digits (p code : ℕ) (i : ℕ) : ℕ := LightCoefficientDecode.digit p code i

def time (d e p u v : ℕ) : ℕ := LightCoefficientDecode.time (2*d) u+
  LightCoefficientDecode.time (2*d) v+LightPolynomialProductCheck.time (e+1) p (2*d)+300

def word (d e p u v : ℕ) : ℕ := LightCoefficientDecode.word (2*d) p u 0 1+
  LightCoefficientDecode.word (2*d) p v 0 1+
  20*((e+2)*(p+1)^2+2*d+(d-e+1)+10)+100

structure Procs (P : Program) (main : ℕ) where
  decode : ℕ
  check : ℕ
  digit : ℕ
  divide : ℕ
  coefficient : ℕ
  raw : ℕ
  mainBody : P[main]?=some (body decode check)
  decodeBody : P[decode]?=some (LightCoefficientDecode.body digit)
  checkBody : P[check]?=some (LightPolynomialProductCheck.body coefficient)
  coefficientBody : P[coefficient]?=some (LightPolynomialCoefficient.reducedBody raw digit)
  rawBody : P[raw]?=some LightPolynomialCoefficient.body
  digitBody : P[digit]?=some (LightRadixDigit.body divide)
  divideBody : P[divide]?=some LightSmallDivide.body

variable {lim : Limits} {P : Program} {depth : ℕ}

theorem Procs.meets {main d e p u v powers target hBase gBase : ℕ}
    (S : Procs P main) (μ : ℕ → ℤ) (f : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+3<lim.depth)
    (hp : 1<p) (he : 0<e) (hed : e<d)
    (hpow : powers+(2*d+1)≤hBase) (htarget : target+2*d≤hBase)
    (hh : hBase+2*d≤gBase) (hspace : gBase+2*d≤lim.space)
    (hpowRead : ∀ i≤2*d, μ (powers+i)=((p^i : ℕ) : ℤ))
    (hfRead : ∀ i<2*d, μ (target+i)=(f i : ℤ))
    (hword : (word d e p u v : ℤ)≤lim.word) :
    Meets lim P main depth [u,v,p,d,e,powers,target,hBase,gBase] μ (time d e p u v)
      (fun z ν => z=LightPolynomialProductCheck.flag p (digits p u) (digits p v) f
          (e+1) (d-e+1) (2*d) ∧ Kept μ ν hBase) := by
  have hwU : (LightCoefficientDecode.word (2*d) p u 0 1 : ℤ)≤lim.word := by unfold word at hword; omega
  have hwV : (LightCoefficientDecode.word (2*d) p v 0 1 : ℤ)≤lim.word := by unfold word at hword; omega
  have hwCheck : ((20*((e+2)*(p+1)^2+2*d+(d-e+1)+10) : ℕ) : ℤ)≤lim.word := by unfold word at hword; omega
  have hu : (u : ℤ)≤lim.word := by unfold LightCoefficientDecode.word at hwU; omega
  have hv : (v : ℤ)≤lim.word := by unfold LightCoefficientDecode.word at hwV; omega
  have hpWord : (p : ℤ)≤lim.word := by unfold LightCoefficientDecode.word at hwU; omega
  have hdWord : (d : ℤ)≤lim.word := by unfold LightCoefficientDecode.word at hwU; omega
  have h2d : (2*(d : ℤ))≤lim.word := by unfold LightCoefficientDecode.word at hwU; omega
  have heWord : (e : ℤ)≤lim.word := by omega
  have hegWord : ((d-e+1 : ℕ) : ℤ)≤lim.word := by omega
  have he1Word : ((e+1 : ℕ) : ℤ)≤lim.word := by omega
  have htwo : (2 : ℤ)≤lim.word := by unfold word at hword; omega
  have hsub : (d : ℤ)-(e : ℤ)=((d-e : ℕ) : ℤ) := (Int.natCast_sub (by omega)).symm
  apply Meets.of_body S.mainBody
  unfold body time
  light_set (2*d : ℕ) using LightCoefficientDecode.time,LightPolynomialProductCheck.time
  light_call (LightCoefficientDecode.meets (d := depth+1) (W := 2*d) (p := p) (k := u)
    (powers := powers) (start := 0) (stride := 1) (dst := hBase) (n := 2*d)
    S.decodeBody S.digitBody S.divideBody hw (by omega) (by omega) (by omega) (by omega)
    (Or.inl hpow) hwU (by intro i hi; omega) hpowRead)
    using LightCoefficientDecode.time,LightPolynomialProductCheck.time
    with z₁ μ₁ ⟨uValues,keep₁⟩
  have pow₁ (i : ℕ) (hi : i≤2*d) : μ₁ (powers+i)=((p^i : ℕ) : ℤ) :=
    (keep₁ _ (Or.inl (by omega))).trans (hpowRead i hi)
  light_call (LightCoefficientDecode.meets (d := depth+1) (W := 2*d) (p := p) (k := v)
    (powers := powers) (start := 0) (stride := 1) (dst := gBase) (n := 2*d)
    S.decodeBody S.digitBody S.divideBody hw (by omega) (by omega) hspace (by omega)
    (Or.inl (by omega)) hwV (by intro i hi; omega) pow₁)
    using LightCoefficientDecode.time,LightPolynomialProductCheck.time
    with z₂ μ₂ ⟨vValues,keep₂⟩
  have u₂ (i : ℕ) (hi : i<e+1) : μ₂ (hBase+i)=(digits p u i : ℤ) := by
    rw [keep₂ _ (Or.inl (by omega))]
    simpa [digits] using uValues i (by omega)
  have v₂ (i : ℕ) (hi : i<d-e+1) : μ₂ (gBase+i)=(digits p v i : ℤ) := by
    simpa [digits] using vValues i (by omega)
  have f₂ (i : ℕ) (hi : i<2*d) : μ₂ (target+i)=(f i : ℤ) := by
    rw [keep₂ _ (Or.inl (by omega)),keep₁ _ (Or.inl (by omega)),hfRead i hi]
  have digBound (code i : ℕ) : digits p code i<p := Nat.mod_lt _ (by omega)
  light_call (LightPolynomialProductCheck.meets (depth := depth+1)
    S.checkBody S.coefficientBody S.rawBody S.digitBody S.divideBody μ₂
    (digits p u) (digits p v) f hw (by omega) (by omega) (by omega) (by omega)
    u₂ v₂ f₂ (fun i _ => digBound u i) (fun i _ => digBound v i) hwCheck)
    using hsub,LightCoefficientDecode.time,LightPolynomialProductCheck.time
    with z ν ⟨hz,hν⟩
  subst ν
  refine ⟨hz,?_⟩
  intro i hi
  change μ₂ i=μ i
  rw [keep₂ _ (Or.inl (by omega)),keep₁ _ (Or.inl hi)]

end ThreeSum.LightExtensionFactorCheck
