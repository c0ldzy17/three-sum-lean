import Submission.ThreeSum.LightPolynomialCoefficient
import Submission.ThreeSum.LightCoefficientDecode

namespace ThreeSum.LightPolynomialProductArray
open Light
set_option maxHeartbeats 2000000

def body (pCoefficient : ℕ) : Stmt :=
  .for 7 (v 4) (
    .call pCoefficient [v 0,v 1,v 2,v 3,v 7,v 5] 8 ;;
    .store (v 6 +' v 7) (v 8))

def time (n p len : ℕ) : ℕ := len*(LightPolynomialCoefficient.reducedTime n p+100)+10

def Inv (μ : ℕ → ℤ) (srcA srcB n m len p dst : ℕ) (f g : ℕ → ℕ)
    (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ), σ=⟨frame [srcA,srcB,n,m,len,p,dst,i,r],ν⟩ ∧
    (∀ k < i, ν (dst+k)=(LightPolynomialCoefficient.coefficient p f g n m k : ℤ)) ∧
    SameOutside μ ν dst len

variable {lim : Limits} {P : Program} {depth : ℕ}

theorem meets {proc pCoefficient pRaw pDigit pDivide srcA srcB dst n m len p : ℕ}
    (hp : P[proc]?=some (body pCoefficient))
    (hcoeff : P[pCoefficient]?=some (LightPolynomialCoefficient.reducedBody pRaw pDigit))
    (hraw : P[pRaw]?=some LightPolynomialCoefficient.body)
    (hdigit : P[pDigit]?=some (LightRadixDigit.body pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (μ : ℕ → ℤ) (f g : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+2<lim.depth)
    (hA : srcA+n≤dst) (hB : srcB+m≤dst) (hD : dst+len≤lim.space)
    (hreadA : ∀ i<n, μ (srcA+i)=(f i : ℤ))
    (hreadB : ∀ i<m, μ (srcB+i)=(g i : ℤ))
    (hf : ∀ i<n, f i<p) (hg : ∀ i<m, g i<p)
    (hword : ((20*((n+1)*(p+1)^2+len+m+10) : ℕ) : ℤ)≤lim.word) :
    Meets lim P proc depth [srcA,srcB,n,m,len,p,dst] μ (time n p len)
      (fun _ ν => (∀ k<len, ν (dst+k)=(LightPolynomialCoefficient.coefficient p f g n m k : ℤ)) ∧
        SameOutside μ ν dst len) := by
  apply Meets.of_body hp
  unfold body time
  refine Ends.for (Inv μ srcA srcB n m len p dst f g) len
    (LightPolynomialCoefficient.reducedTime n p+90) ?start ?round ?done ?bound
  case start =>
    refine ⟨0,μ,?_,?_,SameOutside.refl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : State))
        ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro k hk; omega
  case round =>
    rintro j _ hj _ ⟨old,ν,rfl,written,kept⟩
    have hwordJ : ((20*((n+1)*(p+1)^2+j+m+10) : ℕ) : ℤ)≤lim.word := by omega
    have hrA (i : ℕ) (hi : i<n) : ν (srcA+i)=(f i : ℤ) :=
      (kept _ (Or.inl (by omega))).trans (hreadA i hi)
    have hrB (i : ℕ) (hi : i<m) : ν (srcB+i)=(g i : ℤ) :=
      (kept _ (Or.inl (by omega))).trans (hreadB i hi)
    have hbudget : (LightPolynomialCoefficient.coefficient p f g n m j : ℤ)≤lim.word := by
      have hh := Nat.mod_le (LightPolynomialCoefficient.rawCoefficient f g n m j) p
      have hb := LightPolynomialCoefficient.raw_bound f g hf hg (j := n) le_rfl (k := j)
      have hfit : n*p^2≤20*((n+1)*(p+1)^2+len+m+10) := by
        have hh : n*p^2≤(n+1)*(p+1)^2 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) 2)
        omega
      exact (Int.ofNat_le.mpr (hh.trans (hb.trans hfit))).trans hword
    light_call (LightPolynomialCoefficient.reduced_meets (depth := depth+1)
      hcoeff hraw hdigit hdivide ν f g hw (by omega) (by omega) (by omega) hrA hrB hf hg hwordJ)
      using LightPolynomialCoefficient.reducedTime with result ν₁ ⟨hresult,hν₁⟩
    subst ν₁
    subst result
    light_store (dst+j) (LightPolynomialCoefficient.coefficient p f g n m j : ℕ)
    refine ⟨by simp,(LightPolynomialCoefficient.coefficient p f g n m j : ℤ),
      Function.update ν (dst+j) (LightPolynomialCoefficient.coefficient p f g n m j : ℤ),
      by simp [update_frame_setLocal],?_,kept.update ⟨by omega,by omega⟩ _⟩
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [Function.update_of_ne (by omega)]
      exact written k hk
    · simp
  case done => rintro _ _ ⟨r,ν,rfl,written,kept⟩; exact ⟨written,kept⟩
  case bound => rintro j _ _ _ ⟨r,ν,rfl,_,_⟩; light_side

end ThreeSum.LightPolynomialProductArray
