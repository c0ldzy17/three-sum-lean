import Submission.ThreeSum.LightPrimeCoefficient
import Submission.ThreeSum.LightCoefficientDecode

namespace ThreeSum.LightPrimeAddArray
open Light
set_option maxHeartbeats 2000000

def body (pMulAdd : ℕ) : Stmt :=
  .for 5 (v 3) (
    .call pMulAdd [M (v 0 +' v 5),k 1,M (v 1 +' v 5),v 4] 6 ;;
    .store (v 2 +' v 5) (v 6))

def time (n p : ℕ) : ℕ := n*(LightPrimeCoefficient.mulAddTime p+60)+10

def Inv (μ : ℕ → ℤ) (srcA srcB dst n p : ℕ) (f g : ℕ → ℕ)
    (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ), σ=⟨frame [srcA,srcB,dst,n,p,i,r],ν⟩ ∧
    (∀ j < i, ν (dst+j)=(((f j+g j)%p : ℕ) : ℤ)) ∧ SameOutside μ ν dst n

variable {lim : Limits} {P : Program} {depth : ℕ}

theorem meets {proc pMulAdd pDivide srcA srcB dst n p : ℕ}
    (hp : P[proc]?=some (body pMulAdd))
    (hadd : P[pMulAdd]?=some (LightPrimeCoefficient.mulAddBody pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (μ : ℕ → ℤ) (f g : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+1<lim.depth) (hpp : 1<p)
    (hA : srcA+n≤dst) (hB : srcB+n≤dst) (hD : dst+n≤lim.space)
    (hreadA : ∀ i<n, μ (srcA+i)=(f i : ℤ))
    (hreadB : ∀ i<n, μ (srcB+i)=(g i : ℤ))
    (hf : ∀ i<n, f i<p) (hg : ∀ i<n, g i<p)
    (hword : (LightPrimeCoefficient.word p : ℤ)≤lim.word) :
    Meets lim P proc depth [srcA,srcB,dst,n,p] μ (time n p)
      (fun _ ν => (∀ i<n, ν (dst+i)=(((f i+g i)%p : ℕ) : ℤ)) ∧ SameOutside μ ν dst n) := by
  have hpWord : (p : ℤ)≤lim.word := by
    have hh : p≤LightPrimeCoefficient.word p := by unfold LightPrimeCoefficient.word; nlinarith
    exact (Int.ofNat_le.mpr hh).trans hword
  have h1 : (1 : ℤ)≤lim.word := by omega
  apply Meets.of_body hp
  unfold body time
  refine Ends.for (Inv μ srcA srcB dst n p f g) n
    (LightPrimeCoefficient.mulAddTime p+50) ?start ?round ?done ?bound
  case start =>
    refine ⟨0,μ,?_,?_,SameOutside.refl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : State))
        ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro j hj; omega
  case round =>
    rintro j _ hj _ ⟨old,ν,rfl,written,kept⟩
    have hrA : ν (srcA+j)=(f j : ℤ) := (kept _ (Or.inl (by omega))).trans (hreadA j hj)
    have hrB : ν (srcB+j)=(g j : ℤ) := (kept _ (Or.inl (by omega))).trans (hreadB j hj)
    have hf' := hf j hj
    have hg' := hg j hj
    have hfw : (f j : ℤ)≤lim.word := (by exact_mod_cast (Nat.le_of_lt hf') : (f j : ℤ)≤(p : ℤ)).trans hpWord
    have hgw : (g j : ℤ)≤lim.word := (by exact_mod_cast (Nat.le_of_lt hg') : (g j : ℤ)≤(p : ℤ)).trans hpWord
    have hresWord : (((f j+g j)%p : ℕ) : ℤ)≤lim.word :=
      (by exact_mod_cast Nat.le_of_lt (Nat.mod_lt _ (by omega : 0<p)) : (((f j+g j)%p : ℕ) : ℤ)≤(p : ℤ)).trans hpWord
    light_call (LightPrimeCoefficient.mulAdd_meets (d := depth+1)
      (acc := f j) (x := 1) (y := g j) (p := p) hadd hdivide ν (by omega) (by omega) hf' hpp hg' hword)
      using hrA,hrB,LightPrimeCoefficient.mulAddTime with result ν₁ ⟨hresult,hν₁⟩
    subst ν₁
    have hr : result=(((f j+g j)%p : ℕ) : ℤ) := by simpa using hresult
    light_store (dst+j) ((f j+g j)%p : ℕ) using hr,LightPrimeCoefficient.mulAddTime
    refine ⟨by simp,result,Function.update ν (dst+j) (((f j+g j)%p : ℕ) : ℤ),
      by simp [update_frame_setLocal],?_,kept.update ⟨by omega,by omega⟩ _⟩
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Function.update_of_ne (by omega)]
      exact written i hi
    · simp
  case done => rintro _ _ ⟨r,ν,rfl,written,kept⟩; exact ⟨written,kept⟩
  case bound => rintro j _ _ _ ⟨r,ν,rfl,_,_⟩; light_side

end ThreeSum.LightPrimeAddArray
