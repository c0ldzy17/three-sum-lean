import Submission.ThreeSum.LightExtensionQuotientPredicate
import Submission.ThreeSum.LightPairSearchProgram

noncomputable section
namespace ThreeSum.LightExtensionQuotientSearch
open Light
open LightExtensionQuotientPredicate
set_option maxHeartbeats 1000000
variable {lim : Limits}

noncomputable local instance (Q : Prop) : Decidable Q := Classical.propDecidable Q

def good (C : Layout) (x y f : ℕ → ℕ) (u v : ℕ) : Prop :=
  LightPolynomialProductCheck.Valid C.p x y
    (LightPolynomialQuotientCheck.expected C.p C.dim (digits C.p u) f (digits C.p v))
    C.dim C.dim (2*C.dim)

def program : Program := LightPairSearch.program LightExtensionQuotientPredicate.program 0

theorem time_mono (dim p u v q : ℕ) (hu : u≤q) (hv : v≤q) :
    LightExtensionQuotientPredicate.time dim p u v ≤ LightExtensionQuotientPredicate.time dim p q q := by
  unfold LightExtensionQuotientPredicate.time LightCoefficientDecode.time LightRadixDigit.time
  have h0 := Nat.mul_le_mul_left dim hu
  have h1 := Nat.mul_le_mul_left (2*dim) hv
  nlinarith

theorem word_mono (dim p u v q : ℕ) (hu : u≤q) (hv : v≤q) :
    LightExtensionQuotientPredicate.word dim p u v ≤ LightExtensionQuotientPredicate.word dim p q q := by
  unfold LightExtensionQuotientPredicate.word LightCoefficientDecode.word
  omega

/-- Thirteen real procedures search quotient/remainder codes. The coefficient
decoders and all polynomial arithmetic are included and charged on every call. -/
theorem program_meets (C : Layout) {ctx q depth : ℕ}
    (μ : ℕ → ℤ) (x y f : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+6<lim.depth)
    (hq : 0<q) (hp : 1<C.p)
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
    (hword : (LightExtensionQuotientPredicate.word C.dim C.p q q : ℤ)≤lim.word)
    (hsearchWord : ((q*q+q+ctx+20 : ℕ) : ℤ)≤lim.word) :
    Meets lim program 12 depth [q,ctx] μ
      (q*q*(LightExtensionQuotientPredicate.time C.dim C.p q q+200)+100)
      (fun r ν => r=(LightPairSearch.first (LightPairSearch.goodCode q (good C x y f)) (q*q) : ℤ) ∧
        Kept μ ν C.h) := by
  let I := fun ν : ℕ → ℤ => Kept μ ν C.h
  apply LightPairSearch.program_meets LightExtensionQuotientPredicate.program 0
    (good C x y f) I hq μ (fun _ _ => rfl) hsearchWord (by omega)
  intro u hu v hv ν hν
  have Hν := header_kept H hctx hν
  have hpowν (e : ℕ) (he : e≤2*C.dim) : ν (C.powers+e)=((C.p^e : ℕ) : ℤ) :=
    (hν _ (by omega)).trans (hpowRead e he)
  have hxν (i : ℕ) (hi : i<C.dim) : ν (C.a+i)=(x i : ℤ) :=
    (hν _ (by omega)).trans (hxRead i hi)
  have hyν (i : ℕ) (hi : i<C.dim) : ν (C.b+i)=(y i : ℤ) :=
    (hν _ (by omega)).trans (hyRead i hi)
  have hfν (i : ℕ) (hi : i<C.dim+1) : ν (C.modulus+i)=(f i : ℤ) :=
    (hν _ (by omega)).trans (hfRead i hi)
  have hwuv : (LightExtensionQuotientPredicate.word C.dim C.p u v : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (word_mono C.dim C.p u v q hu.le hv.le)).trans hword
  have hc := LightExtensionQuotientPredicate.procs.meets (depth := depth+2) C ν x y f
    hw (by omega) hp Hν hctx hpowers hpowν ha hb hf hh hr hprod hspace
    hxν hyν hfν hxBound hyBound hfBound hwuv
  apply hc.mono (time_mono C.dim C.p u v q hu.le hv.le)
  rintro r ξ ⟨hr,hkeep⟩
  refine ⟨?_,?_⟩
  · unfold result LightPolynomialProductCheck.flag at hr
    unfold good
    split_ifs at hr ⊢ <;> first | exact hr | contradiction
  · intro a ha
    exact (hkeep a ha).trans (hν a ha)

end ThreeSum.LightExtensionQuotientSearch
