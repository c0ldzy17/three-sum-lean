import Submission.ThreeSum.LightExtensionFactorPredicate
import Submission.ThreeSum.LightPairSearchProgram

noncomputable section
namespace ThreeSum.LightExtensionFactorSearch
open Light LightExtensionFactorPredicate
set_option maxHeartbeats 1000000
variable {lim : Limits}
noncomputable local instance (Q : Prop) : Decidable Q := Classical.propDecidable Q

def good (C : Layout) (f : ℕ → ℕ) (u v : ℕ) : Prop :=
  u<C.p^C.degree ∧ v<C.p^(C.dim-C.degree) ∧
    LightPolynomialProductCheck.Valid C.p
      (LightExtensionFactorCheck.digits C.p (u+C.p^C.degree))
      (LightExtensionFactorCheck.digits C.p (v+C.p^(C.dim-C.degree))) f
      (C.degree+1) (C.dim-C.degree+1) (2*C.dim)

theorem result_flag (C : Layout) (f : ℕ → ℕ) (u v : ℕ) :
    result C f u v=(if good C f u v then 1 else 0) := by
  by_cases hu : u<C.p^C.degree
  · by_cases hv : v<C.p^(C.dim-C.degree)
    · by_cases hval : LightPolynomialProductCheck.Valid C.p
        (LightExtensionFactorCheck.digits C.p (u+C.p^C.degree))
        (LightExtensionFactorCheck.digits C.p (v+C.p^(C.dim-C.degree))) f
        (C.degree+1) (C.dim-C.degree+1) (2*C.dim)
      · simp [result,LightPolynomialProductCheck.flag,good,hu,hv,hval]
      · simp [result,LightPolynomialProductCheck.flag,good,hu,hv,hval]
    · simp [result,good,hu,hv]
  · simp [result,good,hu]

def program : Program := LightPairSearch.program LightExtensionFactorPredicate.program 0

/-- Ten actual procedures search all properly bounded monic factor codes.
The exhaustive loops include coefficient decoding and product checks. -/
theorem program_meets (C : Layout) {ctx q depth : ℕ} (μ : ℕ → ℤ) (f : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+6<lim.depth)
    (hq : 0<q) (hp : 1<C.p) (he : 0<C.degree) (hed : C.degree<C.dim)
    (H : Seg μ ctx (header C)) (hctx : ctx+7≤C.left)
    (hpow : C.powers+(2*C.dim+1)≤C.left)
    (htarget : C.target+2*C.dim≤C.left) (hleft : C.left+2*C.dim≤C.right)
    (hspace : C.right+2*C.dim≤lim.space)
    (hpowRead : ∀ i≤2*C.dim, μ (C.powers+i)=((C.p^i : ℕ) : ℤ))
    (hfRead : ∀ i<2*C.dim, μ (C.target+i)=(f i : ℤ))
    (hword : (word C q q : ℤ)≤lim.word)
    (hsearchWord : ((q*q+q+ctx+20 : ℕ) : ℤ)≤lim.word) :
    Meets lim program 9 depth [q,ctx] μ
      (q*q*(time C q q+200)+100)
      (fun r ν => r=(LightPairSearch.first (LightPairSearch.goodCode q (good C f)) (q*q) : ℤ) ∧
        Kept μ ν C.left) := by
  let I := fun ν : ℕ → ℤ => Kept μ ν C.left
  apply LightPairSearch.program_meets LightExtensionFactorPredicate.program 0
    (good C f) I hq μ (fun _ _ => rfl) hsearchWord (by omega)
  intro u hu v hv ν hν
  have Hν : Seg ν ctx (header C) := by
    intro i hi
    have hi' : i<7 := by simpa [header] using hi
    exact (hν _ (by omega)).trans (H i hi)
  have hpowν (i : ℕ) (hi : i≤2*C.dim) : ν (C.powers+i)=((C.p^i : ℕ) : ℤ) :=
    (hν _ (by omega)).trans (hpowRead i hi)
  have hfν (i : ℕ) (hi : i<2*C.dim) : ν (C.target+i)=(f i : ℤ) :=
    (hν _ (by omega)).trans (hfRead i hi)
  have hwuv : (word C u v : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (word_mono C hu.le hv.le)).trans hword
  have hc := LightExtensionFactorPredicate.procs.meets (depth := depth+2) C ν f hw (by omega)
    hp he hed Hν hctx hpow htarget hleft hspace hpowν hfν hwuv
  apply hc.mono (time_mono C hu.le hv.le)
  rintro r ξ ⟨hr,hkeep⟩
  refine ⟨hr.trans (result_flag C f u v),?_⟩
  intro a ha
  exact (hkeep a ha).trans (hν a ha)

/-- With a code range covering all bounded coefficient vectors, no hit
means no proper monic factor pair at this degree, with no residual code cutoff. -/
theorem nohit_all (C : Layout) (f : ℕ → ℕ) (q : ℕ) (hq : 0<q)
    (hp : 1≤C.p) (he : C.degree≤C.dim) (hcodes : C.p^C.dim≤q) :
    LightPairSearch.first (LightPairSearch.goodCode q (good C f)) (q*q)=0 ↔
      ∀ u v, ¬good C f u v := by
  rw [(LightPairSearch.first_pair_spec q hq (good C f)).1]
  constructor
  · intro h u v hg
    have hu : u<q := hg.1.trans_le ((Nat.pow_le_pow_right hp he).trans hcodes)
    have hv : v<q := hg.2.1.trans_le ((Nat.pow_le_pow_right hp (Nat.sub_le _ _)).trans hcodes)
    exact h u hu v hv hg
  · intro h u hu v hv
    exact h u v

end ThreeSum.LightExtensionFactorSearch
