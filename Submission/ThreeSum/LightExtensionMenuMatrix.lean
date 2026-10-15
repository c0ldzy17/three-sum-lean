import Submission.ThreeSum.LightExtensionMultiplyTable
import Submission.ThreeSum.LightExtensionSeedMatrix
import Submission.ThreeSum.LightSignedCoefficientMatrix

noncomputable section
namespace ThreeSum.LightExtensionMenuMatrix
open Light
set_option maxHeartbeats 5000000
set_option maxRecDepth 6000
noncomputable local instance (Q : Prop) : Decidable Q := Classical.propDecidable Q

/-- q,context,p,dimension,powers,left,right,table,logical,physical,J. -/
def body (pTable pSeeds pPermute : ℕ) : Stmt :=
  .call pTable [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7] 11 ;;
  .call pSeeds [v 7,v 0,v 2,v 8,v 10 +' k 2] 11 ;;
  .call pPermute [v 8,v 9,v 0 *' v 0,v 10] 11

def extra : Program :=
  [LightExtensionSeedRow.body 2,LightExtensionSeedMatrix.body 15 2 3,
    LightSignedCoefficientLayout.body,LightSignedCoefficientMatrix.body 17,body 14 16 18]

def program : Program := LightExtensionMultiplyTable.program++extra

def time (C : LightExtensionQuotientPredicate.Layout) (q J : ℕ) : ℕ :=
  LightExtensionMultiplyTable.time q (LightExtensionMultiplyCell.time C q)+
  LightExtensionSeedMatrix.time (J+2) q+LightSignedCoefficientMatrix.time (q*q) J+500

variable {lim : Limits}

theorem program_meets {ctx q table logical physical J depth : ℕ}
    (C : LightExtensionQuotientPredicate.Layout) (μ : ℕ → ℤ)
    (f : ℕ → ℕ) (mul : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth+9 < lim.depth)
    (hp : 1 < C.p) (hq : 0 < q)
    (H : Seg μ ctx (LightExtensionQuotientPredicate.header C))
    (hctx : ctx+10 ≤ table) (hpow : C.powers+(2*C.dim+1) ≤ table)
    (hmod : C.modulus+(C.dim+1) ≤ table)
    (htable : table+q*q ≤ logical) (hlogical : logical+q*q*(J+2) ≤ physical)
    (hphysical : physical+q*q*(J+2) ≤ C.a)
    (hab : C.a+C.dim ≤ C.b) (hbh : C.b+C.dim ≤ C.h)
    (hh : C.h+C.dim ≤ C.remainder) (hr : C.remainder+2*C.dim ≤ C.productWork)
    (hprod : C.productWork+2*C.dim ≤ C.sumWork)
    (hspace : C.sumWork+2*C.dim ≤ lim.space)
    (hpowRead : ∀ i ≤ 2*C.dim, μ (C.powers+i)=((C.p^i : ℕ) : ℤ))
    (hfRead : ∀ i < C.dim+1, μ (C.modulus+i)=(f i : ℤ))
    (hfBound : ∀ i < C.dim+1, f i < C.p)
    (hword : (LightExtensionMultiplyTable.word q ctx C.p C.dim C.powers C.a C.b : ℤ) ≤ lim.word)
    (hcellWord : (LightExtensionMultiplyCell.word C q ctx : ℤ) ≤ lim.word)
    (hseedWord : (LightExtensionSeedMatrix.word (J+2) q C.p : ℤ) ≤ lim.word)
    (hmul : ∀ x < q, ∀ y < q, mul x y < q)
    (hspec : ∀ a < q, ∀ b < q,
      let z := LightPairSearch.first (LightPairSearch.goodCode q
        (LightExtensionQuotientSearch.good C (LightExtensionQuotientPredicate.digits C.p a)
          (LightExtensionQuotientPredicate.digits C.p b) f)) (q*q)
      0 < z ∧ z ≤ q*q ∧ (z-1)%q=mul a b) :
    Meets lim program 19 depth
      [q,ctx,C.p,C.dim,C.powers,C.a,C.b,table,logical,physical,J] μ (time C q J)
      (fun _ ν => (∀ r < q*q, ∀ i < J+2,
        ν (physical+r*(J+2)+i)=
          (LightExtensionSeedMatrix.value mul q C.p r (TernarySignedLayout.offset J i) : ℤ)) ∧
        Kept μ ν table) := by
  have hqWord : ((q*q : ℕ) : ℤ) ≤ lim.word := by
    unfold LightExtensionSeedMatrix.word at hseedWord; omega
  have hJWord : ((J+2 : ℕ) : ℤ) ≤ lim.word := by
    unfold LightExtensionSeedMatrix.word at hseedWord; omega
  have hpWord : (C.p : ℤ) ≤ lim.word := by
    unfold LightExtensionSeedMatrix.word at hseedWord; omega
  have hc := (LightExtensionMultiplyTable.program_meets C μ f mul hw (by omega) hp hq
    H hctx hpow hmod (by omega) hab hbh hh hr hprod hspace hpowRead hfRead hfBound
    hword hcellWord hmul hspec).append extra
  apply Meets.of_body (show program[19]?=some (body 14 16 18) from rfl)
  unfold body time
  light_call hc with X μ₁ ⟨tableValues,keep₁⟩
  light_call (LightExtensionSeedMatrix.meets (depth := depth+1)
    (table := table) (q := q) (p := C.p) (dst := logical) (len := J+2)
    (show program[16]?=some (LightExtensionSeedMatrix.body 15 2 3) from rfl)
    (show program[15]?=some (LightExtensionSeedRow.body 2) from rfl)
    (show program[2]?=some (LightRadixDigit.body 3) from rfl)
    (show program[3]?=some LightSmallDivide.body from rfl)
    μ₁ mul hw (by omega) hq (by omega) htable (by omega) tableValues hmul hseedWord)
    with Y μ₂ ⟨seedValues,keep₂⟩
  let coeff := fun r i => (LightExtensionSeedMatrix.value mul q C.p r i : ℤ)
  have coeffBound (r : ℕ) (hr : r < q*q) (i : ℕ) (hi : i < J+2) : |coeff r i| ≤ (C.p : ℤ) := by
    change |((LightExtensionSeedMatrix.value mul q C.p r i : ℕ) : ℤ)| ≤ (C.p : ℤ)
    rw [abs_of_nonneg (Int.natCast_nonneg _)]
    unfold LightExtensionSeedMatrix.value
    exact_mod_cast (Nat.mod_lt (LightExtensionSeedRow.trajectory mul (r/q) (r%q) i) (by omega)).le
  light_call (LightSignedCoefficientMatrix.meets (depth := depth+1)
    (src := logical) (dst := physical) (rows := q*q) (J := J) (U := C.p)
    (show program[18]?=some (LightSignedCoefficientMatrix.body 17) from rfl)
    (show program[17]?=some LightSignedCoefficientLayout.body from rfl)
    μ₂ coeff hw (by omega) hlogical (by omega) seedValues coeffBound hpWord hqWord hJWord)
    with Z ν ⟨values,keep₃⟩
  refine ⟨values,?_⟩
  intro a ha
  exact (keep₃ a (Or.inl (by omega))).trans ((keep₂ a (Or.inl (by omega))).trans (keep₁ a ha))

end ThreeSum.LightExtensionMenuMatrix
