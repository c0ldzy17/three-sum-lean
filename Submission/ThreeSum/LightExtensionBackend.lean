import Submission.ThreeSum.LightIrreducibleFinder
import Submission.ThreeSum.LightExtensionMenuMatrix
import Submission.ThreeSum.LightExtensionMenuSemantics
import Submission.ThreeSum.ReportingHostRelocation

noncomputable section
namespace ThreeSum.LightExtensionBackend
open Light TernaryExtensionEncoding
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
noncomputable local instance (Q : Prop) : Decidable Q := Classical.propDecidable Q

def quotientLayout (F : LightExtensionFactorPredicate.Layout) (a b h r prod sum : ℕ) :
    LightExtensionQuotientPredicate.Layout where
  p := F.p
  dim := F.dim
  powers := F.powers
  a := a
  b := b
  modulus := F.target
  h := h
  remainder := r
  productWork := prod
  sumWork := sum

/-- p,dimension,q,powers,target,factorContext,factorLeft,factorRight,
quotientContext,table,logical,physical,a,b,h,remainder,product,sum,J. -/
def body : Stmt :=
  .call 35 [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7] 19 ;;
  .call 36 [v 8,v 0,v 1,v 3,v 12,v 13,v 4,v 14,v 15,v 16,v 17] 20 ;;
  .call 19 [v 2,v 8,v 0,v 1,v 3,v 12,v 13,v 9,v 10,v 11,v 18] 20 ;;
  .set 0 (v 19)

def prelude : Program := ReportingHostRelocation.program LightExtensionMenuMatrix.program LightIrreducibleFinder.program
def program : Program := prelude++[LightArgumentTable.stores 0 10,body]

structure Budget (lim : Limits) (F : LightExtensionFactorPredicate.Layout)
    (q fctx ctx table logical physical J a b h r prod sum T : ℕ) : Prop where
  finder : LightIrreducibleFinder.Budget lim F q fctx T
  targetCtx : F.target+2*F.dim ≤ ctx
  ctxTable : ctx+10 ≤ table
  tableLogical : table+q*q ≤ logical
  logicalPhysical : logical+q*q*(J+2) ≤ physical
  physicalA : physical+q*q*(J+2) ≤ a
  aB : a+F.dim ≤ b
  bH : b+F.dim ≤ h
  hR : h+F.dim ≤ r
  rProduct : r+2*F.dim ≤ prod
  productSum : prod+2*F.dim ≤ sum
  space : sum+2*F.dim ≤ lim.space
  tableWord : (LightExtensionMultiplyTable.word q ctx F.p F.dim F.powers a b : ℤ) ≤ lim.word
  cellWord : (LightExtensionMultiplyCell.word (quotientLayout F a b h r prod sum) q ctx : ℤ) ≤ lim.word
  seedWord : (LightExtensionSeedMatrix.word (J+2) q F.p : ℤ) ≤ lim.word

def time (F : LightExtensionFactorPredicate.Layout) (q J a b h r prod sum T : ℕ) : ℕ :=
  LightIrreducibleFinder.setupTime F q T+
  LightExtensionMenuMatrix.time (quotientLayout F a b h r prod sum) q J+1000

def modulusMonic (F : LightExtensionFactorPredicate.Layout) [Fact F.p.Prime] (c : ℕ) :
    (monicOfCode (p := F.p) F.dim c).Monic := monicCandidate_monic _

variable {lim : Limits}

theorem program_meets (F : LightExtensionFactorPredicate.Layout) [Fact F.p.Prime]
    {q fctx ctx table logical physical J a b h r prod sum T depth : ℕ}
    (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth+13 < lim.depth)
    (B : Budget lim F q fctx ctx table logical physical J a b h r prod sum T)
    (hq : q=F.p^F.dim) :
    Meets lim program 37 depth
      [F.p,F.dim,q,F.powers,F.target,fctx,F.left,F.right,ctx,table,logical,physical,a,b,h,r,prod,sum,J]
      μ (time F q J a b h r prod sum T)
      (fun z ν => ∃ c < q, z=(c+1 : ℕ) ∧ Irreducible (monicOfCode (p := F.p) F.dim c) ∧
        (∀ s < q*q, ∀ i < J+2, ν (physical+s*(J+2)+i)=
          (LightExtensionSeedMatrix.value (encodedMul (modulusMonic F c)) q F.p s
            (TernarySignedLayout.offset J i) : ℤ)) ∧ Kept μ ν F.powers) := by
  let C := quotientLayout F a b h r prod sum
  have hpow := B.finder.powersTarget
  have hdim := B.finder.dimpos
  have hp := B.finder.primeBase
  have hqpos := B.finder.qpos
  have htarget := B.targetCtx
  have hctx := B.ctxTable
  have ht := B.tableLogical
  have hl := B.logicalPhysical
  have hph := B.physicalA
  have hab := B.aB
  have hbh := B.bH
  have hhr := B.hR
  have hrp := B.rProduct
  have hps := B.productSum
  have hspace := B.space
  have hcontrols := B.finder.controls
  have hcontrolsWord := B.seedWord
  unfold LightExtensionSeedMatrix.word at hcontrolsWord
  have hfind := ((ReportingHostRelocation.meets
    (LightIrreducibleFinder.setup_meets F (depth := depth+1) μ hw (by omega) B.finder hq)
    LightExtensionMenuMatrix.program)).append [LightArgumentTable.stores 0 10,body]
  apply Meets.of_body (show program[37]?=some body from rfl)
  unfold body time
  light_call hfind with chosen μ₁ ⟨c,hc,hchosen,hirred,targetValues,powerValues,keep₁⟩
  have hcOneWord : ((c+1 : ℕ) : ℤ) ≤ lim.word := by omega
  have hhead := LightArgumentTable.meets (P := program) (depth := depth+1) (proc := 36) (N := 10)
    rfl (LightExtensionQuotientPredicate.header C) rfl ctx μ₁ hw (by omega)
  light_call hhead using C,quotientLayout,LightExtensionQuotientPredicate.header
    with headerResult μ₂ ⟨hheaderResult,headerValues,keep₂⟩
  have pows₂ (i : ℕ) (hi : i ≤ 2*F.dim) : μ₂ (F.powers+i)=((F.p^i : ℕ) : ℤ) := by
    rw [keep₂ _ (Or.inl (by omega)),powerValues i hi]
  have target₂ (i : ℕ) (hi : i < F.dim+1) : μ₂ (F.target+i)=(codeDigits (p := F.p) (c+q) i : ℤ) := by
    rw [keep₂ _ (Or.inl (by omega)),targetValues i (by omega)]
  have hdegree : (monicOfCode (p := F.p) F.dim c).natDegree=F.dim := monicCandidate_degree _
  have hm : monicOfCode (p := F.p) (monicOfCode (p := F.p) F.dim c).natDegree c=
      monicOfCode (p := F.p) F.dim c := by rw [hdegree]
  have hspec := LightExtensionFieldMultiply.actual_quotient_spec (p := F.p)
    (f := monicOfCode (p := F.p) F.dim c) C rfl hdegree.symm
    (modulusMonic F c) (by omega) (by simpa [hdegree,←hq] using hc) hm
  have hspec' : ∀ x < q, ∀ y < q,
      let z := LightPairSearch.first (LightPairSearch.goodCode q
        (LightExtensionQuotientSearch.good C (LightExtensionQuotientPredicate.digits C.p x)
          (LightExtensionQuotientPredicate.digits C.p y) (codeDigits (p := F.p) (c+q)))) (q*q)
      0 < z ∧ z ≤ q*q ∧ (z-1)%q=encodedMul (modulusMonic F c) x y := by
    simpa [hdegree,←hq] using hspec
  have hmul : ∀ x < q, ∀ y < q, encodedMul (modulusMonic F c) x y < q := by
    intro x hx y hy
    simpa [hdegree,←hq] using encodedMul_lt (modulusMonic F c) x y
  have targetBound (i : ℕ) (_hi : i < F.dim+1) : codeDigits (p := F.p) (c+q) i < F.p :=
    Nat.mod_lt _ (by omega)
  have hmenu := (LightExtensionMenuMatrix.program_meets (depth := depth+1) C μ₂
    (codeDigits (p := F.p) (c+q)) (encodedMul (modulusMonic F c)) hw (by omega) hp hqpos
    headerValues hctx (by dsimp [C,quotientLayout]; omega) (by dsimp [C,quotientLayout]; omega)
    ht hl hph hab hbh hhr hrp hps hspace pows₂ target₂ targetBound
    B.tableWord B.cellWord B.seedWord hmul hspec').append
      (LightIrreducibleFinder.program.map (ReportingHostRelocation.relocate 20)++[LightArgumentTable.stores 0 10,body])
  have hmenu' : Meets lim program 19 (depth+1)
      [q,ctx,F.p,F.dim,F.powers,a,b,table,logical,physical,J] μ₂
      (LightExtensionMenuMatrix.time C q J)
      (fun _ ν => (∀ s < q*q, ∀ i < J+2, ν (physical+s*(J+2)+i)=
        (LightExtensionSeedMatrix.value (encodedMul (modulusMonic F c)) q F.p s
          (TernarySignedLayout.offset J i) : ℤ)) ∧ Kept μ₂ ν table) := by
    have hlen : LightExtensionMenuMatrix.program.length=20 := rfl
    simpa only [program,prelude,ReportingHostRelocation.program,hlen,List.append_assoc,C,quotientLayout] using hmenu
  light_call hmenu' using C,quotientLayout with out ν ⟨values,keep₃⟩
  light_set (c+1 : ℕ) using hchosen,C,quotientLayout
  refine ⟨c,hc,by simp,hirred,values,?_⟩
  intro x hx
  exact (keep₃ x (by omega)).trans ((keep₂ x (Or.inl (by omega))).trans (keep₁ x hx))

end ThreeSum.LightExtensionBackend
