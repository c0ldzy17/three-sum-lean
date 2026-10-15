import Submission.ThreeSum.TernaryArenaPairMass
import Submission.ThreeSum.LightTernaryDimensionsBudget
import Submission.ThreeSum.LightTernaryInitialBudgets
import Submission.ThreeSum.TernaryMomentWeightBounds
import Submission.ThreeSum.TernaryArenaCapacity
import Submission.ThreeSum.LightTernaryPairedPotential
import Submission.ThreeSum.TernaryMomentChannelResources
import Submission.ThreeSum.LightTernaryAppendKeys

noncomputable section
namespace ThreeSum.TernaryArenaPrefixFootprints
open TernaryArenaLayout TernaryArenaPairMass TernarySignedPadding
open TernaryCoverGoodMaps TernaryLocalParameters TernaryNativeCompleteFrontend
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

/-- Pointwise polynomial growth, uniformly over every executed prefix. -/
def Uniform (M : ℕ) (f : ℕ→ℕ→ℕ→ℕ) : Prop :=
  ∃ D E : ℕ, ∀ n U j, j≤Nat.clog M (n^2) → f n U j≤D*(n+U+1)^E

theorem Uniform.const (M c : ℕ) : Uniform M (fun _ _ _=>c) :=
  ⟨c,0,by simp⟩
theorem Uniform.add {M : ℕ} {f g : ℕ→ℕ→ℕ→ℕ}
    (hf : Uniform M f) (hg : Uniform M g) : Uniform M (fun n U j=>f n U j+g n U j) := by
  obtain ⟨D,E,hf⟩:=hf
  obtain ⟨D',E',hg⟩:=hg
  refine ⟨D+D',max E E',fun n U j hj=>?_⟩
  have hp : 1≤n+U+1 := by omega
  have h1 := (hf n U j hj).trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_right hp (le_max_left E E')))
  have h2 := (hg n U j hj).trans (Nat.mul_le_mul_left D' (Nat.pow_le_pow_right hp (le_max_right E E')))
  change f n U j+g n U j≤_
  rw [add_mul]
  omega

theorem Uniform.mul {M : ℕ} {f g : ℕ→ℕ→ℕ→ℕ}
    (hf : Uniform M f) (hg : Uniform M g) : Uniform M (fun n U j=>f n U j*g n U j) := by
  obtain ⟨D,E,hf⟩:=hf
  obtain ⟨D',E',hg⟩:=hg
  refine ⟨D*D',E+E',fun n U j hj=>?_⟩
  simpa [pow_add,mul_assoc,mul_left_comm,mul_comm] using Nat.mul_le_mul (hf n U j hj) (hg n U j hj)

theorem Uniform.pow {M : ℕ} {f : ℕ→ℕ→ℕ→ℕ} (hf : Uniform M f) (k : ℕ) :
    Uniform M (fun n U j=>(f n U j)^k) := by
  obtain ⟨D,E,hf⟩:=hf
  refine ⟨D^k,E*k,fun n U j hj=>?_⟩
  simpa [mul_pow,←pow_mul] using Nat.pow_le_pow_left (hf n U j hj) k

theorem Uniform.succ {M : ℕ} {f : ℕ→ℕ→ℕ→ℕ} (hf : Uniform M f) :
    Uniform M (fun n U j=>Nat.succ (f n U j)) :=
  hf.add (Uniform.const M 1)

theorem Uniform.mono {M : ℕ} {f g : ℕ→ℕ→ℕ→ℕ}
    (hg : Uniform M g) (h : ∀ n U j, j≤Nat.clog M (n^2) → f n U j≤g n U j) : Uniform M f := by
  obtain ⟨D,E,hg⟩:=hg
  exact ⟨D,E,fun n U j hj=>(h n U j hj).trans (hg n U j hj)⟩

theorem inputN (M : ℕ) : Uniform M (fun n _ _=>n) := ⟨1,1,by intros; simp; omega⟩
theorem inputU (M : ℕ) : Uniform M (fun _ U _=>U) := ⟨1,1,by intros; simp; omega⟩
theorem prefixCount {M : ℕ} (hM : 1<M) : Uniform M (fun _ _ j=>j) := by
  refine (inputN M |>.pow 2).mono ?_
  intro n U j hj
  exact hj.trans (LightTernaryDimensions.r_le hM n)

theorem digits {M b : ℕ} (hM : 1<M) (hb : 1<b) :
    Uniform M (fun n U _=>LightTernaryDimensions.J M b n U) := by
  refine (((inputN M |>.pow 2).add ((Uniform.const M 4).mul (inputU M))).add (Uniform.const M 3)).mono ?_
  intro n U j hj
  exact LightTernaryDimensions.J_le hM hb n U

theorem alphabet {M : ℕ} (hM : 1<M) (A : ℕ) : Uniform M (fun _ _ j=>A^j) := by
  refine ⟨M^(A+1),2*(A+1),fun n U j hj=>?_⟩
  have hh := (Nat.pow_le_pow_left (Nat.le_succ A) j).trans
    ((Nat.pow_le_pow_right (by omega : 1≤A+1) hj).trans (fixed_pow_clog M (A+1) n hM))
  exact hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : n+1≤n+U+1) _))

theorem alphabet_final {M : ℕ} (hM : 1<M) (A : ℕ) :
    Uniform M (fun n _ _=>A^(Nat.clog M (n^2))) := by
  obtain ⟨D,E,h⟩ := alphabet hM A
  exact ⟨D,E,fun n U j _=>h n U _ le_rfl⟩

theorem carries {M b : ℕ} (hM : 1<M) (hb : 1<b) :
    Uniform M (fun n U _=>2^(LightTernaryDimensions.J M b n U)) := by
  have hdigit : Uniform M (fun _ U _=>2^(Nat.clog b (4*U+1))) := by
    refine (((Uniform.const M b).mul (((Uniform.const M 4).mul (inputU M)).add (Uniform.const M 1)))).mono ?_
    intro n U j hj
    exact (Nat.pow_le_pow_left (by omega : 2≤b) _).trans
      (clog_power_bound hb (by omega : 0<4*U+1))
  have hfull := (hdigit.mul (alphabet_final hM 2)).mul (Uniform.const M 2)
  convert hfull using 1
  funext n U j
  simp [LightTernaryDimensions.J,LightTernaryDimensions.r,paddedLength,digitLength,pow_add,pow_succ]

/-- All fixed-degree scoring and reporting channels use this common cap. -/
def weight (H wordRadix U : ℕ) : ℕ :=
  TernaryMomentWeightBounds.leftBound U (2*H)+(2*wordRadix+1)^2

def sourceWidth {p m F : ℕ} [Fact p.Prime] (maps : Fin F→Weight m p) (cap : ℕ) : ℕ :=
  (localRecords maps cap false).length+(localRecords maps cap true).length+1

def wantedWidth {p m F : ℕ} [Fact p.Prime] (maps : Fin F→Weight m p) (τ : ℕ) : ℕ :=
  (TernaryGoodOutputCatalog.raws maps τ).length+F*TernaryGoodOutputCatalog.cap m p τ+1

/-- Every scalar in this record is a literal, positive arithmetic upper
bound for one of the actual source, count, tensor, span or budget kernels. -/
structure Numbers where
  localSize : ℕ
  radixCells : ℕ
  joinCells : ℕ
  hits : ℕ
  sourceHistogram : ℕ
  sourceWord : ℕ
  prefixCells : ℕ
  bankCells : ℕ
  nearMetadata : ℕ
  nearDivision : ℕ
  frontendWord : ℕ
  tensorCells : ℕ
  tensorWord : ℕ
  potentialWord : ℕ
  spanCells : ℕ
  originalMatrixCells : ℕ
  menuCells : ℕ
  budgets : ℕ
  depth : ℕ
  reporterWord : ℕ
  reporterCells : ℕ
  candidateScore : ℕ
  prefixHeader : ℕ

def Numbers.list (A : Numbers) : List ℕ :=
  [A.localSize,A.radixCells,A.joinCells,A.hits,A.sourceHistogram,A.sourceWord,
   A.prefixCells,A.bankCells,A.nearMetadata,A.nearDivision,A.frontendWord,
   A.tensorCells,A.tensorWord,A.potentialWord,A.spanCells,A.originalMatrixCells,
   A.menuCells,A.budgets,A.depth,A.reporterWord,A.reporterCells,A.candidateScore,A.prefixHeader]

def Fits (C : ℕ) (A : Numbers) : Prop := ∀v∈A.list, v≤C

theorem Fits.localSize {C : ℕ} {A : Numbers} (h : Fits C A) : A.localSize≤C :=
  h _ (by simp [Numbers.list])

theorem Fits.radixCells {C : ℕ} {A : Numbers} (h : Fits C A) : A.radixCells≤C :=
  h _ (by simp [Numbers.list])

theorem Fits.joinCells {C : ℕ} {A : Numbers} (h : Fits C A) : A.joinCells≤C :=
  h _ (by simp [Numbers.list])

theorem Fits.hits {C : ℕ} {A : Numbers} (h : Fits C A) : A.hits≤C :=
  h _ (by simp [Numbers.list])

theorem Fits.sourceHistogram {C : ℕ} {A : Numbers} (h : Fits C A) : A.sourceHistogram≤C :=
  h _ (by simp [Numbers.list])

theorem Fits.sourceWord {C : ℕ} {A : Numbers} (h : Fits C A) : A.sourceWord≤C :=
  h _ (by simp [Numbers.list])

theorem Fits.prefixCells {C : ℕ} {A : Numbers} (h : Fits C A) : A.prefixCells≤C :=
  h _ (by simp [Numbers.list])

theorem Fits.bankCells {C : ℕ} {A : Numbers} (h : Fits C A) : A.bankCells≤C :=
  h _ (by simp [Numbers.list])

theorem Fits.nearMetadata {C : ℕ} {A : Numbers} (h : Fits C A) : A.nearMetadata≤C :=
  h _ (by simp [Numbers.list])

theorem Fits.nearDivision {C : ℕ} {A : Numbers} (h : Fits C A) : A.nearDivision≤C :=
  h _ (by simp [Numbers.list])

theorem Fits.frontendWord {C : ℕ} {A : Numbers} (h : Fits C A) : A.frontendWord≤C :=
  h _ (by simp [Numbers.list])

theorem Fits.tensorCells {C : ℕ} {A : Numbers} (h : Fits C A) : A.tensorCells≤C :=
  h _ (by simp [Numbers.list])

theorem Fits.tensorWord {C : ℕ} {A : Numbers} (h : Fits C A) : A.tensorWord≤C :=
  h _ (by simp [Numbers.list])

theorem Fits.potentialWord {C : ℕ} {A : Numbers} (h : Fits C A) : A.potentialWord≤C :=
  h _ (by simp [Numbers.list])

theorem Fits.spanCells {C : ℕ} {A : Numbers} (h : Fits C A) : A.spanCells≤C :=
  h _ (by simp [Numbers.list])

theorem Fits.originalMatrixCells {C : ℕ} {A : Numbers} (h : Fits C A) : A.originalMatrixCells≤C :=
  h _ (by simp [Numbers.list])

theorem Fits.menuCells {C : ℕ} {A : Numbers} (h : Fits C A) : A.menuCells≤C :=
  h _ (by simp [Numbers.list])

theorem Fits.budgets {C : ℕ} {A : Numbers} (h : Fits C A) : A.budgets≤C :=
  h _ (by simp [Numbers.list])

theorem Fits.depth {C : ℕ} {A : Numbers} (h : Fits C A) : A.depth≤C :=
  h _ (by simp [Numbers.list])

theorem Fits.reporterWord {C : ℕ} {A : Numbers} (h : Fits C A) : A.reporterWord≤C :=
  h _ (by simp [Numbers.list])

theorem Fits.reporterCells {C : ℕ} {A : Numbers} (h : Fits C A) : A.reporterCells≤C :=
  h _ (by simp [Numbers.list])

theorem Fits.candidateScore {C : ℕ} {A : Numbers} (h : Fits C A) : A.candidateScore≤C :=
  h _ (by simp [Numbers.list])

theorem Fits.prefixHeader {C : ℕ} {A : Numbers} (h : Fits C A) : A.prefixHeader≤C :=
  h _ (by simp [Numbers.list])

theorem Numbers.sum_list (A : Numbers) : A.list.sum=A.localSize+(A.radixCells+(A.joinCells+(A.hits+(A.sourceHistogram+(A.sourceWord+(A.prefixCells+(A.bankCells+(A.nearMetadata+(A.nearDivision+(A.frontendWord+(A.tensorCells+(A.tensorWord+(A.potentialWord+(A.spanCells+(A.originalMatrixCells+(A.menuCells+(A.budgets+(A.depth+(A.reporterWord+(A.reporterCells+(A.candidateScore+(A.prefixHeader+0)))))))))))))))))))))) := by
  simp only [Numbers.list,List.sum_cons,List.sum_nil]

def numbers {p m F : ℕ} [Fact p.Prime] (maps : Fin F→Weight m p)
    (τ cap M b K H drift scale n U j : ℕ) : Numbers :=
  let J := LightTernaryDimensions.J M b n U
  let N := fixedLength m*j
  let W := sourceWidth maps cap
  let Z := wantedWidth maps τ
  let R := 4^fixedLength m
  let Q := R^j
  let P := p*(p+1)^j
  let A := (2^(fixedAlpha m 2))^j
  let G := F^j
  let weights := weight H (4^fixedLength m) U
  let hits := n*W^j
  let count := n*2^J*Z^j
  let sourceV := A*weights*(2*hits+1)
  let eulerV := 2*(N+1)*Q*sourceV
  let tensorV := Q^2*n^2*(W^j)^2*weights^2
  let Λ := J+2
  let width := TernaryPairedColumnEnumeration.width K
  let poly := (LightTernaryPairedPolynomial.polynomial K).coefficient.toNat*
    (tensorV+1)^(LightTernaryPairedPolynomial.polynomial K).degree
  { localSize := W+Z+106
    radixCells := (j+1)*(W^j+1)
    joinCells := 10+n+2*W^j+4*p^j+P+2*hits
    hits := hits
    sourceHistogram := G*Q+1
    sourceWord := p+p*p*(p+1)^j+p+1+
      R+R*R*(R+1)^j+R+1+F+F*F*(F+1)^j+F+1+
      4*P+12*p^j+32+3*Q+16+G*Q+1+A+A*hits*weights+(hits+1)*weights+
      (2*R)^j+(2*F)^j+
      3*LightTernaryAppendKeys.word (J+2) p p (p^j)+
      p^j+J+16+p+R+F+Z+(8*P+4*p+16)+(2*R)^j+(2*F)^j+n+j+
      2*(n*n+n+p^j*p+16)
    prefixCells := Q+2*N+9+100000000+2*N+j+m+F+(F+1)*(F+1)^j+4*Q+100
    bankCells := G*(N+1)*Q+4*Q+2*N+1
    nearMetadata := 2*N*Q+N
    nearDivision := eulerV+3
    frontendWord := 100*(N+Q+G+count+Q+(N+1)*Q+2*Q+4*Q+Q*sourceV+
      eulerV+(Q*sourceV)^2+Q*(Q*sourceV)^2+100)
    tensorCells := count*Λ^4+width+5
    tensorWord := (2*R+2)^2+Λ+count+Λ^4+4*(Λ^4+Λ^5+Λ+8)
    potentialWord := 10*(Λ^(width+1)+Λ^width+width+Λ+2)+
      2*(Λ^width+1)*(poly+1)+poly+count*Λ^width*poly
    spanCells := p^j*J
    originalMatrixCells := n*2^J*(J+2)
    menuCells := (8*p^(4*K+1)*(J+3))^2*(J+2)
    budgets := (p^(2*K))^j+(drift*scale)^j*
      LightTernaryInitialBudgets.word K b (p^(2*K)) drift scale n J (n*2^J)+9^j*n^2
    depth := n+5*N+j+J+100
    reporterWord := TernaryMomentDetectorResources.coefficient
        (TernaryArenaPairMass.envelope maps cap M n) H*
          (U+1)^TernaryMomentDetectorResources.degree H+
      (TernaryMomentChannelResources.need (TernaryArenaPairMass.envelope maps cap M n) U (2*H)).word+
      2*n+2^(2*N+1)+16+(n*n+n+p^j+16)+2*U+3
    reporterCells := (2*H+1)*(count+1)+3*count+4*n+2+(2*N+1)
    candidateScore := n^2+(2^(fixedPi m 2*K))^j*count*((n*W^j)^2)^K*
      Λ^(2*K)*(((2*K).factorial*(2*R+1)^(2*K))^2)
    prefixHeader := 106+100*(j+m+p+p^j+fixedAlpha m 2+TernaryArenaSourceSetup.alphaRank m+2*R+J+
      N+20384999*m*j+2*N+F^j+Q+p^j*p+fixedAlpha m 2*j+A+TernaryArenaSourceSetup.alphaRank m*j+
      (N+1)*Q+N*Q+2*(TernaryArenaSourceSetup.alphaRank m*j)+(R+1)^j+(p^(2*K))^j*p^(2*K)+
      9^j*n^2*9+
      LightTernaryInitialBudgets.word K b (p^(2*K)) drift scale n J (n*2^J)*
        (drift*scale)^j*drift*scale+
      LightTernaryInitialBudgets.word K b (p^(2*K)) drift scale n J (n*2^J)*
        (drift*scale)^j*drift+9) }

def total {p m F : ℕ} [Fact p.Prime] (maps : Fin F→Weight m p)
    (τ cap M b K H drift scale n U j : ℕ) : ℕ :=
  (numbers maps τ cap M b K H drift scale n U j).list.sum

attribute [irreducible] Uniform

open Lean Elab Tactic Meta
syntax "arena_poly" : tactic
elab_rules : tactic
| `(tactic| arena_poly) => do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    let args := target.getAppArgs
    unless args.size == 2 do throwError "expected Uniform, got {target}"
    let kind ← forallTelescopeReducing (← inferType args[1]!) fun xs _ => do
      let body := (mkAppN args[1]! xs).headBeta
      let varies (e : Expr) := xs.any fun x => e.containsFVar x.fvarId!
      if !varies body then return (0 : Nat)
      let head := body.getAppFn.constName?
      if head == some ``HAdd.hAdd || head == some ``Nat.add then return 1
      if head == some ``HMul.hMul || head == some ``Nat.mul then return 2
      if head == some ``HPow.hPow || head == some ``Nat.pow then
        if !varies body.getAppArgs.back! then return 3
      if head == some ``Nat.succ then return 5
      return 4
    match kind with
    | 0 => evalTactic (← `(tactic| exact Uniform.const _ _))
    | 1 => evalTactic (← `(tactic| apply Uniform.add <;> arena_poly))
    | 2 => evalTactic (← `(tactic| apply Uniform.mul <;> arena_poly))
    | 3 => evalTactic (← `(tactic| apply Uniform.pow <;> arena_poly))
    | 5 => evalTactic (← `(tactic| apply Uniform.succ <;> arena_poly))
    | _ => evalTactic (← `(tactic| assumption))

/-- The bound is uniform in the actual original magnitude and all prefixes;
all alphabets and circuit degrees are fixed by the compiled program. -/
theorem numbers_uniform {p m F M b : ℕ} [Fact p.Prime]
    (maps : Fin F→Weight m p) (τ cap K H drift scale : ℕ)
    (hM : 1<M) (hb : 1<b) :
    Uniform M (total maps τ cap M b K H drift scale) := by
  have hn := inputN M
  have hU := inputU M
  have hj := prefixCount hM
  have hJ := digits hM hb
  have hcarry := carries hM hb
  have hpow (A : ℕ) := alphabet hM A
  have hN : Uniform M (fun _ _ j=>fixedLength m*j) := (Uniform.const M _).mul hj
  have hW : Uniform M (fun _ _ j=>(sourceWidth maps cap)^j) := hpow _
  have hZ : Uniform M (fun _ _ j=>(wantedWidth maps τ)^j) := hpow _
  have hQ : Uniform M (fun _ _ j=>(4^fixedLength m)^j) := hpow _
  have hP : Uniform M (fun _ _ j=>(p+1)^j) := hpow _
  have hFp : Uniform M (fun _ _ j=>F^j) := hpow _
  have hF : Uniform M (fun _ _ j=>(F+1)^j) := hpow _
  have hR : Uniform M (fun _ _ j=>(4^fixedLength m+1)^j) := hpow _
  have hp : Uniform M (fun _ _ j=>p^j) := hpow _
  have hA : Uniform M (fun _ _ j=>(2^fixedAlpha m 2)^j) := hpow _
  have hB : Uniform M (fun _ _ j=>(p^(2*K))^j) := hpow _
  have hD : Uniform M (fun _ _ j=>(drift*scale)^j) := hpow _
  have h2R : Uniform M (fun _ _ j=>(2*(4^fixedLength m))^j) := hpow _
  have h2F : Uniform M (fun _ _ j=>(2*F)^j) := hpow _
  have hscale : Uniform M (fun _ _ j=>(2^(fixedPi m 2*K))^j) := hpow _
  have h9 : Uniform M (fun _ _ j=>9^j) := hpow _
  have field0 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).localSize) := by
    dsimp only [numbers,weight,TernaryMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    arena_poly
  have field1 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).radixCells) := by
    dsimp only [numbers,weight,TernaryMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    arena_poly
  have field2 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).joinCells) := by
    dsimp only [numbers,weight,TernaryMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    arena_poly
  have field3 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).hits) := by
    dsimp only [numbers,weight,TernaryMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    arena_poly
  have field4 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).sourceHistogram) := by
    dsimp only [numbers,weight,TernaryMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    arena_poly
  have field5 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).sourceWord) := by
    dsimp only [numbers,weight,TernaryMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    arena_poly
  have field6 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).prefixCells) := by
    dsimp only [numbers,weight,TernaryMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    arena_poly
  have field7 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).bankCells) := by
    dsimp only [numbers,weight,TernaryMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    arena_poly
  have field8 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).nearMetadata) := by
    dsimp only [numbers,weight,TernaryMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    arena_poly
  have field9 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).nearDivision) := by
    dsimp only [numbers,weight,TernaryMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    arena_poly
  have field10 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).frontendWord) := by
    dsimp only [numbers,weight,TernaryMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    arena_poly
  have field11 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).tensorCells) := by
    dsimp only [numbers,weight,TernaryMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    arena_poly
  have field12 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).tensorWord) := by
    dsimp only [numbers,weight,TernaryMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    arena_poly
  have field13 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).potentialWord) := by
    dsimp only [numbers,weight,TernaryMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    arena_poly
  have field14 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).spanCells) := by
    dsimp only [numbers,weight,TernaryMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    arena_poly
  have field15 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).originalMatrixCells) := by
    dsimp only [numbers,weight,TernaryMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    arena_poly
  have field16 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).menuCells) := by
    dsimp only [numbers,weight,TernaryMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    arena_poly
  have field17 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).budgets) := by
    dsimp only [numbers,weight,TernaryMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    arena_poly
  have field18 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).depth) := by
    dsimp only [numbers,weight,TernaryMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    arena_poly
  have field19 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).reporterWord) := by
    have h2N : Uniform M (fun _ _ j=>2^(2*(fixedLength m*j)+1)) := by
      have hh := (Uniform.const M 2).mul hQ
      convert hh using 1
      funext n U j
      rw [pow_succ,show 2*(fixedLength m*j)=(2*fixedLength m)*j by ring,pow_mul]
      norm_num [pow_mul]
      ring
    dsimp only [numbers,TernaryMomentDetectorResources.coefficient,TernaryMomentDetectorResources.degree,
      TernaryMomentChannelResources.need,TernaryArenaPairMass.envelope]
    arena_poly
  have field20 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).reporterCells) := by
    dsimp only [numbers]
    arena_poly
  have field21 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).candidateScore) := by
    dsimp only [numbers]
    arena_poly
  have field22 : Uniform M (fun n U j => (numbers maps τ cap M b K H drift scale n U j).prefixHeader) := by
    dsimp only [numbers,weight,TernaryMomentWeightBounds.leftBound,
      LightTernaryInitialBudgets.word,LightTernaryInitialBudgets.initial,
      LightTernaryAppendKeys.word,LightSignedRowHash.word]
    arena_poly
  have result := field0.add (field1.add (field2.add (field3.add (field4.add (field5.add (field6.add (field7.add (field8.add (field9.add (field10.add (field11.add (field12.add (field13.add (field14.add (field15.add (field16.add (field17.add (field18.add (field19.add (field20.add (field21.add (field22.add (Uniform.const M 0)))))))))))))))))))))))
  convert result using 1
  funext n U j
  exact Numbers.sum_list _

/-- The fourth power also pays the selector's score/denominator products
and all fixed-size control sums. -/
def envelope {p m F : ℕ} [Fact p.Prime] (maps : Fin F→Weight m p)
    (τ cap M b K H drift scale n U j : ℕ) : ℕ :=
  (total maps τ cap M b K H drift scale n U j+1)^4

/-- Fixed constants for the complete concrete prefix envelope. -/
theorem fixed_capacity_all {p m F M b : ℕ} [Fact p.Prime]
    (maps : Fin F→Weight m p) (τ cap K H drift scale : ℕ)
    (hM : 1<M) (hb : 1<b) :
    ∃ D E : ℕ, ∀ n U j, j≤Nat.clog M (n^2) →
      envelope maps τ cap M b K H drift scale n U j≤capacity D E (n+U) := by
  have hu := ((numbers_uniform maps τ cap K H drift scale hM hb).add (Uniform.const M 1)).pow 4
  unfold Uniform at hu
  obtain ⟨D,E,h⟩ := hu
  refine ⟨D,E,fun n U j hj=>?_⟩
  exact (h n U j hj).trans
    (Nat.mul_le_mul_right _ (by omega : D≤256*(D+1)))

/-- These are universal compile-time constants for every literal entry of
our actual prefix footprint list, rather than a resource-oracle premise. -/
theorem fixed_capacity {p m F M b : ℕ} [Fact p.Prime]
    (maps : Fin F→Weight m p) (τ cap K H drift scale : ℕ)
    (hM : 1<M) (hb : 1<b) :
    ∃ D E : ℕ, ∀ n U j, j≤Nat.clog M (n^2) →
      ∀ v∈(numbers maps τ cap M b K H drift scale n U j).list,
        v≤capacity D E (n+U) := by
  obtain ⟨D,E,h⟩ := fixed_capacity_all maps τ cap K H drift scale hM hb
  refine ⟨D,E,fun n U j hj v hv=>?_⟩
  have hvsum := List.le_sum_of_mem hv
  have hp : total maps τ cap M b K H drift scale n U j+1≤
      (total maps τ cap M b K H drift scale n U j+1)^4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right
      (by omega : 1≤total maps τ cap M b K H drift scale n U j+1) (by decide : 1≤4)
  exact hvsum.trans ((Nat.le_succ _).trans (hp.trans (h n U j hj)))


/-- The initializer exponent itself also fits the fixed capacity constant,
even when both runtime inputs are zero. -/
theorem fixed_capacity_constants {p m F M b : ℕ} [Fact p.Prime]
    (maps : Fin F→Weight m p) (τ cap K H drift scale : ℕ)
    (hM : 1<M) (hb : 1<b) :
    ∃ D E : ℕ, E≤D ∧ ∀ n U j, j≤Nat.clog M (n^2) →
      envelope maps τ cap M b K H drift scale n U j≤capacity D E (n+U) := by
  obtain ⟨D,E,h⟩ := fixed_capacity_all maps τ cap K H drift scale hM hb
  refine ⟨D+E,E,by omega,fun n U j hj => (h n U j hj).trans ?_⟩
  unfold capacity
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))

end ThreeSum.TernaryArenaPrefixFootprints
