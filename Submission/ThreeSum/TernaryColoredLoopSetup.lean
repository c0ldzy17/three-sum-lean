import Submission.ThreeSum.TernaryConcreteProfile
import Submission.ThreeSum.TernaryArenaLoopState
import Submission.ThreeSum.TernaryPreparedOriginals
import Submission.ThreeSum.TernaryArenaPrefixPrepareAllocation
import Submission.ThreeSum.TernaryArenaSelectorAllocation

noncomputable section
namespace ThreeSum.TernaryColoredLoopSetup
open Light TernaryArenaLayout TernaryArenaSourceSetup TernaryArenaSeedCandidate
open TernaryConcreteProfile TernaryLocalParameters
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
variable {κ : ℕ}

def J (P : Profile κ) (n : ℕ) :=LightTernaryDimensions.J P.M P.radix n (n^κ)
def rounds (P : Profile κ) (n : ℕ) :=LightTernaryDimensions.r P.M n
def dim (P : Profile κ) (n : ℕ) :=LightTernaryDimensions.dim P.M P.radix P.p P.K n (n^κ)
def q (P : Profile κ) (n : ℕ) :=P.p^(dim P n)
def cells (P : Profile κ) (n : ℕ) :=capacity P.allocation.D P.allocation.E (n+n^κ)
def weight (P : Profile κ) (n : ℕ) :=TernaryArenaPrefixFootprints.weight P.H (4^fixedLength P.m) (n^κ)

def baseInput (P : Profile κ) (n free : ℕ) (A B C : List ℤ) : Input :=
  TernaryPreparedOriginals.input free n (n^κ) (J P n) (cells P n) (weight P n) 0 A B C

/-- A finite proof-only time maximum. No list of queries or answers is
provided to the executable. -/
def queryTime (P : Profile κ) (n free : ℕ) (A B C : List ℤ) : ℕ :=
  (Finset.range (rounds P n+1)).sup fun j =>
    TernaryArenaCountReady.queryTime (m:=P.m) (r:=j) (baseInput P n free A B C)
      (valueCap (r:=j) P.maps P.cap (baseInput P n free A B C))

def input (P : Profile κ) (n free : ℕ) (A B C : List ℤ) : Input :=
  {baseInput P n free A B C with queryTime:=queryTime P n free A B C}

def arrays (P : Profile κ) (n free menu : ℕ) (A B C : List ℤ) : Inputs :=
  TernaryPreparedOriginals.inputs free n (J P n) menu A B C

def initialBudget (P : Profile κ) (n : ℕ) (A : List ℤ) :=
  LightTernaryInitialBudgets.initial P.K P.radix n (J P n) (A.length*2^(J P n))

abbrev Extension (P : Profile κ) (n c : ℕ) :=
  AdjoinRoot (TernaryComputedExtensionMenu.modulus P.p (dim P n) c)

theorem dim_pos (P : Profile κ) (n : ℕ) : 0<dim P n :=
  TernaryExtensionEncoding.menuDegree_pos (p:=P.p) (J P n+2) P.K

/-- Every field, dimension, endpoint and immutable row of the loop model is
fixed by actual preprocessing and the particular irreducible found at runtime. -/
def setup (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (μ : ℕ→ℤ)
    [Fact (Irreducible (TernaryComputedExtensionMenu.modulus P.p (dim P n) c))] :
    TernaryArenaLoop.Setup P.p P.m P.F P.K (q P n*q P n) (Extension P n c) where
  maps:=P.maps
  threshold:=P.threshold
  cap:=P.cap
  Q:=P.output
  M:=P.M
  radix:=P.radix
  H:=P.H
  drift:=P.drift
  scale:=P.scale
  allocation:=P.allocation
  input:=input P n free A B C
  arrays:=arrays P n free menu A B C
  n:=n
  U:=n^κ
  rounds:=rounds P n
  U0:=initialBudget P n A
  featureBound:=P.radix
  tagBound:=P.radix
  positionCap:=n
  valueTag:=n^κ
  V:=0
  scoreBound:=0
  enumeration:=TernaryComputedExtensionMenu.seeds
  ell:=TernaryComputedExtensionMenu.functional (dim_pos P n)
  L:=TernaryArenaSelectedSigned.left (n^κ) P.radix (J P n) (fun i=>B.getD i 0)
  R:=TernaryArenaSelectedSigned.right (n^κ) P.radix (J P n) (fun i=>C.getD i 0)
  O:=TernaryArenaSelectedSigned.requester (n^κ) P.radix (J P n) (fun i=>A.getD i 0)
  catalogs:=fun _ _ _=>0
  initial:=μ

theorem query_time (P : Profile κ) (n free : ℕ) (A B C : List ℤ) (j : ℕ) (hj : j≤rounds P n) :
    TernaryArenaCountReady.queryTime (m:=P.m) (r:=j) (input P n free A B C)
      (valueCap (r:=j) P.maps P.cap (input P n free A B C))≤
      (input P n free A B C).queryTime := by
  change TernaryArenaCountReady.queryTime (m:=P.m) (r:=j) (baseInput P n free A B C)
      (valueCap (r:=j) P.maps P.cap (baseInput P n free A B C))≤queryTime P n free A B C
  exact Finset.le_sup (f:=fun j => TernaryArenaCountReady.queryTime (m:=P.m) (r:=j)
    (baseInput P n free A B C) (valueCap (r:=j) P.maps P.cap (baseInput P n free A B C)))
    (Finset.mem_range.mpr (by omega))

theorem originals_query_time {p : ℕ} [Fact p.Prime] {E : Type*} [Field E] [Fintype E]
    [DecidableEq E] [Algebra (ZMod p) E] {I : Input} {A : Inputs}
    {seedCount featureBound tagBound positionCap : ℕ} {ell : E→ₗ[ZMod p] ZMod p}
    {seeds : ℕ→E×E} {L R O : ℕ→ℕ→ℤ} {μ : ℕ→ℤ}
    (H : TernaryArenaPrefixInputs.Originals I A seedCount featureBound tagBound positionCap ell seeds L R O μ)
    (t : ℕ) :
    TernaryArenaPrefixInputs.Originals {I with queryTime:=t} A seedCount featureBound tagBound positionCap ell seeds L R O μ := by
  exact ⟨H.BEnd,H.CEnd,H.OEnd,H.menuEnd,H.positionEnd,H.leftEnd,H.rightEnd,H.feature,
    H.BBound,H.CBound,H.OBound,H.leftBound,H.rightBound,H.BRead,H.CRead,H.ORead,
    H.menuRead,H.positionRead,H.positionBound,H.leftRead,H.rightRead⟩

section Facts
variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (μ : ℕ→ℤ)
variable [Fact (Irreducible (TernaryComputedExtensionMenu.modulus P.p (dim P n) c))]

 theorem field_sizes :
    8*(J P n+2)*P.p^2≤Fintype.card (Extension P n c) ∧
    8*(J P n+2)*P.p^(2*(P.K+P.K))≤Fintype.card (Extension P n c) := by
  apply TernaryArenaPhaseBudget.field_sizes (J P n) P.K P.K_pos
  exact TernaryComputedExtensionMenu.field_card

 theorem left_injective (hmeta : TernaryPreparedOriginals.Metadata n (n^κ) A B C)
    (hinputs : TernaryArenaFixedParameters.InputGuards P.K P.m P.radix κ n) :
    Function.Injective (fun i : Fin B.length=>fun t : Fin (J P n+2)=>
      (TernaryArenaSelectedSigned.left (n^κ) P.radix (J P n) (fun j=>B.getD j 0) i.val t.val:ZMod P.p)) := by
  apply TernarySignedFeatureHash.left_injective (fun i : Fin B.length=>B.getD i.val 0)
    P.radix_gt_one P.basePrime hinputs.2.2.1
    (fun i=>hmeta.boundB i.val i.isLt) hmeta.injectiveB

 theorem right_injective (hmeta : TernaryPreparedOriginals.Metadata n (n^κ) A B C)
    (hinputs : TernaryArenaFixedParameters.InputGuards P.K P.m P.radix κ n) :
    Function.Injective (fun i : Fin C.length=>fun t : Fin (J P n+2)=>
      (TernaryArenaSelectedSigned.right (n^κ) P.radix (J P n) (fun j=>C.getD j 0) i.val t.val:ZMod P.p)) := by
  apply TernarySignedFeatureHash.right_injective (fun i : Fin C.length=>C.getD i.val 0)
    P.radix_gt_one P.basePrime hinputs.2.2.1
    (fun i=>hmeta.boundC i.val i.isLt) hmeta.injectiveC

 theorem budgets (hmeta : TernaryPreparedOriginals.Metadata n (n^κ) A B C)
    (hinputs : TernaryArenaFixedParameters.InputGuards P.K P.m P.radix κ n) :
    let S:=setup P n free menu c A B C μ
    ∀j≤S.rounds,TernaryArenaSelectedBudgets.Budget S.maps S.threshold S.cap S.Q S.input S.arrays
      P.K S.n S.U0 S.L S.R S.O j (S.state j) := by
  have hp9 : 9<P.p := P.primeLarge
  have hp : 3≤P.p := by omega
  have hs:=field_sizes P n c
  have hm : (P.K+P.K).factorial*P.radix^(P.K+P.K)<P.p := by
    simpa only [←two_mul,Profile.radix,Profile.p] using P.minor
  have hh:=TernaryArenaSignedSelection.budget P.maps P.threshold P.cap (n^κ) 0 0 P.output
    (input P n free A B C) (arrays P n free menu A B C) P.K n P.radix A.length
    (TernaryComputedExtensionMenu.seeds (p:=P.p) (d:=dim P n) (c:=c))
    (TernaryComputedExtensionMenu.functional (dim_pos P n))
    (fun i=>A.getD i 0) (fun i=>B.getD i 0) (fun i=>C.getD i 0) (fun _ _ _=>0)
    (rounds P n) hinputs.2.1.le (TernaryComputedExtensionMenu.functional_ne_zero (dim_pos P n))
    hp P.radix_gt_one P.basePrime hinputs.2.2.1 hmeta.injectiveB hmeta.injectiveC
    hmeta.boundB hmeta.boundC hm hs.1 hs.2 hmeta.lengthB hmeta.lengthC
  exact hh

end Facts

end ThreeSum.TernaryColoredLoopSetup
