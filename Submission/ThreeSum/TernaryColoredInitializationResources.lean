import Submission.ThreeSum.TernaryColoredLoopSetup

noncomputable section
namespace ThreeSum.TernaryColoredInitializationResources
open Light TernaryConcreteProfile TernaryColoredLoopSetup TernaryArenaLayout TernaryLocalParameters
set_option maxHeartbeats 2000000
set_option maxRecDepth 24000
variable {κ : ℕ}

structure Bounds (P : Profile κ) (n free : ℕ) (A B C : List ℤ) (lim : Limits) (depth : ℕ) : Prop where
  hardware : (TernaryArenaAllocationResources.need P.allocation n (n^κ)).Ok lim
    (input P n free A B C).free (depth+4)
  finish : TernaryArenaLayout.finish (input P n free A B C).free (cells P n)≤lim.space
  inputWord : ((n+n^κ:ℕ):ℤ)+1≤lim.word
  exponentWord : (P.allocation.E:ℤ)≤lim.word
  menu : q P n*q P n≤cells P n
  constants : P.p+4^fixedLength P.m+P.F≤cells P n
  budgetWord : (LightTernaryInitialBudgets.word P.K P.radix (P.p^(2*P.K)) P.drift P.scale
    n (J P n) (A.length*2^(J P n)):ℤ)≤lim.word
  depthBound : depth+1<lim.depth

/-- The literal per-color resource need supplies every scalar and pointer
condition for the two actual initialization calls and subsequent prefix call. -/
theorem bounds {lim : Limits} {depth : ℕ} (P : Profile κ) (n free : ℕ) (A B C : List ℤ)
    (hneed : (P.colorNeed n (n^κ)).Ok lim free depth)
    (hmeta : TernaryPreparedOriginals.Metadata n (n^κ) A B C) :
    Bounds P n free A B C lim depth := by
  have hs : (TernaryArenaAllocationResources.need P.allocation n (n^κ)).Ok lim
      (input P n free A B C).free (depth+100) :=
    TernaryColoredSolverNeed.arena_ok P.allocation hneed hmeta.lengthA hmeta.lengthB hmeta.lengthC
  have ho := TernaryArenaAllocationResources.ok P.allocation hs
  have hc := P.allocation.constants n (n^κ)
  have hwC : (cells P n:ℤ)≤lim.word := ho.2.1
  have hi : n+n^κ+1≤cells P n := hc.2.2
  have hinit := TernaryColoredSolverNeed.initial_word P.allocation n (n^κ)
    (A.length*2^(J P n)) (Nat.mul_le_mul_right _ hmeta.lengthA)
  have hq := TernaryArenaAllocationResources.menu_square P.allocation n (n^κ) 0 (Nat.zero_le _)
  refine {
    hardware:=hs.mono le_rfl le_rfl (by omega)
    finish:=ho.1
    inputWord:=?_
    exponentWord:=(Int.ofNat_le.mpr hc.2.1).trans hwC
    menu:=by simpa only [q,dim,pow_two,cells] using hq
    constants:=TernaryColoredSolverNeed.initialization_constants P.allocation n (n^κ)
    budgetWord:=(Int.ofNat_le.mpr hinit).trans hwC
    depthBound:=by have hh:=ho.2.2.1;omega }
  have hh := (Int.ofNat_le.mpr hi).trans hwC
  push_cast at hh
  exact hh

end ThreeSum.TernaryColoredInitializationResources
