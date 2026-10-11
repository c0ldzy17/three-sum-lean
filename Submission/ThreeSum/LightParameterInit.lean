import Submission.ThreeSum.LightScales
import Submission.ThreeSum.LightLocalParameters
import Submission.ThreeSum.LightGlobalSizes

/-!
# One fixed integer-parameter initializer from the input length

The program starts with only `n`, an output pointer, and a scratch pointer.
It constructs the exact block schedule, local graph counts, selected local
prime, cap, typed global output count, radix, rounded band size, and prime
window. Every helper in the fixed program has an operational contract.
-/

namespace ThreeSum.LightParameterInit

open Light LocalCoverBounds Scales

set_option maxHeartbeats 1500000
set_option maxRecDepth 5000

def half (n : ℕ) : ℕ := microHalf (inputBits n)

def values (n : ℕ) : List ℤ :=
  ((LightScales.values n ++ LightLocalParameters.values (half n)) ++
    LightGlobalSizes.values (LightGlobalSizes.localCount n) (localRadix n)
      (blockCount (inputBits n)) (mu n)) ++ [(primeWindow n : ℤ)]

def body (pCore pLocal pGlobal pSqrt pPower : ℕ) : Stmt :=
  .call pCore [v 0,v 1] 3 ;;
  .set 4 (M (v 1 +' k 1)) ;;
  .call pLocal [v 4,v 1 +' k 5,v 2] 5 ;;
  .set 6 (M (v 1 +' k 3)) ;;
  .set 7 (M (v 1 +' k 5)) ;;
  .call pGlobal [v 7,v 5,v 6,v 3,v 1 +' k 13] 8 ;;
  .set 9 (M (v 1)) ;;
  .call pSqrt [v 9] 10 ;;
  .set 11 (v 10 +' k 1) ;;
  .call pPower [k 2,v 11] 12 ;;
  .store (v 1 +' k 18) (v 12) ;;
  .set 0 (v 8)

def time (n : ℕ) : ℕ := LightScales.time n+LightLocalParameters.time (half n)+
  LightGlobalSizes.time (LightGlobalSizes.localCount n) (blockCount (inputBits n)) (mu n)+
  sqrtTime (inputBits n)+LightNatPower.time (windowExponent (inputBits n))+400

def space (work n : ℕ) : ℕ := LightLocalParameters.space work (half n)

def word (n : ℕ) : ℕ := 1000*(n+1)+LightLocalParameters.word (half n)+
  LightGlobalSizes.word (LightGlobalSizes.localCount n) (localRadix n)
    (blockCount (inputBits n)) (mu n)+100*(primeWindow n+inputBits n+1)

structure Procs (P : Program) (pMain : ℕ) where
  pCore : ℕ
  pLocal : ℕ
  pGlobal : ℕ
  pSqrt : ℕ
  pPower : ℕ
  core : LightScales.Procs P pCore
  localParams : LightLocalParameters.Procs P pLocal
  globalSizes : LightGlobalSizes.Procs P pGlobal
  sqrt : P[pSqrt]? = some sqrtBody
  power : P[pPower]? = some LightNatPower.body
  main : P[pMain]? = some (body pCore pLocal pGlobal pSqrt pPower)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {n dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*half n+6 ≤ lim.depth)
    (hout : dst+19 ≤ work) (hspace : space work n ≤ lim.space)
    (hword : (word n : ℤ) ≤ lim.word) :
    Meets lim P pMain d [n,dst,work] μ (time n)
      (fun r μ' => r = (radix n : ℤ) ∧ Seg μ' dst (values n) ∧
        KeptBut μ μ' work dst 19) := by
  have hCoreWord : ((1000*(n+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : 1000*(n+1) ≤ word n := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hLocalWord : (LightLocalParameters.word (half n) : ℤ) ≤ lim.word := by
    have hh : LightLocalParameters.word (half n) ≤ word n := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hGlobalWord : (LightGlobalSizes.word (LightGlobalSizes.localCount n) (localRadix n)
      (blockCount (inputBits n)) (mu n) : ℤ) ≤ lim.word := by
    have hh : LightGlobalSizes.word (LightGlobalSizes.localCount n) (localRadix n)
      (blockCount (inputBits n)) (mu n) ≤ word n := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hAuxWord : ((100*(primeWindow n+inputBits n+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : 100*(primeWindow n+inputBits n+1) ≤ word n := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwork : work ≤ lim.space := by
    have hh : LightLocalCounts.space work (half n) ≤ lim.space :=
      (le_max_left _ _).trans hspace
    unfold LightLocalCounts.space at hh
    omega
  have hbits := LightScales.inputBits_le_self n
  have hhalf : half n ≤ n := (LightScales.microHalf_le_self (inputBits n)).trans hbits
  have hmu : mu n ≤ n := (LightScales.totalSize_le_self (inputBits n)).trans hbits
  have hJ : blockCount (inputBits n) ≤ 20*n :=
    (LightScales.blockCount_le _).trans (Nat.mul_le_mul_left _ hbits)
  have hglobalBound (x : ℕ) (hx : x ≤ LightGlobalSizes.word (LightGlobalSizes.localCount n)
      (localRadix n) (blockCount (inputBits n)) (mu n)) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hGlobalWord
  have hCWord := hglobalBound (LightGlobalSizes.localCount n) (by unfold LightGlobalSizes.word; omega)
  have hpWord := hglobalBound (localRadix n) (by unfold LightGlobalSizes.word; omega)
  have hRWord : (radix n : ℤ) ≤ lim.word :=
    hglobalBound (radix n) (by unfold LightGlobalSizes.word radix; omega)
  have hWindowWord : (primeWindow n : ℤ) ≤ lim.word := by omega
  have hsqrt := Nat.sqrt_le_self (inputBits n)
  have he : windowExponent (inputBits n) ≤ inputBits n+1 := by unfold windowExponent; omega
  have heWord : (windowExponent (inputBits n) : ℤ) ≤ lim.word := by omega
  have hWindowPowers (i : ℕ) (hi : i ≤ windowExponent (inputBits n)) :
      ((2^i : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) hi)).trans hWindowWord
  apply Meets.of_body S.main
  unfold body time
  light_call (S.core.meets (d := d+1) (μ := μ) (n := n) (dst := dst)
    hw (by omega) hCoreWord (by omega))
    using LightNatPower.time with total μ₁ ⟨htotal,hcore,hkept₁⟩
  have hhalfRead : μ₁ (dst+1) = (half n : ℤ) := by
    simpa [LightScales.values,half] using hcore 1 (by simp [LightScales.values])
  light_set (half n : ℕ) using hhalfRead,LightNatPower.time
  light_call (S.localParams.meets (d := d+1) (μ := μ₁) (h := half n) (dst := dst+5) (work := work)
    hw (by omega) (by omega) hspace hLocalWord)
    using LightNatPower.time with pval μ₂ ⟨hpval,hlocal,hkept₂⟩
  have hpval' : pval = (localRadix n : ℤ) := hpval
  have hcore₂ : Seg μ₂ dst (LightScales.values n) := by
    apply hcore.congr
    intro i hi
    have hi' : i < 5 := by simpa [LightScales.values] using hi
    exact hkept₂ _ ⟨by omega,Or.inl (by omega)⟩
  have hprefix₂ : Seg μ₂ dst (LightScales.values n ++ LightLocalParameters.values (half n)) := by
    apply seg_append.mpr
    exact ⟨hcore₂,by simpa [LightScales.values] using hlocal⟩
  have hJread : μ₂ (dst+3) = (blockCount (inputBits n) : ℤ) := by
    simpa [LightScales.values] using hcore₂ 3 (by simp [LightScales.values])
  have hCread : μ₂ (dst+5) = (LightGlobalSizes.localCount n : ℤ) := by
    simpa [LightLocalParameters.values,LightLocalCounts.values,half,LightGlobalSizes.localCount]
      using hlocal 0 (by simp [LightLocalParameters.values,LightLocalCounts.values])
  have hJnat : ((dst : ℤ)+3).toNat = dst+3 := by
    rw [show (dst : ℤ)+3 = ((dst+3 : ℕ) : ℤ) by omega,Int.toNat_natCast]
  have hCnat : ((dst : ℤ)+5).toNat = dst+5 := by
    rw [show (dst : ℤ)+5 = ((dst+5 : ℕ) : ℤ) by omega,Int.toNat_natCast]
  light_set (blockCount (inputBits n) : ℕ) using hJnat,hJread,LightNatPower.time
  light_set (LightGlobalSizes.localCount n : ℕ) using hCnat,hCread,LightNatPower.time
  light_call (S.globalSizes.meets (d := d+1) (μ := μ₂) (C := LightGlobalSizes.localCount n)
    (p := localRadix n) (J := blockCount (inputBits n)) (mu := mu n) (dst := dst+13)
    hw (by omega) (LightGlobalSizes.localCount_pos n) (localPrime_pos (half n))
    (by omega) hGlobalWord)
    using hpval',htotal,LightNatPower.time with rglobal μ₃ ⟨hglobalResult,hglobal,hkept₃⟩
  have hglobalResult' : rglobal = (radix n : ℤ) := hglobalResult
  have hprefix₃ : Seg μ₃ dst
      (LightScales.values n ++ LightLocalParameters.values (half n)) := by
    apply hprefix₂.congr
    intro i hi
    have hi' : i < 13 := by
      simpa [LightScales.values,LightLocalParameters.values,LightLocalCounts.values] using hi
    exact hkept₃ _ (Or.inl (by omega))
  have hfull : Seg μ₃ dst
      ((LightScales.values n ++ LightLocalParameters.values (half n)) ++
        LightGlobalSizes.values (LightGlobalSizes.localCount n) (localRadix n)
          (blockCount (inputBits n)) (mu n)) := by
    apply seg_append.mpr
    exact ⟨hprefix₃,by simpa [LightScales.values,LightLocalParameters.values,LightLocalCounts.values] using hglobal⟩
  have hbitsRead : μ₃ dst = (inputBits n : ℤ) := by
    simpa [LightScales.values] using hprefix₃ 0 (by simp [LightScales.values])
  light_set (inputBits n : ℕ) using hbitsRead,LightNatPower.time
  light_call (sqrt_meets (d := d+1) (K := inputBits n) S.sqrt μ₃ (by omega))
    using LightNatPower.time with rt μ₄ ⟨hrt,hmem₄⟩
  subst μ₄
  have hrt' : rt+1 = (windowExponent (inputBits n) : ℤ) := by
    simpa [windowExponent] using congrArg (fun z : ℤ => z+1) hrt
  light_set (windowExponent (inputBits n) : ℕ) using hrt',LightNatPower.time
  light_call (LightNatPower.meets (d := d+1) (b := 2) (e := windowExponent (inputBits n))
    S.power μ₃ heWord hWindowPowers) using LightNatPower.time
    with window μ₅ ⟨hwindow,hmem₅⟩
  subst μ₅
  have hwindow' : window = (primeWindow n : ℤ) := hwindow
  light_store (dst+18) (primeWindow n : ℕ) using hwindow',LightNatPower.time
  light_set (radix n : ℕ) using hglobalResult',LightNatPower.time
  refine ⟨rfl,?_,?_⟩
  · simpa [values,LightScales.values,LightLocalParameters.values,LightLocalCounts.values,
      LightGlobalSizes.values] using hfull.snoc (primeWindow n : ℤ)
  · intro a ha
    change Function.update μ₃ (dst+18) _ a = μ a
    rw [Function.update_of_ne (by omega)]
    exact (hkept₃ a (by omega)).trans
      ((hkept₂ a ⟨ha.1,by omega⟩).trans (hkept₁ a (by omega)))

def program : Program :=
  [body 1 6 20 16 21,
    LightScales.body 2 3 4 5,log2Body,cbrtCeilBody,halfBody,LightSmallDivide.body,
    LightLocalParameters.body 7 15 5,LightLocalCounts.body 8,LightSubsetSetup.body 9 13 14,
    LightPascal.buildBody 10 11,fillBody,LightPascal.rowBody 12,LightArray.linearBody,
    powTableBody,LightSubsetAddress.rankBody 14,
    LightSelectedPrime.body 16 17,sqrtBody,LightPrimePool.body 18,LightPrimality.body 19,emodBody,
    LightGlobalSizes.body 21 5 16,LightNatPower.body]

def procs : Procs program 0 :=
  ⟨1,6,20,16,21,
    ⟨2,3,4,5,rfl,rfl,rfl,rfl,rfl⟩,
    ⟨7,15,5,⟨8,9,10,11,12,13,14,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,
      ⟨16,17,rfl,⟨18,⟨19,rfl,rfl⟩,rfl⟩,rfl⟩,rfl,rfl⟩,
    ⟨21,5,16,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl⟩

theorem program_meets {μ : ℕ → ℤ} {n dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*half n+6 ≤ lim.depth)
    (hout : dst+19 ≤ work) (hspace : space work n ≤ lim.space)
    (hword : (word n : ℤ) ≤ lim.word) :
    Meets lim program 0 d [n,dst,work] μ (time n)
      (fun r μ' => r = (radix n : ℤ) ∧ Seg μ' dst (values n) ∧
        KeptBut μ μ' work dst 19) := procs.meets hw hd hout hspace hword

end ThreeSum.LightParameterInit
