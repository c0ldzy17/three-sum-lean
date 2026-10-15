import Submission.ThreeSum.TernaryArenaPrefixCommit
import Submission.ThreeSum.LightTernaryInitialBudgets
import Submission.ThreeSum.LightTernaryArenaTemplate
import Submission.ThreeSum.TernaryPrefixSeedHeader

noncomputable section
namespace ThreeSum.TernaryArenaInitialSeedHeader
open Light TernaryArenaLayout TernaryArenaSourceSetup TernaryArenaSeedCandidate
open LightTernarySeedScoreFactory LightTernaryControllerFactory LightTernaryPrefixHeader LightTernaryPrefixFinish
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

def replace (xs : List ℤ) (dB dC dP tB tC tP : ℕ) : List ℤ :=
  (((((xs.set 41 dB).set 42 dC).set 43 dP).set 44 tB).set 45 tC).set 46 tP

def patch (μ : ℕ→ℤ) (seed dB dC dP tB tC tP : ℕ) : ℕ→ℤ :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update μ (seed+41) dB) (seed+42) dC) (seed+43) dP) (seed+44) tB) (seed+45) tC) (seed+46) tP

theorem replacement {μ ν : ℕ→ℤ} {seed : ℕ} {xs : List ℤ} {dB dC dP tB tC tP : ℕ}
    (hs : Seg μ seed xs) (hlen : xs.length=48)
    (hb : Seg ν (seed+41) (LightTernaryBudgetStep.oldValues dB dC dP tB tC tP))
    (hk : ∀x,x<seed+48→(x<seed+41 ∨ seed+47≤x)→ν x=μ x) :
    Seg ν seed (replace xs dB dC dP tB tC tP) :=by
  let patched:=patch μ seed dB dC dP tB tC tP
  have hp : Seg patched seed (replace xs dB dC dP tB tC tP):=by
    have hh:=store_seg (store_seg (store_seg (store_seg (store_seg (store_seg hs 41 dB) 42 dC) 43 dP) 44 tB) 45 tC) 46 tP
    simpa [patched,replace,patch,Nat.add_assoc] using hh
  have hpbudget : Seg patched (seed+41) (LightTernaryBudgetStep.oldValues dB dC dP tB tC tP):=by
    intro i hi
    have hi6 : i<6:=by simpa [LightTernaryBudgetStep.oldValues] using hi
    interval_cases i <;> simp [patched,patch,LightTernaryBudgetStep.oldValues,Nat.add_assoc]
  apply hp.congr
  intro i hi
  by_cases hin : (41 ≤ i ∧ i < 47)
  · have hindex : i-41<6:=by omega
    have hb':=hb (i-41) (by simpa [LightTernaryBudgetStep.oldValues] using hindex)
    have hp':=hpbudget (i-41) (by simpa [LightTernaryBudgetStep.oldValues] using hindex)
    have ha : seed+41+(i-41)=seed+i:=by omega
    rw [ha] at hb' hp'
    exact hb'.trans hp'.symm
  · have hi48 : i<48:=by simpa only [replace,List.length_set,hlen] using hi
    rw [hk _ (by omega) (by omega)]
    dsimp only [patched,patch]
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),Function.update_of_ne (by omega),
      Function.update_of_ne (by omega),Function.update_of_ne (by omega),Function.update_of_ne (by omega)]

theorem replace_header (C : Config) (n dB dC dP tB tC tP dB' dC' dP' tB' tC' tP' newSpan : ℕ) :
    replace (header C n dB dC dP tB tC tP newSpan) dB' dC' dP' tB' tC' tP'=
      header C n dB' dC' dP' tB' tC' tP' newSpan :=by
  simp [replace,header,LightTernarySeedController.args,Config.argv,withSeed,LightTernarySeedScore.args]

/-- Exact equality of the actual arena constructor's 48 seed fields. -/
theorem template_values (I : Input) (A : Inputs) (p U wordRadix F q : ℕ) :
    LightTernaryArenaTemplate.seedValues
      (frame (LightTernaryArenaTemplate.args U I.free A.Bmatrix I.nB A.Cmatrix I.nC A.Omatrix I.requesterCount
        A.positions A.leftTagged A.rightTagged A.menu A.J p wordRadix F q 0 0 0 0 0 0)) I.free I.capacity=
      header (config p 0 I A 0) (q*q) 1 1 1 0 0 0 (addr I.free I.capacity 8) :=by
  simp [LightTernaryArenaTemplate.seedValues,LightTernaryArenaTemplate.seedFields,LightTernaryArenaTemplate.value,
    LightTernaryArenaTemplate.args,frame,header,LightTernarySeedController.args,Config.argv,withSeed,
    LightTernarySeedScore.args,config]

/-- The real budget initialization's six writes give the entire exact seed
header consumed by actual Init182. -/
theorem initialized {I : Input} {A : Inputs} {p q seed constants K bDigit n : ℕ}
    {μ ν : ℕ→ℤ}
    (hseed : seed=addr I.free I.capacity 2)
    (hconstants : seed+48≤constants)
    (hs : Seg μ seed (header (config p 0 I A 0) (q*q) 1 1 1 0 0 0 (addr I.free I.capacity 8)))
    (hb : Seg ν (seed+41) [1,1,1,((n*n:ℕ):ℤ),((n*n:ℕ):ℤ),
      (LightTernaryInitialBudgets.initial K bDigit n A.J I.requesterCount:ℤ)])
    (hk : ∀x,(x<seed+41 ∨ seed+47≤x)→(x<constants ∨ constants+3≤x)→ν x=μ x) :
    Seg ν seed (header (config p 0 I A 0) (q*q) 1 1 1 (n^2) (n^2)
      (LightTernaryInitialBudgets.initial K bDigit n A.J I.requesterCount) (addr I.free I.capacity 8)) :=by
  rw [←replace_header (config p 0 I A 0) (q*q) 1 1 1 0 0 0 1 1 1 (n^2) (n^2)
    (LightTernaryInitialBudgets.initial K bDigit n A.J I.requesterCount) (addr I.free I.capacity 8)]
  apply replacement hs (by simp) (by simpa only [LightTernaryBudgetStep.oldValues,Nat.pow_two,Nat.cast_one] using hb)
  intro x hlt hx
  exact hk x hx (Or.inl (by omega))

end ThreeSum.TernaryArenaInitialSeedHeader
