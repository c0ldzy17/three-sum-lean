import Submission.ThreeSum.LightTernaryPrefixStep

noncomputable section
namespace ThreeSum.TernaryPrefixSeedHeader
open Light LightTernarySeedScoreFactory LightTernaryControllerFactory
open LightTernaryPrefixStep LightTernaryPrefixHeader LightTernaryPrefixFinish
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

def result (xs : List ℤ) (X : Inputs) : List ℤ :=
  ((((((((((xs.set 4 X.power).set 6 X.power).set 24 X.liveHeader).set 39 (X.j+1)).set 41 (X.xB*X.p)).set 42 (X.xC*X.p)).set 43 (X.xP*X.a)).set 44 (X.tB*9)).set 45 (X.tC*9)).set 46 (X.tP*X.b*X.scale))

@[simp] theorem result_length (xs : List ℤ) (X : Inputs) : (result xs X).length=xs.length :=by simp [result]

theorem result_seg {μ : ℕ→ℤ} {xs : List ℤ} (X : Inputs) (H : Seg μ X.seed xs) :
    Seg (LightTernaryBudgetStep.changed
      (LightTernaryPrefixPrepare.seedChanged μ X.seed X.power X.liveHeader (X.j+1))
      (X.seed+41) X.p X.a X.b X.scale X.xB X.xC X.xP X.tB X.tC X.tP)
      X.seed (result xs X) :=by
  have h:=store_seg (store_seg (store_seg (store_seg (store_seg (store_seg
    (store_seg (store_seg (store_seg (store_seg H 4 X.power) 6 X.power) 24 X.liveHeader)
      39 (X.j+1)) 41 (X.xB*X.p)) 42 (X.xC*X.p)) 43 (X.xP*X.a)) 44 (X.tB*9))
      45 (X.tC*9)) 46 (X.tP*X.b*X.scale)
  simpa only [LightTernaryBudgetStep.changed,LightTernaryPrefixPrepare.seedChanged,result,Nat.add_assoc,Nat.cast_add,Nat.cast_one,
    show (41+1:ℕ)=42 by decide,show (41+2:ℕ)=43 by decide,show (41+3:ℕ)=44 by decide,
    show (41+4:ℕ)=45 by decide,show (41+5:ℕ)=46 by decide] using h

/-- Actual entry184 preserves the old live seed header through enumeration
and host construction, then performs exactly the ten scalar writes. -/
theorem prepared_segment {X : Inputs} {μ ν : ℕ→ℤ} {xs : List ℤ}
    (H : Prepared X μ ν) (hs : Seg μ X.seed xs)
    (hbefore : X.seed+xs.length≤X.prefixFree) (hafter : X.liveHeader+106≤X.seed) :
    Seg ν X.seed (result xs X) :=by
  obtain ⟨μ₁,μ₂,_,_,_,hkeep,_,hsame,hν⟩:=H
  have hs₁:=hs.of_kept hkeep hbefore
  have hs₂:=hs₁.of_sameOutside hsame (Or.inr hafter)
  subst ν
  exact result_seg X hs₂

def nextConfig (C : Config) (X : Inputs) : Config :=
  {C with catalogRows:=X.power,power:=X.power,header:=X.liveHeader,prefixLength:=X.j+1}

instance (C : Config) [Fact C.p.Prime] (X : Inputs) : Fact (nextConfig C X).p.Prime :=
  inferInstanceAs (Fact C.p.Prime)

/-- The computed writes are exactly the next controller ABI. -/
theorem result_header (C : Config) (X : Inputs) (n dB dC dP tB tC tP newSpan : ℕ) :
    result (header C n dB dC dP tB tC tP newSpan) X=
      header (nextConfig C X) n (X.xB*X.p) (X.xC*X.p) (X.xP*X.a) (X.tB*9) (X.tC*9)
        (X.tP*X.b*X.scale) newSpan :=by
  simp [result,header,nextConfig,LightTernarySeedController.args,Config.argv,withSeed,LightTernarySeedScore.args]

/-- A genuine previous live header yields the exact next live header. No
48-word configuration advice is assumed after preparation. -/
theorem prepared_header {X : Inputs} {C : Config} {μ ν : ℕ→ℤ}
    {n dB dC dP tB tC tP newSpan : ℕ}
    (H : Prepared X μ ν) (hs : Seg μ X.seed (header C n dB dC dP tB tC tP newSpan))
    (hbefore : X.seed+48≤X.prefixFree) (hafter : X.liveHeader+106≤X.seed) :
    Seg ν X.seed (header (nextConfig C X) n (X.xB*X.p) (X.xC*X.p) (X.xP*X.a)
      (X.tB*9) (X.tC*9) (X.tP*X.b*X.scale) newSpan) :=by
  rw [←result_header C X n dB dC dP tB tC tP newSpan]
  exact prepared_segment H hs (by simpa using hbefore) hafter

/-- Every old key, retained catalog entry and original immutable input
survives the actual bank/header/budget preparation. -/
theorem prepared_kept_regions {X : Inputs} {μ ν : ℕ→ℤ}
    (H : Prepared X μ ν) (x : ℕ) (hp : x<X.prefixFree)
    (hhost : x<X.liveHeader ∨ X.liveHeader+106≤x)
    (hseed : x<X.seed ∨ X.seed+48≤x) : ν x=μ x :=by
  obtain ⟨μ₁,μ₂,_,_,_,hkeep,_,hsame,hν⟩:=H
  rw [hν,LightTernaryBudgetStep.changed_outside _ _ _ _ _ _ _ _ _ _ _ _ x (by omega)]
  simp only [LightTernaryPrefixPrepare.seedChanged]
  rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),
    Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
  exact (hsame x hhost).trans (hkeep x hp)

/-- Every physically emitted bank/header/power cell is retained by the
subsequent low-address scalar writes in entry184. -/
theorem prepared_outputs {X : Inputs} {μ ν : ℕ→ℤ}
    (H : Prepared X μ ν) (hhost : X.liveHeader+106≤X.seed)
    (hseed : X.seed+48≤X.prefixFree) :
    Seg ν (LightTernaryPrefixSetup.headerAt X.prefixFree X.m (X.j+1))
      (LightTernaryPrefixSetup.header X.m (X.j+1) X.F X.prefixFree
        (LightTernaryPrefixSetup.workAt X.prefixFree X.m (X.j+1))) ∧
    Seg ν X.prefixFree ((TernaryAddresses.codes (LightTernaryPrefixSetup.N X.m (X.j+1))
      (LightTernaryPrefixSetup.T X.m (X.j+1))).map (fun (c:ℕ)=>(c:ℤ))) ∧
    LightSubsetAddress.Powers ν (LightTernaryPrefixSetup.workAt X.prefixFree X.m (X.j+1))
      (2*LightTernaryPrefixSetup.N X.m (X.j+1)) :=by
  obtain ⟨μ₁,μ₂,hHeader,hCodes,hPowers,_,_,hsame,hν⟩:=H
  have keep (x : ℕ) (hx : X.prefixFree≤x) : ν x=μ₁ x:=by
    rw [hν,LightTernaryBudgetStep.changed_outside _ _ _ _ _ _ _ _ _ _ _ _ x (by omega)]
    simp only [LightTernaryPrefixPrepare.seedChanged]
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),
      Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact hsame x (Or.inr (by omega))
  refine ⟨hHeader.congr ?_,hCodes.congr ?_,?_⟩
  · intro i hi
    apply keep
    unfold LightTernaryPrefixSetup.headerAt LightTernaryPrefixSetup.workAt
    generalize 4^(LightTernaryPrefixSetup.N X.m (X.j+1))=mask
    omega
  · intro i hi;exact keep _ (by omega)
  · intro i hi
    rw [keep _ (by unfold LightTernaryPrefixSetup.workAt;generalize 4^(LightTernaryPrefixSetup.N X.m (X.j+1))=mask;omega)]
    exact hPowers i hi

/-- The six previous scalar budgets are actual cells of the live header. -/
theorem budget_segment {C : Config} {μ : ℕ→ℤ} {seed n dB dC dP tB tC tP newSpan : ℕ}
    (H : Seg μ seed (header C n dB dC dP tB tC tP newSpan)) :
    Seg μ (seed+41) (LightTernaryBudgetStep.oldValues dB dC dP tB tC tP) :=by
  intro i hi
  have hi6 : i<6:=by simpa [LightTernaryBudgetStep.oldValues] using hi
  have hread:=H.getD (i:=41+i) (by simp;omega) 0
  interval_cases i <;>
    simpa [header,LightTernarySeedController.args,Config.argv,withSeed,LightTernarySeedScore.args,
      LightTernaryBudgetStep.oldValues,Nat.add_assoc] using hread

end ThreeSum.TernaryPrefixSeedHeader
