import Submission.ThreeSum.LightTernaryPrefixPhases

noncomputable section
namespace ThreeSum.LightTernaryPrefixInit
open Light LightTernarySeedScoreFactory LightTernaryControllerFactory LightTernaryPrefixLoop
open LightTernaryPrefixPhases
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

private theorem initial_keys {lim : Limits} {P : Program} {d : ℕ}
    (hfill : P[173]?=some fillBody)
    (hmain : P[174]?=some (ReportingHostRelocation.relocate 173 LightTernaryInitialKeys.body))
    (C : Config) (μ : ℕ→ℤ) (hw : (lim.space:ℤ)≤lim.word)
    (hBC : C.Bold+C.nB≤C.Cold) (hCO : C.Cold+C.nC≤C.Oold)
    (hO : C.Oold+C.nO≤lim.space) (hd : d<lim.depth) :
    Meets lim P 174 d [C.Bold,C.nB,C.Cold,C.nC,C.Oold,C.nO] μ
      (LightTernaryInitialKeys.time C.nB C.nC C.nO)
      (fun r ν=>r=0 ∧ (∀i<C.nB,ν (C.Bold+i)=0) ∧ (∀i<C.nC,ν (C.Cold+i)=0) ∧
        (∀i<C.nO,ν (C.Oold+i)=0) ∧ (∀x,x<C.Bold ∨ C.Oold+C.nO≤x→ν x=μ x)) :=by
  have hBspace : C.Bold+C.nB≤lim.space:=by omega
  have hCspace : C.Cold+C.nC≤lim.space:=by omega
  apply Meets.of_body hmain
  simp only [LightTernaryInitialKeys.body,ReportingHostRelocation.relocate]
  unfold LightTernaryInitialKeys.time
  light_call (fill_meets (μ:=μ) (d:=d+1) (x:=(0:ℤ)) hfill hw hBspace) with rb μb ⟨hb,kb⟩
  light_call (fill_meets (μ:=μb) (d:=d+1) (x:=(0:ℤ)) hfill hw hCspace) with rc μc ⟨hc,kc⟩
  light_call (fill_meets (μ:=μc) (d:=d+1) (x:=(0:ℤ)) hfill hw hO) with ro ν ⟨ho,ko⟩
  light_set (0:ℕ)
  dsimp only
  refine ⟨by simp,?_,?_,?_,?_⟩
  · intro i hi
    rw [ko _ (by omega),kc _ (by omega)]
    exact (hb i (by simpa using hi)).trans (List.getElem_replicate _)
  · intro i hi
    rw [ko _ (by omega)]
    exact (hc i (by simpa using hi)).trans (List.getElem_replicate _)
  · intro i hi
    exact (ho i (by simpa using hi)).trans (List.getElem_replicate _)
  · intro x hx
    rw [ko x (by omega),kc x (by omega),kb x (by omega)]

def Initialized (C : Config) (seed : ℕ) (values : List ℤ) (μ ν : ℕ→ℤ) : Prop :=
  Seg ν seed values ∧ (∀i<C.nB,ν (C.Bold+i)=0) ∧ (∀i<C.nC,ν (C.Cold+i)=0) ∧
    (∀i<C.nO,ν (C.Oold+i)=0) ∧ (∀i<C.J,ν (C.catalog+i)=0) ∧
    (∀x,(x<seed ∨ seed+48≤x)→(x<C.Bold ∨ C.Oold+C.nO≤x)→
      (x<C.catalog ∨ C.catalog+C.J≤x)→ν x=μ x)

def time (C : Config) (rounds T : ℕ) : ℕ :=
  copyTime 48+LightTernaryInitialKeys.time C.nB C.nC C.nO+fillTime C.J+LightTernaryPrefixLoop.time rounds T+1000

/-- Entry182 constructs the live header, zero old keys and the actual empty
catalog, then executes the actual loop supplied by its pure phase plan. -/
theorem meets {lim : Limits} {C : Config}
    {rounds m F p seed template host prefixFree alpha2 alphaRank localQ radix J a b scale seedTemplate
      depth K R S T n dB dC dP tB tC tP newSpan : ℕ}
    {raws : List ℤ} {words maps : List ℕ} {xl yl zl xr yr zr : List ℤ}
    (μ : ℕ→ℤ) (hw : (lim.space:ℤ)≤lim.word)
    (htemplate : seedTemplate+48≤seed) (hseed : seed+48≤C.Bold)
    (hBC : C.Bold+C.nB≤C.Cold) (hCO : C.Cold+C.nC≤C.Oold)
    (hCatalog : C.Oold+C.nO≤C.catalog) (hSpace : C.catalog+C.J≤lim.space)
    (hJ : J=C.J) (hd : depth+1<lim.depth)
    (hvalues : Seg μ seedTemplate (LightTernaryPrefixFinish.header C n dB dC dP tB tC tP newSpan))
    (loops : ∀ν, Initialized C seed (LightTernaryPrefixFinish.header C n dB dC dP tB tC tP newSpan) μ ν→
      LoopPlan lim rounds m F p seed template host prefixFree alpha2 alphaRank localQ radix J a b scale
        (depth+1) K R S T raws words maps xl yl zl xr yr zr ν) :
    Meets lim (program p R S K raws words maps xl yl zl xr yr zr) 182 depth
      (args rounds m F p seed template host prefixFree alpha2 alphaRank localQ radix J a b scale++[(seedTemplate:ℤ)])
      μ (time C rounds T)
      (fun z ω=>z=((p^rounds:ℕ):ℤ) ∧ ∃ν,∃h:Initialized C seed
        (LightTernaryPrefixFinish.header C n dB dC dP tB tC tP newSpan) μ ν,(loops ν h).invariant rounds ω) :=by
  let values:=LightTernaryPrefixFinish.header C n dB dC dP tB tC tP newSpan
  have hlen : values.length=48:=LightTernaryPrefixFinish.header_length _ _ _ _ _ _ _ _ _
  let P:=program p R S K raws words maps xl yl zl xr yr zr
  have L:=program_library p R S K raws words maps xl yl zl xr yr zr
  have hfill : P[0]?=some fillBody:=by rfl
  have hseedSpace : seed+48≤lim.space:=by omega
  have hc:=copy_meets (P:=P) (d:=depth+1) (μ:=μ) L.spanCopy hw
    (show seedTemplate+48≤lim.space by omega) hseedSpace (Or.inl htemplate)
  apply Meets.of_body L.initial
  unfold initBody time
  light_call hc using args with copied ξ ⟨hcopied,hcopy⟩
  have hξseg : Seg ξ seed values:=by
    intro i hi
    exact (hcopied i (by omega)).trans (hvalues i hi)
  have hξread (i : ℕ) (hi : i<48) :=hξseg.getD (by simpa only [hlen] using hi) 0
  have hξ3 : ξ ((seed:ℤ)+3).toNat=(C.catalog:ℤ) :=by
    rw [show ((seed:ℤ)+3).toNat=seed+3 by omega]
    simpa [values,LightTernaryPrefixFinish.header,LightTernarySeedController.args,Config.argv,withSeed,LightTernarySeedScore.args] using hξseg.getD (i:=3) (by simp [values]) 0
  have hξ8 : ξ ((seed:ℤ)+8).toNat=(C.Bold:ℤ) :=by
    rw [show ((seed:ℤ)+8).toNat=seed+8 by omega]
    simpa [values,LightTernaryPrefixFinish.header,LightTernarySeedController.args,Config.argv,withSeed,LightTernarySeedScore.args] using hξseg.getD (i:=8) (by simp [values]) 0
  have hξ10 : ξ ((seed:ℤ)+10).toNat=(C.nB:ℤ) :=by
    rw [show ((seed:ℤ)+10).toNat=seed+10 by omega]
    simpa [values,LightTernaryPrefixFinish.header,LightTernarySeedController.args,Config.argv,withSeed,LightTernarySeedScore.args] using hξseg.getD (i:=10) (by simp [values]) 0
  have hξ12 : ξ ((seed:ℤ)+12).toNat=(C.Cold:ℤ) :=by
    rw [show ((seed:ℤ)+12).toNat=seed+12 by omega]
    simpa [values,LightTernaryPrefixFinish.header,LightTernarySeedController.args,Config.argv,withSeed,LightTernarySeedScore.args] using hξseg.getD (i:=12) (by simp [values]) 0
  have hξ14 : ξ ((seed:ℤ)+14).toNat=(C.nC:ℤ) :=by
    rw [show ((seed:ℤ)+14).toNat=seed+14 by omega]
    simpa [values,LightTernaryPrefixFinish.header,LightTernarySeedController.args,Config.argv,withSeed,LightTernarySeedScore.args] using hξseg.getD (i:=14) (by simp [values]) 0
  have hξ16 : ξ ((seed:ℤ)+16).toNat=(C.Oold:ℤ) :=by
    rw [show ((seed:ℤ)+16).toNat=seed+16 by omega]
    simpa [values,LightTernaryPrefixFinish.header,LightTernarySeedController.args,Config.argv,withSeed,LightTernarySeedScore.args] using hξseg.getD (i:=16) (by simp [values]) 0
  have hξ18 : ξ ((seed:ℤ)+18).toNat=(C.nO:ℤ) :=by
    rw [show ((seed:ℤ)+18).toNat=seed+18 by omega]
    simpa [values,LightTernaryPrefixFinish.header,LightTernarySeedController.args,Config.argv,withSeed,LightTernarySeedScore.args] using hξseg.getD (i:=18) (by simp [values]) 0
  have hk:=initial_keys L.initialFill L.initialMain C ξ hw hBC hCO (by omega) hd
  light_call hk using args,hξ8,hξ10,hξ12,hξ14,hξ16,hξ18,LightTernaryInitialKeys.time,copyTime with keyRet η ⟨hkeyRet,hB,hC,hO,hkeyKeep⟩
  have hηseg : Seg η seed values:=by
    intro i hi
    rw [hkeyKeep _ (Or.inl (by omega))]
    exact hξseg i hi
  have hη3 : η ((seed:ℤ)+3).toNat=(C.catalog:ℤ) :=by
    rw [hkeyKeep _ (Or.inl (by omega))]
    exact hξ3
  have hzero:=fill_meets (P:=P) (d:=depth+1) (μ:=η) (dst:=C.catalog) (n:=C.J) (x:=(0:ℤ)) hfill hw hSpace
  light_call hzero using args,hη3,hJ,LightTernaryInitialKeys.time,copyTime with spanRet ν ⟨hspan,hspanKeep⟩
  have hinitial : Initialized C seed values μ ν:=by
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · exact hηseg.of_sameOutside hspanKeep (Or.inl (by omega))
    · intro i hi
      rw [hspanKeep _ (Or.inl (by omega))]
      exact hB i hi
    · intro i hi
      rw [hspanKeep _ (Or.inl (by omega))]
      exact hC i hi
    · intro i hi
      rw [hspanKeep _ (Or.inl (by omega))]
      exact hO i hi
    · intro i hi
      exact (hspan i (by simpa using hi)).trans (List.getElem_replicate _)
    · intro x hc hk hs
      rw [hspanKeep x hs,hkeyKeep x hk,hcopy x hc]
  have hloop:=(loops ν hinitial).run
  light_call hloop using args,LightTernaryInitialKeys.time,copyTime with z ω ⟨hz,hω⟩
  exact ⟨hz,ν,hinitial,hω⟩

end ThreeSum.LightTernaryPrefixInit
