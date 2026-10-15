import Submission.ThreeSum.TernaryArenaHeaderAgreement
import Submission.ThreeSum.LightTernaryPrefixPrepare

noncomputable section
namespace ThreeSum.TernaryPrefixPreparedHeader
open Light TernaryArenaLayout TernaryArenaSourceSetup TernaryArenaHeaderAgreement
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]

theorem prefixN_eq (m r : ℕ) : LightTernaryPrefixSetup.N m r=N m r :=by
  simp only [LightTernaryPrefixSetup.N,N,TernaryLocalParameters.fixedLength]
  ring

theorem receipt_segment {μ ν : ℕ→ℤ} (I : Input) (j J : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m)
    (hTemplate : Seg μ (addr I.free I.capacity 0) (templateValues I p m F))
    (H : LightTernaryPrefixPrepare.HeaderReceipt μ ν m F p
      (addr I.free I.capacity 0) (addr I.free I.capacity 1) I.prefixFree
      (TernaryLocalParameters.fixedAlpha m 2) (alphaRank m)
      (TernaryCodeSemantics.address Q.val) (4^(TernaryLocalParameters.fixedLength m)) J j
      (p^j) (addr I.free I.capacity 50) (addr I.free I.capacity 51)) :
    ∃ret, Seg ν (addr I.free I.capacity 1) (emittedHeader I p m F j Q ret) :=by
  obtain ⟨μcopy,ret,hCopied,hKept,hν⟩:=H
  refine ⟨ret,?_⟩
  have hs:=LightTernaryPrefixHeader.result_segment (templateValues_length I) hTemplate hCopied hν
  simpa [LightTernaryPrefixPrepare.headerLoc,emittedHeader,
    LightTernaryPrefixHeader.resultHeader,LightTernaryPrefixHeader.patchList,
    LightTernaryPrefixHeader.args,LightTernaryPrefixHeader.locals,LightTernaryPrefixLoop.headerWrites,
    LightTernaryPrefixSetup.nb,LightTernaryPrefixSetup.workAt,prefixN_eq,
    nb,bankCodes,cut] using hs

theorem budget_preserves_header {μ ν : ℕ→ℤ} {xs : List ℤ}
    {header seed power liveHeader s p a b scale xB xC xP tB tC tP : ℕ}
    (hs : Seg μ header xs) (hsep : header+xs.length≤seed)
    (hν : ν=LightTernaryBudgetStep.changed
      (LightTernaryPrefixPrepare.seedChanged μ seed power liveHeader s)
      (seed+41) p a b scale xB xC xP tB tC tP) : Seg ν header xs :=by
  subst ν
  intro i hi
  have hk:=LightTernaryBudgetStep.changed_outside
    (LightTernaryPrefixPrepare.seedChanged μ seed power liveHeader s)
    (seed+41) p a b scale xB xC xP tB tC tP
  rw [hk (header+i) (Or.inl (by omega))]
  simp only [LightTernaryPrefixPrepare.seedChanged]
  rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),
    Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
  exact hs i hi

/-- The actual count write performed by SeedScore yields the exact host ABI;
no configuration header is supplied as advice to the machine. -/
theorem count_header {ν : ℕ→ℤ} (I : Input) (j : ℕ)
    (maps : Fin F→TernaryCoverGoodMaps.Weight m p) (τ cap : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (ret : ℤ)
    (hs : Seg ν (addr I.free I.capacity 1) (emittedHeader I p m F j Q ret)) :
    Seg (Function.update ν (addr I.free I.capacity 1+104)
      ((entries (r:=j+1) maps τ I).length:ℤ)) (addr I.free I.capacity 1)
      (setup (r:=j+1) maps τ cap Q I).argv :=by
  rw [← argv_agreement maps τ cap j Q I ret]
  exact LightTernaryPrefixHeader.store_seg hs 104 _

end ThreeSum.TernaryPrefixPreparedHeader
