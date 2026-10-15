import Submission.ThreeSum.LightTernarySeedScoreFactory

noncomputable section
namespace ThreeSum.LightTernarySeedScoreFull
open Light LightTernarySeedScoreFactory

structure Outputs (C : Config) (D : Data C) (R S : ℕ)
    (raws : List ℤ) (words maps : List ℕ) (ν : ℕ→ℤ) : Prop where
  B : Reads ν C.Bnew C.nB D.newB
  Cvalues : Reads ν C.Cnew C.nC D.newC
  O : Reads ν C.Onew C.nO D.newO
  wanted : Seg ν C.wanted (D.wantedRows R S raws words maps)
  count : ν (C.header+104)=(D.H R S raws words maps : ℤ)

end ThreeSum.LightTernarySeedScoreFull

namespace ThreeSum.LightTernarySeedScoreFactory
open Light
open scoped BigOperators
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
variable {lim : Limits}

theorem Ready.run_full {C : Config} [Fact C.p.Prime] {D : Data C}
    {depth R mapRadix cap V K N U a b : ℕ} {host : TernarySourceCountExecutionFactory.Setup N}
    {L Rvalues : ℕ → ℕ → ℤ} {scoreBound : ℤ} {raws : List ℤ} {words maps : List ℕ} {μ : ℕ → ℤ}
    (G : Ready C D lim depth R mapRadix cap V K N U host L Rvalues scoreBound raws words maps μ)
    (hretain : C.wanted+(D.wantedRows R mapRadix raws words maps).length≤C.tensor)
    (hleft : ∀pair∈host.left.records, TernaryBank.rank (host.front.E.word (host.left.key pair.2))=a)
    (hright : ∀pair∈host.right.records, TernaryBank.rank (host.front.E.word (host.right.key pair.2))=b)
    (hQ : ∀j<host.front.count, TernaryBank.rank (host.front.Q j)=a+b)
    (P : Fin host.front.count → Type*) [∀i, Fintype (P i)]
    (A B : ∀i, P i → Fin (C.J+2) → ℤ) (s : ℤ)
    (hModel : ∀(i : Fin host.front.count) (a b c e : Fin (C.J+2)),
      LightTernaryTensorFactory.score host C.J L Rvalues i.val
        (LightTernaryPairedPolynomial.tensorIndex (C.J+2) a.val b.val c.val e.val)=
        s*TernaryPairedTensor.tensor (A i) (B i) a b c e)
    (hPairedWord : |s^K*((∑i : Fin host.front.count, ∑e : Fin K→P i,
      TernaryPairedPotential.rowWeight (Sum.elim (fun j => A i (e j)) (fun j => B i (e j)))) : ℤ)|≤lim.word) :
    Meets lim (LightTernarySeedScore.program C.p R mapRadix K raws words maps
      host.left.xs host.left.ys host.left.zs host.right.xs host.right.ys host.right.zs)
      164 depth C.argv μ (runtime D host K R mapRadix cap V raws words maps)
      (fun r ν => r=D.flag ∧ ∃ξ, (KeptInput C μ ξ ∧ LightTernarySeedScoreFull.Outputs C D R mapRadix raws words maps ξ) ∧ ν=
        Function.update (Function.update (Function.update (Function.update ξ
          (C.flags+C.seed) D.flag) (C.scoreB+C.seed) D.collisionB) (C.scoreC+C.seed) D.collisionC)
          (C.scorePaired+C.seed) (s^K*((∑i : Fin host.front.count, ∑e : Fin K→P i,
            TernaryPairedPotential.rowWeight (Sum.elim (fun j => A i (e j)) (fun j => B i (e j)))) : ℤ))) := by
  let paired : ℤ := s^K*((∑i : Fin host.front.count, ∑e : Fin K→P i,
    TernaryPairedPotential.rowWeight (Sum.elim (fun j => A i (e j)) (fun j => B i (e j)))) : ℤ)
  have hSpace := G.append.scratchSpace
  have hBScratch := G.append.outScratch
  have hBC := G.append.BC
  have hCO := G.append.CO
  have hWanted := G.wanted.targetEnd
  have hHist := G.collision.histogramAfter
  have hHistSpace := G.collision.histogramSpace
  have hLen : C.J+2≤lim.space := by have := G.append.rowBefore; omega
  have hRow : C.row≤lim.space := by have := G.append.rowBefore; omega
  have hFlagWord : |D.flag|≤lim.word := by
    have hp := G.span.pword
    have hprime := (Fact.out : C.p.Prime).one_lt
    unfold Data.flag LightStoredSpan.admissibleFlag
    split_ifs <;> norm_num <;> omega
  have hHrows := TernaryWantedBatchCount.rows_length C.p R mapRadix C.prefixLength raws words maps
    D.targets D.position C.nO
  have hCursor : C.wanted+3*D.H R mapRadix raws words maps≤lim.space := by
    have hBound := LightTernaryWantedBatch.rows_length_le C.p R mapRadix C.prefixLength cap raws words maps
      D.targets D.position G.wanted.capBound C.nO
    change (D.wantedRows R mapRadix raws words maps).length=3*D.H R mapRadix raws words maps at hHrows
    rw [hHrows] at hHist
    omega
  have hTensor : ∀ν, Built C D R mapRadix raws words maps μ ν →
      Meets lim (LightTernaryTensorFactory.program host K) 138 (depth+1)
        [C.header,C.leftTagged,C.nB,C.rightTagged,C.nC,C.J,C.leftWeights,C.rightWeights,C.tensor,
          D.H R mapRadix raws words maps,C.countOutput,C.quadScratch,C.quadPowers,C.potentialColumns,C.potentialPowers]
        (Function.update ν (C.header+104) (D.H R mapRadix raws words maps : ℤ))
        (LightTernaryTensorDriver.time K C.J C.nB C.nC (D.H R mapRadix raws words maps) host.runtime)
        (fun r ξ => r=paired ∧ (KeptInput C μ ξ ∧ LightTernarySeedScoreFull.Outputs C D R mapRadix raws words maps ξ)) := by
    intro ν H
    have HT := G.tensor ν H
    have hh := HT.run_scaled hleft hright hQ P A B s hModel
    have hh' := hh.mono le_rfl (fun r ξ h => show r=paired ∧
        (KeptInput C μ ξ ∧ LightTernarySeedScoreFull.Outputs C D R mapRadix raws words maps ξ) from by
      have htensor : C.tensor≤C.quadScratch := by have := HT.tensorEnd; omega
      have preserve (x : ℕ) (hx : x<C.tensor) :
          ξ x=(Function.update ν (C.header+104) (D.H R mapRadix raws words maps : ℤ)) x :=
        h.2 x ⟨by omega,Or.inl hx⟩
      have hhead : C.header+104<C.Bnew := by have := G.headerBefore; omega
      have keys (base n : ℕ) (f : ℕ→ℕ) (hl : C.Bnew≤base)
          (hu : base+n≤C.tensor) (hf : Reads ν base n f) : Reads ξ base n f := by
        intro i hi
        rw [preserve _ (by omega),Function.update_of_ne (by omega)]
        exact hf i hi
      refine ⟨h.1,?_,?_⟩
      · intro x hx hne
        rw [preserve x (by have := G.tensorAfter; omega),Function.update_of_ne hne]
        exact H.1.1.1.1 x hx
      · refine ⟨?_,?_,?_,?_,?_⟩
        · exact keys C.Bnew C.nB D.newB le_rfl (by have := G.append.BC; have := G.append.CO; have := G.wanted.targetEnd; omega) H.1.1.1.2
        · exact keys C.Cnew C.nC D.newC (by have := G.append.BC; omega)
            (by have := G.append.CO; have := G.wanted.targetEnd; omega) H.1.1.2
        · exact keys C.Onew C.nO D.newO (by have := G.append.BC; have := G.append.CO; omega)
            (by have := G.wanted.targetEnd; omega) H.1.2
        · intro i hi
          rw [preserve _ (by omega),Function.update_of_ne (by
            have := G.append.BC; have := G.append.CO; have := G.wanted.targetEnd; omega)]
          exact H.2 i hi
        · rw [preserve _ (by have := G.tensorAfter; omega)]
          exact Function.update_self _ _ _)
    simpa only [G.leftN,G.rightN,G.leftWeights,G.rightWeights,G.count,G.countOutput] using hh'
  have hh := LightTernarySeedScore.program_meets (menu := C.menu) (seed := C.seed) (J := C.J)
    (catalog := C.catalog) (catalogRows := C.catalogRows) (p := C.p) (power := C.power)
    (Bmatrix := C.Bmatrix) (Bold := C.Bold) (Bnew := C.Bnew) (nB := C.nB)
    (Cmatrix := C.Cmatrix) (Cold := C.Cold) (Cnew := C.Cnew) (nC := C.nC)
    (Omatrix := C.Omatrix) (Oold := C.Oold) (Onew := C.Onew) (nO := C.nO)
    (positions := C.positions) (wanted := C.wanted) (work := C.work) (hashWork := C.hashWork)
    (hist := C.hist) (header := C.header) (leftTagged := C.leftTagged) (rightTagged := C.rightTagged)
    (leftWeights := C.leftWeights) (rightWeights := C.rightWeights) (tensor := C.tensor)
    (countOutput := C.countOutput) (quadScratch := C.quadScratch) (quadPowers := C.quadPowers)
    (potentialColumns := C.potentialColumns) (potentialPowers := C.potentialPowers)
    (flags := C.flags) (scoreB := C.scoreB) (scoreC := C.scoreC) (scorePaired := C.scorePaired)
    (prefixLength := C.prefixLength) (d := depth) (H := D.H R mapRadix raws words maps)
    raws words maps host.left.xs host.left.ys host.left.zs host.right.xs host.right.ys host.right.zs
    μ D.flag D.collisionB D.collisionC paired
    (BuiltB C D μ) (BuiltC C D μ) (BuiltO C D μ)
    (Built C D R mapRadix raws words maps μ) (Built C D R mapRadix raws words maps μ)
    (Built C D R mapRadix raws words maps μ)
    (fun ξ => KeptInput C μ ξ ∧ LightTernarySeedScoreFull.Outputs C D R mapRadix raws words maps ξ)
    G.append.spaceWord hLen hRow (by omega) (by have := G.headerBefore; omega) hCursor G.divideWord
    G.flagAddr G.BAddr G.CAddr G.PAddr hFlagWord G.BWord G.CWord hPairedWord
    (by have := G.append.depth; omega) le_rfl (runSpan G.append G.span) G.append.runB
    (fun ν H => G.append.runC H) (fun ν H => G.append.runO H)
    (fun ν H => runWanted G.append G.wanted H)
    (fun ν H => runCollisionB G.append G.wanted G.collision H)
    (fun ν H => runCollisionC G.append G.wanted G.collision H) hTensor
  exact hh


end ThreeSum.LightTernarySeedScoreFactory
