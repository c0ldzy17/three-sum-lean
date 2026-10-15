import Submission.ThreeSum.LightTernaryPreparedPostSelection
import Submission.ThreeSum.TernaryArenaLayout

noncomputable section
namespace ThreeSum.TernaryArenaCleanupLayout
open Light TernaryArenaLayout LightOriginalSurvivors LightOriginalSurvivorPair
set_option maxHeartbeats 2000000

def layout (free C aBase nA bBase nB cBase nC q L : ℕ) : Layout where
  aBase:=aBase
  nA:=nA
  bBase:=bBase
  nB:=nB
  cBase:=cBase
  nC:=nC
  keyB:=addr free C 4
  keyC:=addr free C 5
  histB:=addr free C 7
  histC:=addr free C 8
  q:=q
  powers:=addr free C 6
  L:=L
  outB:=addr free C 9
  valueB:=addr free C 10
  packedB:=addr free C 16
  lengthB:=addr free C 16+nB
  outC:=addr free C 16+nB+1
  valueC:=addr free C 16+nB+1+2*nC
  packedC:=addr free C 17
  lengthC:=addr free C 17+nC

theorem unchanged_bank {free C aBase nA bBase nB cBase nC q L : ℕ}
    {keysB keysC : ℕ→ℕ} {μ ν : ℕ→ℤ}
    (hnB : nB≤C) (hnC : nC≤C)
    (h : (layout free C aBase nA bBase nB cBase nC q L).Unchanged keysB keysC μ ν)
    {x : ℕ} (hlo : addr free C 11≤x) (hhi : x<addr free C 16) : ν x=μ x := by
  have hBl := length_le keysB nB
  have hCl := length_le keysC nC
  apply h x
  · simp only [LightOriginalSurvivorStage.Unwritten,layout]
    unfold addr at *
    omega
  · simp only [LightOriginalSurvivorStage.Unwritten,layout]
    unfold addr at *
    omega

theorem unchanged_high {free C aBase nA bBase nB cBase nC q L : ℕ}
    {keysB keysC : ℕ→ℕ} {μ ν : ℕ→ℤ}
    (hcounts : nB+3*nC+1≤C) (hC : nC+1≤C)
    (h : (layout free C aBase nA bBase nB cBase nC q L).Unchanged keysB keysC μ ν)
    {x : ℕ} (hx : addr free C 18≤x) : ν x=μ x := by
  have hBl := length_le keysB nB
  have hCl := length_le keysC nC
  apply h x
  · simp only [LightOriginalSurvivorStage.Unwritten,layout]
    unfold addr at *
    omega
  · simp only [LightOriginalSurvivorStage.Unwritten,layout]
    unfold addr at *
    omega

theorem preparation_bank {free C q L : ℕ}
    {μ ν : ℕ→ℤ} (hL : L+1≤C) (hq : q≤C)
    (h : ∀ x,LightTernaryFinalPreparation.Unwritten (addr free C 6) L
      (addr free C 7) (addr free C 8) q x→ν x=μ x)
    {x : ℕ} (hx : addr free C 9≤x) : ν x=μ x := by
  apply h
  unfold LightTernaryFinalPreparation.Unwritten addr at *
  omega

theorem inputs {lim : Limits} {d U free C aBase nA bBase nB cBase nC q L : ℕ}
    (μ : ℕ→ℤ) (A B Cv : ℕ→ℤ) (keysB keysC : ℕ→ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hend : finish free C≤lim.space)
    (hA : aBase+nA≤addr free C 6) (hB : bBase+nB≤addr free C 6)
    (hC : cBase+nC≤addr free C 6)
    (hBcap : 2*nB≤C) (hCcap : nB+3*nC+1≤C) (hCc : nC+1≤C)
    (hq : q≤C) (hL : L+1≤C)
    (hword : ((nB+nC+2^(L+1)+16 : ℕ) : ℤ)≤lim.word)
    (hscoreB : ((nB*nB+nB+q+16 : ℕ) : ℤ)≤lim.word)
    (hscoreC : ((nC*nC+nC+q+16 : ℕ) : ℤ)≤lim.word)
    (hkeysB : ∀ i<nB,keysB i<q) (hkeysC : ∀ i<nC,keysC i<q)
    (hreadKB : ∀ i<nB,μ (addr free C 4+i)=(keysB i : ℤ))
    (hreadKC : ∀ i<nC,μ (addr free C 5+i)=(keysC i : ℤ))
    (hboundA : ∀ i<nA,|A i|≤(U : ℤ))
    (hboundB : ∀ i<nB,|B i|≤(U : ℤ)) (hboundC : ∀ i<nC,|Cv i|≤(U : ℤ))
    (hreadA : ∀ i<nA,μ (aBase+i)=A i)
    (hreadB : ∀ i<nB,μ (bBase+i)=B i) (hreadC : ∀ i<nC,μ (cBase+i)=Cv i)
    (hvalueWord : 2*(U : ℤ)+3≤lim.word)
    (hsortedB : ∀ i j,i<j→j<nB→B i<B j)
    (hsortedC : ∀ i j,i<j→j<nC→Cv i<Cv j)
    (hnB : nB<2^L) (hnC : nC<2^L) (hd : d+L+5≤lim.depth) :
    LightTernaryPreparedPostSelection.Inputs
      (layout free C aBase nA bBase nB cBase nC q L) lim d U L μ A B Cv keysB keysC := by
  have hnb : nB≤C := by omega
  have hnc : nC≤C := by omega
  have hfinish := hend
  unfold finish slots addr at hfinish
  refine {
    hw:=hw
    hA:=?_
    hB:=?_
    hC:=?_
    hkB:=?_
    hkC:=?_
    hhB:=?_
    hhC:=?_
    hp:=?_
    hB1:=?_
    hB2:=?_
    hB3:=by rfl
    hBC:=by rfl
    hC1:=by rfl
    hC2:=?_
    hC3:=by rfl
    hEnd:=?_
    hword:=hword
    hkeysB:=hkeysB
    hkeysC:=hkeysC
    hreadKB:=hreadKB
    hreadKC:=hreadKC
    hboundA:=hboundA
    hboundB:=hboundB
    hboundC:=hboundC
    hreadA:=hreadA
    hreadB:=hreadB
    hreadC:=hreadC
    hvalueWord:=hvalueWord
    hsortedB:=hsortedB
    hsortedC:=hsortedC
    hL:=le_rfl
    hnB:=hnB
    hnC:=hnC
    hd:=hd
    beforeA:=hA
    beforeB:=hB
    beforeC:=hC
    beforeKeyB:=?_
    beforeKeyC:=?_
    powerBeforeHist:=?_
    histBeforeHist:=?_
    scoreWordB:=hscoreB
    scoreWordC:=hscoreC }
  all_goals simp only [layout]
  all_goals unfold addr at *
  all_goals omega

end ThreeSum.TernaryArenaCleanupLayout
