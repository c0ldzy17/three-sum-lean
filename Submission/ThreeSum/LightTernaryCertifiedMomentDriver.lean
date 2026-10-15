import Submission.ThreeSum.LightTernaryMomentDriver
import Submission.ThreeSum.LightTernaryMomentChannelFactory

/-! The full original-source moment driver instantiated from pure source,
query, memory, and arithmetic certificates, with no execution callbacks. -/
noncomputable section
namespace ThreeSum.LightTernaryCertifiedMomentDriver
open Light TernaryMomentSchedule LightTernaryMomentChannelFactory
set_option maxHeartbeats 3000000

def cost {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (c : ℕ×ℕ) : ℕ :=
  LightTernaryMomentChannelStep.time c.1 c.2 S.left.NL S.right.NL S.front.count S.runtime 106

def program {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (terms : ℕ) : Program :=
  LightTernaryMomentDriver.program S.left.xs S.left.ys S.left.zs S.right.xs S.right.ys S.right.zs
    (channels terms) terms (9+S.argv.length)

def time {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (terms : ℕ) : ℕ :=
  LightTernaryMomentDriver.time (channels terms) (cost S) terms S.front.count (9+S.argv.length)

@[simp] theorem program_length {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (terms : ℕ) :
    (program S terms).length=127*(channels terms).length+2 := by
  simp [program,LightTernaryMomentDriver.program]

theorem meets {lim : Limits} {N a b d originalB originalC matrix terms U W : ℕ}
    (S : TernarySourceCountExecutionFactory.Setup N) (μ : ℕ→ℤ) (B C : ℕ→ℤ)
    (hseed : ∀ k<terms, ∀ j≤k,
      TernarySourceCountExecutionFactory.Seed S lim (d+2) S.left.weightBase μ
        (leftWeights k j B) (rightWeights k j C))
    (himmutable : TernarySourceCountExecutionFactory.Immutable S matrix)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+2<lim.depth)
    (hBspace : originalB+S.left.NL≤matrix) (hCspace : originalC+S.right.NL≤matrix)
    (hwindow : matrix+terms*S.front.count≤S.left.weightBase)
    (hleft : S.left.weightBase+S.left.NL≤S.right.weightBase)
    (hright : S.right.weightBase+S.right.NL≤lim.space)
    (houtBefore : S.left.weightBase≤S.front.dst) (hout : S.front.dst+S.front.count≤lim.space)
    (hleftSpace : S.left.weightBase≤lim.space)
    (hB : ∀ i<S.left.NL, μ (originalB+i)=B i)
    (hC : ∀ i<S.right.NL, μ (originalC+i)=C i)
    (hBabs : ∀ i<S.left.NL, |B i|≤(U : ℤ)) (hCabs : ∀ i<S.right.NL, |C i|≤(U : ℤ))
    (hscore : ∀ k<terms, ∀ j≤k, ∀ i<S.front.count, |score S B C k j i|≤(W : ℤ))
    (hleftWord : ∀ k<terms, ∀ j≤k,
      max (U : ℤ) (2*((k.choose j : ℤ)+1)*((U : ℤ)+2)^j)≤lim.word)
    (hrightWord : ∀ k<terms, ∀ j≤k, max (U : ℤ) (2*((U : ℤ)+1)^(k-j))≤lim.word)
    (haddWord : 2*(((channels terms).length*W : ℕ) : ℤ)≤lim.word)
    (htermsWord : (terms : ℤ)≤lim.word)
    (hargsWord : ∀ z∈LightTernaryMomentChannelFactory.args S originalB originalC matrix, |z|≤lim.word)
    (hleftHom : ∀ pair∈S.left.records, TernaryBank.rank (S.front.E.word (S.left.key pair.2))=a)
    (hrightHom : ∀ pair∈S.right.records, TernaryBank.rank (S.front.E.word (S.right.key pair.2))=b)
    (hQ : ∀ i<S.front.count, TernaryBank.rank (S.front.Q i)=a+b) :
    Meets lim (program S terms) (127*(channels terms).length+1) d
      (LightTernaryMomentChannelFactory.args S originalB originalC matrix) μ (time S terms)
      (fun _ ν =>
        (∀ k<terms, ∀ i<S.front.count,
          ν (matrix+k*S.front.count+i)=∑ j∈Finset.range (k+1), score S B C k j i) ∧
        Kept μ ν matrix) := by
  let steps := channels terms
  let value := score S B C
  have hmBefore : matrix≤S.left.weightBase := by omega
  have hstep : ∀ idx<steps.length, ∀ ν,
      TernaryMomentMatrixInvariant.Holds μ matrix S.front.count terms S.left.weightBase
        (steps.take idx) value ν →
      Meets lim (LightTernaryMomentSourceProgram.program S.left.xs S.left.ys S.left.zs
        S.right.xs S.right.ys S.right.zs (steps.getD idx (0,0)).1 (steps.getD idx (0,0)).2)
        126 (d+1) (LightTernaryMomentChannelFactory.args S originalB originalC matrix) ν
        (cost S (steps.getD idx (0,0)))
        (fun _ ξ => TernaryMomentMatrixInvariant.Holds μ matrix S.front.count terms S.left.weightBase
          (steps.take (idx+1)) value ξ) := by
    intro idx hidx ν hI
    let c := steps.getD idx (0,0)
    have hcget : c=steps[idx] := List.getD_eq_getElem _ _ hidx
    have hcmem : c∈channels terms := by rw [hcget]; exact List.getElem_mem hidx
    have hc : c.1<terms ∧ c.2≤c.1 := by
      exact mem_channels.mp (by simpa only [Prod.mk.eta] using hcmem)
    have hkeep : Kept μ ν matrix := by
      intro x hx
      exact hI.2 x (by omega) (Or.inl hx)
    have H := (hseed c.1 hc.1 c.2 hc.2).transport hkeep himmutable
    have hBν : ∀ i<S.left.NL, ν (originalB+i)=B i := by
      intro i hi
      exact (hkeep _ (by omega)).trans (hB i hi)
    have hCν : ∀ i<S.right.NL, ν (originalC+i)=C i := by
      intro i hi
      exact (hkeep _ (by omega)).trans (hC i hi)
    have hrowEnd : matrix+c.1*S.front.count+S.front.count≤S.left.weightBase := by
      have hh := Nat.mul_le_mul_right S.front.count (show c.1+1≤terms by omega)
      simp only [Nat.add_mul,one_mul] at hh
      omega
    have hbounded : ∀ i<S.front.count,
        |aggregate (steps.take idx) value c.1 i|≤((steps.length*W : ℕ) : ℤ) ∧
        |value c.1 c.2 i|≤((steps.length*W : ℕ) : ℤ) := by
      intro i hi
      have hpart := TernaryMomentMatrixInvariant.aggregate_abs_le (steps.take idx) value c.1 i W
        (by
          intro e he
          have hemem : e∈channels terms := List.mem_of_mem_take he
          have hec : e.1<terms ∧ e.2≤e.1 :=
            mem_channels.mp (by simpa only [Prod.mk.eta] using hemem)
          exact hscore e.1 hec.1 e.2 hec.2 i hi)
      have hlen : (steps.take idx).length≤steps.length := by simp only [List.length_take]; exact Nat.min_le_right _ _
      have hm := Nat.mul_le_mul_right W hlen
      have hmZ : ((steps.take idx).length : ℤ)*W≤((steps.length*W : ℕ) : ℤ) := by exact_mod_cast hm
      have hW : W≤steps.length*W := by
        have hn : 1≤steps.length := by omega
        nlinarith
      exact ⟨hpart.trans hmZ,(hscore c.1 hc.1 c.2 hc.2 i hi).trans (by exact_mod_cast hW)⟩
    have hkWord : (c.1 : ℤ)≤lim.word :=
      (Int.ofNat_le.mpr (show c.1≤terms by omega)).trans htermsWord
    have hs := LightTernaryMomentChannelFactory.meets (d := d+1) S ν B C
      (aggregate (steps.take idx) value c.1) H hw (by omega) (by omega) (by omega)
      hrowEnd hleft hright houtBefore hout hleftSpace hBν hCν hBabs hCabs
      (hI.1 c.1 hc.1) hbounded (hleftWord c.1 hc.1 c.2 hc.2)
      (hrightWord c.1 hc.1 c.2 hc.2) haddWord hkWord hargsWord hleftHom hrightHom hQ
    apply hs.mono le_rfl
    rintro r ξ ⟨_,hrow,hrest⟩
    have hadvance := TernaryMomentMatrixInvariant.advance (steps.take idx) value hc.1 hwindow hI hrow hrest
    have htake : steps.take (idx+1)=steps.take idx++[c] := by
      rw [List.take_succ_eq_append_getElem hidx,hcget]
    simpa only [htake] using hadvance
  have hh := LightTernaryMomentDriver.program_meets S.left.xs S.left.ys S.left.zs
    S.right.xs S.right.ys S.right.zs steps (cost S) value μ hw (by omega)
    hwindow hleftSpace htermsWord hstep
  apply hh.mono le_rfl
  intro r ν hI
  refine ⟨TernaryMomentMatrixInvariant.complete value hI,?_⟩
  intro x hx
  exact hI.2 x (by omega) (Or.inl hx)

end ThreeSum.LightTernaryCertifiedMomentDriver
