import Submission.ThreeSum.LightTernaryCertifiedMomentDriver
import Submission.ThreeSum.TernaryNativePairMoments

/-! A pure resource certificate for the complete actual reporting driver. -/
noncomputable section
namespace ThreeSum.LightTernaryCertifiedMomentDriver
open Light TernaryMomentSchedule LightTernaryMomentChannelFactory

structure Resources {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (lim : Limits) (d originalB originalC matrix terms a b U W : ℕ)
    (μ : ℕ→ℤ) (B C : ℕ→ℤ) : Prop where
  hseed : ∀ k<terms, ∀ j≤k,
      TernarySourceCountExecutionFactory.Seed S lim (d+2) S.left.weightBase μ
        (leftWeights k j B) (rightWeights k j C)
  himmutable : TernarySourceCountExecutionFactory.Immutable S matrix
  hw : (lim.space : ℤ)≤lim.word
  hd : d+2<lim.depth
  hBspace : originalB+S.left.NL≤matrix
  hCspace : originalC+S.right.NL≤matrix
  hwindow : matrix+terms*S.front.count≤S.left.weightBase
  hleft : S.left.weightBase+S.left.NL≤S.right.weightBase
  hright : S.right.weightBase+S.right.NL≤lim.space
  houtBefore : S.left.weightBase≤S.front.dst
  hout : S.front.dst+S.front.count≤lim.space
  hleftSpace : S.left.weightBase≤lim.space
  hB : ∀ i<S.left.NL, μ (originalB+i)=B i
  hC : ∀ i<S.right.NL, μ (originalC+i)=C i
  hBabs : ∀ i<S.left.NL, |B i|≤(U : ℤ)
  hCabs : ∀ i<S.right.NL, |C i|≤(U : ℤ)
  hscore : ∀ k<terms, ∀ j≤k, ∀ i<S.front.count, |score S B C k j i|≤(W : ℤ)
  hleftWord : ∀ k<terms, ∀ j≤k,
      max (U : ℤ) (2*((k.choose j : ℤ)+1)*((U : ℤ)+2)^j)≤lim.word
  hrightWord : ∀ k<terms, ∀ j≤k, max (U : ℤ) (2*((U : ℤ)+1)^(k-j))≤lim.word
  haddWord : 2*(((channels terms).length*W : ℕ) : ℤ)≤lim.word
  htermsWord : (terms : ℤ)≤lim.word
  hargsWord : ∀ z∈LightTernaryMomentChannelFactory.args S originalB originalC matrix, |z|≤lim.word
  hleftHom : ∀ pair∈S.left.records, TernaryBank.rank (S.front.E.word (S.left.key pair.2))=a
  hrightHom : ∀ pair∈S.right.records, TernaryBank.rank (S.front.E.word (S.right.key pair.2))=b
  hQ : ∀ i<S.front.count, TernaryBank.rank (S.front.Q i)=a+b

theorem Resources.run {N d originalB originalC matrix terms a b U W : ℕ}
    {S : TernarySourceCountExecutionFactory.Setup N} {lim : Limits}
    {μ : ℕ→ℤ} {B C : ℕ→ℤ}
    (H : Resources S lim d originalB originalC matrix terms a b U W μ B C) :
    Meets lim (program S terms) (127*(channels terms).length+1) d
      (LightTernaryMomentChannelFactory.args S originalB originalC matrix) μ (time S terms)
      (fun _ ν => (∀ k<terms, ∀ i<S.front.count,
        ν (matrix+k*S.front.count+i)=∑ p : TernaryNativePairMoments.Pair S i,
          TernaryNativePairMoments.mass S i p*TernaryNativePairMoments.mode B C p^k) ∧
        Kept μ ν matrix) := by
  have hh := meets S μ B C
    H.hseed H.himmutable H.hw H.hd H.hBspace H.hCspace H.hwindow H.hleft H.hright H.houtBefore H.hout H.hleftSpace H.hB H.hC H.hBabs H.hCabs H.hscore H.hleftWord H.hrightWord H.haddWord H.htermsWord H.hargsWord H.hleftHom H.hrightHom H.hQ
  apply hh.mono le_rfl
  rintro r ν ⟨hm,hkeep⟩
  refine ⟨?_,hkeep⟩
  intro k hk i hi
  rw [hm k hk i hi,TernaryNativePairMoments.channel_sum]

end ThreeSum.LightTernaryCertifiedMomentDriver
