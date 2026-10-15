import Submission.ThreeSum.LightTernaryTensorFactory

noncomputable section
namespace ThreeSum.LightTernaryTensorFactory
open Light TernaryJointType
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

structure Ready {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (lim : Limits) (d K J config ls rs tensor quad powers cols potPowers : ℕ)
    (μ : ℕ→ℤ) (L R : ℕ→ℕ→ℤ) (U : ℕ) (V : ℤ) : Prop where
  immutable : TernarySourceCountExecutionFactory.Immutable S tensor
  seed : ∀ q<(J+2)^4, TernarySourceCountExecutionFactory.Seed S lim (d+2)
    S.left.weightBase μ (leftWeights J q L) (rightWeights J q R)
  wordSpace : (lim.space : ℤ)≤lim.word
  depth : d+4<lim.depth
  tensorEnd : tensor+S.front.count*(J+2)^4≤quad
  quadEnd : quad+4≤powers
  powersEnd : powers+5≤S.left.weightBase
  leftEnd : S.left.weightBase+S.left.NL≤S.right.weightBase
  rightSpace : S.right.weightBase+S.right.NL≤lim.space
  countAfter : S.left.weightBase≤S.front.dst
  countSpace : S.front.dst+S.front.count≤lim.space
  configEnd : config+106≤tensor
  leftInputEnd : ls+S.left.NL*(J+2)≤tensor
  rightInputEnd : rs+S.right.NL*(J+2)≤tensor
  configRead : ∀ i<106, μ (config+i)=S.argv.getD i 0
  leftRead : ∀ i<S.left.NL, ∀ j<J+2,
    μ (ls+i*(J+2)+TernarySignedLayout.offset J j)=L i j
  rightRead : ∀ i<S.right.NL, ∀ j<J+2,
    μ (rs+i*(J+2)+TernarySignedLayout.offset J j)=R i j
  leftBound : ∀ i<S.left.NL, ∀ j<J+2, |L i j|≤(U : ℤ)
  rightBound : ∀ i<S.right.NL, ∀ j<J+2, |R i j|≤(U : ℤ)
  channelWord : ((U : ℤ)+1)^2≤lim.word
  indexWord : ((J+3 : ℕ) : ℤ)≤lim.word
  countWord : (S.front.count : ℤ)≤lim.word
  radixWord : (((J+2)^4 : ℕ) : ℤ)≤lim.word
  rowWord : (LightWeightRow.word 4 (J+2) ((J+2)^4) 0 1 : ℤ)≤lim.word
  potentialCols : cols+TernaryPairedColumnEnumeration.width K≤lim.space
  potentialPowers : potPowers+(TernaryPairedColumnEnumeration.width K+1)≤lim.space
  colsAfter : quad≤cols
  potentialPowersAfter : quad≤potPowers
  potentialApart : Apart potPowers (TernaryPairedColumnEnumeration.width K+1)
    cols (TernaryPairedColumnEnumeration.width K)
  scoreNonneg : 0≤V
  scoreBound : ∀ w<S.front.count, ∀ q<(J+2)^4, |score S J L R w q|≤V
  kernelWord : LightTernaryPairedPotential.word K (J+2) V≤lim.word
  polyWord : (LightTernaryPairedPolynomial.polynomial K).coefficient*
    (V+1)^(LightTernaryPairedPolynomial.polynomial K).degree≤lim.word
  sumWord : (S.front.count : ℤ)*((J+2)^TernaryPairedColumnEnumeration.width K : ℕ)*
    (LightTernaryPairedPolynomial.polynomial K).bound V≤lim.word

/-- Complete actual tensor execution from pure memory, finite-model and
resource readiness. No execution premise or oracle occurs in this contract. -/
theorem Ready.run {N a b d K J config ls rs tensor quad powers cols potPowers U : ℕ}
    {S : TernarySourceCountExecutionFactory.Setup N} {lim : Limits} {μ : ℕ→ℤ}
    {L R : ℕ→ℕ→ℤ} {V : ℤ}
    (H : Ready S lim d K J config ls rs tensor quad powers cols potPowers μ L R U V)
    (hleft : ∀ pair∈S.left.records, TernaryBank.rank (S.front.E.word (S.left.key pair.2))=a)
    (hright : ∀ pair∈S.right.records, TernaryBank.rank (S.front.E.word (S.right.key pair.2))=b)
    (hQ : ∀ j<S.front.count, TernaryBank.rank (S.front.Q j)=a+b) :
    Meets lim (program S K) 138 d
      [config,ls,S.left.NL,rs,S.right.NL,J,S.left.weightBase,S.right.weightBase,
        tensor,S.front.count,S.front.dst,quad,powers,cols,potPowers] μ
      (LightTernaryTensorDriver.time K J S.left.NL S.right.NL S.front.count S.runtime)
      (fun r ν => r=LightTernaryPairedPotentialBatch.total K tensor (J+2) ν S.front.count ∧
        (∀ w<S.front.count, ∀ q<(J+2)^4, ν (tensor+w*((J+2)^4)+q)=score S J L R w q) ∧
        LightTernaryTensorDriver.InputKept μ ν quad tensor S.front.count ((J+2)^4)) := by
  have ht := H.tensorEnd
  have hqe := H.quadEnd
  have hpe := H.powersEnd
  have hle := H.leftEnd
  have hrs := H.rightSpace
  have hca := H.countAfter
  have hcs := H.countSpace
  have hce := H.configEnd
  have hls := H.leftInputEnd
  have hrsrc := H.rightInputEnd
  have hpc := H.potentialCols
  have hpp := H.potentialPowers
  have hdepth := H.depth
  have Q := procs S K
  have hquadSpace : quad+4≤lim.space := by omega
  have hpowSpace : powers+5≤lim.space := by omega
  apply LightTernaryTensorDriver.meets K config ls S.left.NL rs S.right.NL J
    S.left.weightBase S.right.weightBase tensor S.front.count S.front.dst quad powers cols potPowers
    μ (score S J L R) S.runtime Q.main Q.powers Q.row Q.digit Q.divide H.wordSpace H.depth
    H.tensorEnd H.quadEnd H.powersEnd (by omega) (by omega) (by omega) (by omega)
    hquadSpace hpowSpace H.indexWord H.countWord H.radixWord H.rowWord
  · intro q hq ν hinput hcoords
    have hkeep : Kept μ ν tensor := by
      intro x hx
      exact hinput x ⟨by omega,Or.inl hx⟩
    have HS := (H.seed q hq).transport hkeep H.immutable
    have hreadL : ∀ i<S.left.NL, ∀ j<J+2,
        ν (ls+i*(J+2)+TernarySignedLayout.offset J j)=L i j := by
      intro i hi j hj
      rw [hkeep _ (by
        have hoff := TernarySignedLayout.offset_lt hj
        have hh := Nat.mul_le_mul_right (J+2) (by omega : i+1≤S.left.NL)
        nlinarith [H.leftInputEnd])]
      exact H.leftRead i hi j hj
    have hreadR : ∀ i<S.right.NL, ∀ j<J+2,
        ν (rs+i*(J+2)+TernarySignedLayout.offset J j)=R i j := by
      intro i hi j hj
      rw [hkeep _ (by
        have hoff := TernarySignedLayout.offset_lt hj
        have hh := Nat.mul_le_mul_right (J+2) (by omega : i+1≤S.right.NL)
        nlinarith [H.rightInputEnd])]
      exact H.rightRead i hi j hj
    apply LightTernaryQuarticStep.meets config ls S.left.NL rs S.right.NL J
      S.left.weightBase S.right.weightBase tensor S.front.count S.front.dst
      (LightTernaryTensorDriver.digit J q 0) (LightTernaryTensorDriver.digit J q 1)
      (LightTernaryTensorDriver.digit J q 2) (LightTernaryTensorDriver.digit J q 3) q ((J+2)^4)
      S.left.weightBase ν L R (fun w => score S J L R w q) S.argv S.runtime
      Q.step Q.channel Q.offset Q.product Q.scatter H.wordSpace (by omega)
      (WeightEnumeration.digit_lt (by omega)) (WeightEnumeration.digit_lt (by omega))
      (WeightEnumeration.digit_lt (by omega)) (WeightEnumeration.digit_lt (by omega)) hq (by positivity)
      (by omega) (by omega) (by omega) (by omega) H.leftEnd H.rightSpace (by omega) le_rfl
      H.countSpace (by omega) H.radixWord H.countWord U H.channelWord H.indexWord hreadL hreadR
      H.leftBound H.rightBound (by rfl) (by intro i hi; exact (hkeep _ (by omega)).trans (H.configRead i hi))
    intro ξ hchanged hL hR
    have hpref : Kept ν ξ S.left.weightBase := by
      intro x hx
      exact hchanged x ⟨Or.inl hx,Or.inl (by omega)⟩
    have HH := HS.run_physical hpref hL hR hleft hright hQ
    simpa only [program_split,score,Nat.add_assoc] using HH.append (extras K)
  · intro ν hread
    have hh := LightTernaryPairedPotentialBatch.meets K tensor (J+2) S.front.count cols potPowers quad ν
      Q.batch Q.potential Q.powers Q.potentialRow Q.potentialDigit Q.potentialDivide Q.polynomial
      (by omega) H.wordSpace (by omega) H.tensorEnd (by omega) H.potentialCols H.potentialPowers
      H.colsAfter H.potentialPowersAfter H.potentialApart V H.scoreNonneg
      (by intro w hw q hq; rw [hread w hw q hq]; exact H.scoreBound w hw q hq)
      H.kernelWord H.polyWord H.sumWord H.countWord
    exact LightTernaryPairedPotentialBatch.receipt_final (by omega) H.tensorEnd hh

end ThreeSum.LightTernaryTensorFactory
