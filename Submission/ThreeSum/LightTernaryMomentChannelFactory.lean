import Submission.ThreeSum.TernarySourceCountWeightSeed
import Submission.ThreeSum.LightTernaryMomentSourceProgram

/-! An original-source signed moment channel, closed from pure readiness
and resource certificates. There are no execution callbacks in `meets`. -/
noncomputable section
namespace ThreeSum.LightTernaryMomentChannelFactory
open Light TernaryJointType TernaryWeightChannels

def leftWeights (k j : ℕ) (B : ℕ→ℤ) (i : ℕ) : ℤ := (k.choose j : ℤ)*(-(B i))^j
def rightWeights (k j : ℕ) (C : ℕ→ℤ) (i : ℕ) : ℤ := (C i)^(k-j)

def score {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (B C : ℕ→ℤ) (k j i : ℕ) : ℤ :=
  TernaryConvolution.factorial (S.front.Q i)*
    TernaryWeightedPhysicalSources.pairWeight
      (TernarySourceHostModel.channel S.left.records S.left.group (S.front.group i))
      (TernarySourceHostModel.channel S.right.records S.right.group (S.front.group i))
      (fun pair => S.front.E.word (S.left.key pair.2))
      (fun pair => S.front.E.word (S.right.key pair.2))
      (fun pair => leftWeights k j B pair.1) (fun pair => rightWeights k j C pair.1) (S.front.Q i)

def program {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (k j : ℕ) : Program :=
  LightTernaryMomentSourceProgram.program S.left.xs S.left.ys S.left.zs
    S.right.xs S.right.ys S.right.zs k j

def args {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (originalB originalC matrix : ℕ) : List ℤ :=
  LightTernaryMomentChannelStep.args originalB S.left.NL originalC S.right.NL
    S.left.weightBase S.right.weightBase matrix S.front.count S.front.dst S.argv

theorem backend_length {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) :
    S.argv.length=106 := by rfl

theorem meets {lim : Limits} {N a b d originalB originalC matrix k j U V : ℕ}
    (S : TernarySourceCountExecutionFactory.Setup N) (μ : ℕ→ℤ) (B C accum : ℕ→ℤ)
    (H : TernarySourceCountExecutionFactory.Seed S lim (d+1) S.left.weightBase μ
      (leftWeights k j B) (rightWeights k j C))
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+1<lim.depth)
    (hBspace : originalB+S.left.NL≤S.left.weightBase)
    (hCspace : originalC+S.right.NL≤S.left.weightBase)
    (hmatrix : matrix+k*S.front.count+S.front.count≤S.left.weightBase)
    (hleft : S.left.weightBase+S.left.NL≤S.right.weightBase)
    (hright : S.right.weightBase+S.right.NL≤lim.space)
    (houtBefore : S.left.weightBase≤S.front.dst) (hout : S.front.dst+S.front.count≤lim.space)
    (hleftSpace : S.left.weightBase≤lim.space)
    (hB : ∀ i<S.left.NL, μ (originalB+i)=B i)
    (hC : ∀ i<S.right.NL, μ (originalC+i)=C i)
    (hBabs : ∀ i<S.left.NL, |B i|≤(U : ℤ)) (hCabs : ∀ i<S.right.NL, |C i|≤(U : ℤ))
    (haccum : ∀ i<S.front.count, μ (matrix+k*S.front.count+i)=accum i)
    (hbounded : ∀ i<S.front.count, |accum i|≤(V : ℤ) ∧ |score S B C k j i|≤(V : ℤ))
    (hleftWord : max (U : ℤ) (2*((k.choose j : ℤ)+1)*((U : ℤ)+2)^j)≤lim.word)
    (hrightWord : max (U : ℤ) (2*((U : ℤ)+1)^(k-j))≤lim.word)
    (haddWord : 2*(V : ℤ)≤lim.word) (hkWord : (k : ℤ)≤lim.word)
    (hargsWord : ∀ z∈args S originalB originalC matrix, |z|≤lim.word)
    (hleftHom : ∀ pair∈S.left.records, TernaryBank.rank (S.front.E.word (S.left.key pair.2))=a)
    (hrightHom : ∀ pair∈S.right.records, TernaryBank.rank (S.front.E.word (S.right.key pair.2))=b)
    (hQ : ∀ i<S.front.count, TernaryBank.rank (S.front.Q i)=a+b) :
    Meets lim (program S k j) 126 d (args S originalB originalC matrix) μ
      (LightTernaryMomentChannelStep.time k j S.left.NL S.right.NL S.front.count S.runtime 106)
      (fun r ν => r=0 ∧
        (∀ i<S.front.count, ν (matrix+k*S.front.count+i)=accum i+score S B C k j i) ∧
        ∀ x<S.left.weightBase,
          (x<matrix+k*S.front.count ∨ matrix+k*S.front.count+S.front.count≤x) → ν x=μ x) := by
  have hpos : ∀ i∈LightTernaryMomentSourceProgram.positions, 9 ≤ i ∧ i < 9+S.argv.length := by
    apply LightTernaryMomentSourceProgram.positions_range
    rw [backend_length]
  have hhost : ∀ ν, Kept μ ν S.left.weightBase →
      (∀ i<S.left.NL, ν (S.left.weightBase+i)=(k.choose j : ℤ)*(-(B i))^j) →
      (∀ i<S.right.NL, ν (S.right.weightBase+i)=(C i)^(k-j)) →
      Meets lim (program S k j) 122 (d+1)
        (LightTernaryMomentChannelStep.values LightTernaryMomentSourceProgram.positions
          (args S originalB originalC matrix)) ν S.runtime
        (fun _ ξ => Kept ν ξ S.left.weightBase ∧ ∀ i<S.front.count,
          ξ (S.front.dst+i)=score S B C k j i) := by
    intro ν hkeep hL hR
    rw [args,LightTernaryMomentSourceProgram.values_positions _ _ _ _ _ _ _ _ _ S.argv (backend_length S)]
    exact (H.run_physical hkeep hL hR hleftHom hrightHom hQ).append
      (LightTernaryMomentSourceProgram.extra k j)
  have hh := (LightTernaryMomentSourceProgram.procs S.left.xs S.left.ys S.left.zs
    S.right.xs S.right.ys S.right.zs k j (9+S.argv.length)).meets μ B C accum (score S B C k j)
    hw hd hBspace hCspace hmatrix hleft hright houtBefore hout hleftSpace hB hC hBabs hCabs
    haccum hbounded hleftWord hrightWord haddWord hkWord hpos hargsWord hhost
  simpa only [program,args,LightTernaryMomentSourceProgram.positions,List.length_map,List.length_range] using hh

end ThreeSum.LightTernaryMomentChannelFactory
