import Submission.ThreeSum.TernarySourceCountExecutionFactory
import Submission.ThreeSum.TernarySourceWeightSeed

/-! Readiness before signed source weights are written by the actual channel
initializers. Completing it uses only their proved output-array contents. -/
noncomputable section
namespace ThreeSum.TernarySourceCountExecutionFactory
open Light TernaryJointType

structure Seed {N : ℕ} (S : Setup N) (lim : Limits) (d boundary : ℕ) (μ : ℕ→ℤ)
    (leftWeight rightWeight : ℕ→ℤ) : Prop where
  layout : Layout S
  left : TernarySourceExecutionFactory.Seed S.left lim (d+1) μ leftWeight S.front.E.word
  right : TernarySourceExecutionFactory.Seed S.right lim (d+1) μ rightWeight S.front.E.word
  front : TernaryCountExecutionFactory.Ready S.front lim (d+1) μ (S.F leftWeight) (S.G rightWeight)
  leftInputBefore : S.left.src+S.left.NL≤boundary
  leftCodesBefore : S.left.a+S.left.bank≤boundary
  leftPowersBefore : S.left.powers+(S.left.W+1)≤boundary
  rightInputBefore : S.right.src+S.right.NL≤boundary
  rightCodesBefore : S.right.a+S.right.bank≤boundary
  rightPowersBefore : S.right.powers+(S.right.W+1)≤boundary
  frontCodesBefore : S.front.f.bank+S.front.f.nb≤boundary
  frontRecordsBefore : S.front.records+3*S.front.count≤boundary
  boundaryBefore : boundary≤S.left.base0
  depth : d<lim.depth

structure Immutable {N : ℕ} (S : Setup N) (keep : ℕ) : Prop where
  leftInput : S.left.src+S.left.NL≤keep
  leftCodes : S.left.a+S.left.bank≤keep
  leftPowers : S.left.powers+(S.left.W+1)≤keep
  rightInput : S.right.src+S.right.NL≤keep
  rightCodes : S.right.a+S.right.bank≤keep
  rightPowers : S.right.powers+(S.right.W+1)≤keep
  frontCodes : S.front.f.bank+S.front.f.nb≤keep
  frontRecords : S.front.records+3*S.front.count≤keep

theorem Seed.transport {N : ℕ} {S : Setup N} {lim : Limits} {d boundary keep : ℕ}
    {μ ν : ℕ→ℤ} {leftWeight rightWeight : ℕ→ℤ}
    (H : Seed S lim d boundary μ leftWeight rightWeight) (hkeep : Kept μ ν keep)
    (I : Immutable S keep) : Seed S lim d boundary ν leftWeight rightWeight := by
  exact {H with
    left := H.left.transport hkeep I.leftInput I.leftCodes I.leftPowers
    right := H.right.transport hkeep I.rightInput I.rightCodes I.rightPowers
    front := H.front.transport hkeep I.frontCodes I.frontRecords}

theorem Seed.finish {N : ℕ} {S : Setup N} {lim : Limits} {d boundary : ℕ}
    {μ ν : ℕ→ℤ} {leftWeight rightWeight : ℕ→ℤ}
    (H : Seed S lim d boundary μ leftWeight rightWeight) (hkeep : Kept μ ν boundary)
    (hleftRead : ∀ i<S.left.NL, ν (S.left.weightBase+i)=leftWeight i)
    (hrightRead : ∀ i<S.right.NL, ν (S.right.weightBase+i)=rightWeight i) :
    Ready S lim d ν leftWeight rightWeight where
  layout := H.layout
  left := (H.left.transport hkeep H.leftInputBefore H.leftCodesBefore H.leftPowersBefore).finish hleftRead
  right := (H.right.transport hkeep H.rightInputBefore H.rightCodesBefore H.rightPowersBefore).finish hrightRead
  front := H.front.transport hkeep H.frontCodesBefore H.frontRecordsBefore
  depth := H.depth

theorem Seed.run_physical {N a b : ℕ} {S : Setup N} {lim : Limits} {d boundary : ℕ}
    {μ ν : ℕ→ℤ} {leftWeight rightWeight : ℕ→ℤ}
    (H : Seed S lim d boundary μ leftWeight rightWeight) (hkeep : Kept μ ν boundary)
    (hleftRead : ∀ i<S.left.NL, ν (S.left.weightBase+i)=leftWeight i)
    (hrightRead : ∀ i<S.right.NL, ν (S.right.weightBase+i)=rightWeight i)
    (hleft : ∀ pair∈S.left.records, TernaryBank.rank (S.front.E.word (S.left.key pair.2))=a)
    (hright : ∀ pair∈S.right.records, TernaryBank.rank (S.front.E.word (S.right.key pair.2))=b)
    (hQ : ∀ j<S.front.count, TernaryBank.rank (S.front.Q j)=a+b) :
    Meets lim S.program 122 d S.argv ν S.runtime
      (fun _ ξ => Kept ν ξ boundary ∧ ∀ j<S.front.count,
        ξ (S.front.dst+j)=TernaryConvolution.factorial (S.front.Q j)*
          TernaryWeightedPhysicalSources.pairWeight
            (TernarySourceHostModel.channel S.left.records S.left.group (S.front.group j))
            (TernarySourceHostModel.channel S.right.records S.right.group (S.front.group j))
            (fun pair => S.front.E.word (S.left.key pair.2))
            (fun pair => S.front.E.word (S.right.key pair.2))
            (fun pair => leftWeight pair.1) (fun pair => rightWeight pair.1) (S.front.Q j)) := by
  apply ((H.finish hkeep hleftRead hrightRead).run_physical hleft hright hQ).mono le_rfl
  rintro r ξ ⟨hprefix,hvalue⟩
  exact ⟨fun x hx => hprefix x (lt_of_lt_of_le hx H.boundaryBefore),hvalue⟩

end ThreeSum.TernarySourceCountExecutionFactory
