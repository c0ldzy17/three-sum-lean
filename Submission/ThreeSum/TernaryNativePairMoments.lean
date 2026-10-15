import Submission.ThreeSum.LightTernaryMomentChannelFactory
import Submission.ThreeSum.TernaryPhysicalTensorChannels
import Submission.ThreeSum.TernaryPhysicalMomentSupport
import Submission.ThreeSum.TernaryPairedSupport

/-! The literal pair type and positive measure computed by the actual moment
driver. Native dictionary multiplicities and original duplicates are retained. -/
noncomputable section
namespace ThreeSum.TernaryNativePairMoments
open Finset TernaryJointType
open scoped BigOperators

def leftSet {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (i : ℕ) :=
  TernarySourceHostModel.channel S.left.records S.left.group (S.front.group i)
def rightSet {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (i : ℕ) :=
  TernarySourceHostModel.channel S.right.records S.right.group (S.front.group i)
def leftWord {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (p : ℕ×ℕ) :=
  S.front.E.word (S.left.key p.2)
def rightWord {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (p : ℕ×ℕ) :=
  S.front.E.word (S.right.key p.2)

def pairs {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (i : ℕ) :
    Finset ((ℕ×ℕ)×(ℕ×ℕ)) :=
  TernaryPhysicalTensorChannels.records (leftSet S i) (rightSet S i)
    (leftWord S) (rightWord S) (S.front.Q i)

abbrev Pair {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (i : ℕ) : Type := pairs S i

def mode {N : ℕ} {S : TernarySourceCountExecutionFactory.Setup N} {i : ℕ}
    (B C : ℕ→ℤ) (p : Pair S i) : ℤ := C p.val.2.1-B p.val.1.1

def mass {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (i : ℕ) (_ : Pair S i) : ℤ :=
  TernaryConvolution.factorial (S.front.Q i)

theorem mass_positive {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (i : ℕ) :
    ∀ p : Pair S i, 0<mass S i p := by
  intro p
  exact TernaryConvolution.factorial_pos _

/-- The binomial channel sum is exactly the positive physical moment,
including the query word's common, positive factorial factor. -/
theorem channel_sum {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (B C : ℕ→ℤ) (k i : ℕ) :
    (∑ j∈range (k+1), LightTernaryMomentChannelFactory.score S B C k j i)=
      ∑ p : Pair S i, mass S i p*mode B C p^k := by
  classical
  unfold LightTernaryMomentChannelFactory.score
  rw [← mul_sum]
  have hs := TernaryWeightChannels.pair_moment_channels
    (leftSet S i) (rightSet S i) (leftWord S) (rightWord S)
    (fun p => B p.1) (fun p => C p.1) (S.front.Q i) k
  simp only [TernaryWeightChannels.leftMoment_eval,TernaryWeightChannels.rightMoment_eval] at hs
  rw [show
      (∑ j∈range (k+1), TernaryWeightedPhysicalSources.pairWeight
        (TernarySourceHostModel.channel S.left.records S.left.group (S.front.group i))
        (TernarySourceHostModel.channel S.right.records S.right.group (S.front.group i))
        (fun pair => S.front.E.word (S.left.key pair.2))
        (fun pair => S.front.E.word (S.right.key pair.2))
        (fun pair => LightTernaryMomentChannelFactory.leftWeights k j B pair.1)
        (fun pair => LightTernaryMomentChannelFactory.rightWeights k j C pair.1) (S.front.Q i))=
      ∑ b∈leftSet S i, ∑ c∈rightSet S i,
        if TernaryConvolution.Adds (leftWord S b) (rightWord S c) (S.front.Q i)
          then (C c.1-B b.1)^k else 0 from hs]
  rw [← TernaryPhysicalTensorChannels.sum_records (leftSet S i) (rightSet S i)
    (leftWord S) (rightWord S) (S.front.Q i) (fun p => (C p.2.1-B p.1.1)^k),Finset.mul_sum]
  rfl

/-- The support convention in the paired-rank cap is exactly the support
consumed by the physical moment detector. -/
theorem support_eq {P : Type*} [Fintype P] (mode : P→ℤ) :
    TernaryPhysicalMomentSupport.support mode=TernaryPairedSupport.physicalSupport mode := rfl

end ThreeSum.TernaryNativePairMoments
