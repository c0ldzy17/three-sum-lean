import Submission.ThreeSum.LightTernaryTensorFactoryScaled
import Submission.ThreeSum.TernaryNativePairMoments

noncomputable section
namespace ThreeSum.TernaryNativeTensorScore
open TernaryJointType TernaryNativePairMoments
open LightTernaryTensorFactory LightTernaryPairedPolynomial
open scoped BigOperators
set_option maxHeartbeats 1500000

private theorem block_div (p u v : ℕ) (hp : 0<p) (hv : v<p) :
    (u*p+v)/p=u := by
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ hp,Nat.div_eq_of_lt hv]
  simp
private theorem block_mod (p u v : ℕ) (hv : v<p) : (u*p+v)%p=v := by
  simp [Nat.add_mod,Nat.mul_mod,Nat.mod_eq_of_lt hv]

/-- The actual radix decoder reads the four physical row-major tensor
coordinates exactly; no column tuple is supplied as runtime advice. -/
theorem packed_digits {p a b c d : ℕ} (hp : 0<p)
    (ha : a<p) (hb : b<p) (hc : c<p) (hd : d<p) :
    WeightEnumeration.digit p 4 (tensorIndex p a b c d) 0=a ∧
    WeightEnumeration.digit p 4 (tensorIndex p a b c d) 1=b ∧
    WeightEnumeration.digit p 4 (tensorIndex p a b c d) 2=c ∧
    WeightEnumeration.digit p 4 (tensorIndex p a b c d) 3=d := by
  have h1 := block_div p ((a*p+b)*p+c) d hp hd
  have h2 := block_div p (a*p+b) c hp hc
  have h3 := block_div p a b hp hb
  have hm1 := block_mod p ((a*p+b)*p+c) d hd
  have hm2 := block_mod p (a*p+b) c hc
  have hm3 := block_mod p a b hb
  have hdiv2 : tensorIndex p a b c d/p^2=a*p+b := by
    rw [show p^2=p*p by ring,←Nat.div_div_eq_div_mul]
    change (((a*p+b)*p+c)*p+d)/p/p=a*p+b
    rw [h1,h2]
  have hdiv3 : tensorIndex p a b c d/p^3=a := by
    rw [show p^3=p^2*p by ring,←Nat.div_div_eq_div_mul,hdiv2,h3]
  change tensorIndex p a b c d/p^(4-1-0)%p=a ∧
    tensorIndex p a b c d/p^(4-1-1)%p=b ∧
    tensorIndex p a b c d/p^(4-1-2)%p=c ∧
    tensorIndex p a b c d/p^(4-1-3)%p=d
  norm_num only [Nat.reduceSub,pow_one,pow_zero,Nat.div_one]
  refine ⟨?_,?_,?_,?_⟩
  · rw [hdiv3]
    exact Nat.mod_eq_of_lt ha
  · rw [hdiv2]
    exact hm3
  · change (((a*p+b)*p+c)*p+d)/p%p=c
    rw [h1]
    exact hm2
  · exact hm1

def originalLeft {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (J : ℕ) (L : ℕ→ℕ→ℤ) (i : ℕ) (pair : Pair S i) (a : Fin (J+2)) : ℤ := L pair.val.1.1 a.val

def originalRight {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (J : ℕ) (R : ℕ→ℕ→ℤ) (i : ℕ) (pair : Pair S i) (a : Fin (J+2)) : ℤ := R pair.val.2.1 a.val

theorem score_eq_original_tensor {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (J : ℕ) (L R : ℕ→ℕ→ℤ) (i : ℕ) (a b c d : Fin (J+2)) :
    score S J L R i (tensorIndex (J+2) a.val b.val c.val d.val)=
      TernaryConvolution.factorial (S.front.Q i)*
        TernaryPairedTensor.tensor (originalLeft S J L i) (originalRight S J R i) a b c d := by
  have hdigit := packed_digits (by omega : 0<J+2) a.isLt b.isLt c.isLt d.isLt
  have hphysical := TernaryPhysicalTensorChannels.fourth_tensor_on_physical_records
    (leftSet S i) (rightSet S i) (leftWord S) (rightWord S)
    (fun pair (a : Fin (J+2)) => L pair.1 a.val)
    (fun pair (a : Fin (J+2)) => R pair.1 a.val) a b c d (S.front.Q i)
  rw [TernaryWeightedPhysicalSources.convolution_histograms] at hphysical
  unfold score leftWeights rightWeights LightTernaryTensorDriver.digit
  rw [hdigit.1,hdigit.2.1,hdigit.2.2.1,hdigit.2.2.2]
  exact congrArg (fun z => TernaryConvolution.factorial (S.front.Q i)*z) hphysical

def pairedPotential {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (K J : ℕ) (L R : ℕ→ℕ→ℤ) : ℕ :=
  ∑ i : Fin S.front.count, ∑ e : Fin K→Pair S i.val,
    TernaryPairedPotential.rowWeight (Sum.elim
      (fun j => originalLeft S J L i.val (e j)) (fun j => originalRight S J R i.val (e j)))

/-- No finite tensor-model equality remains among the assumptions: original
physical record multiplicities and the four channels are identified here. -/
theorem run_native {N a b d K J config ls rs tensorBase quad powers cols potPowers U t : ℕ}
    {S : TernarySourceCountExecutionFactory.Setup N} {lim : Light.Limits} {μ : ℕ→ℤ}
    {L R : ℕ→ℕ→ℤ} {V : ℤ}
    (H : Ready S lim d K J config ls rs tensorBase quad powers cols potPowers μ L R U V)
    (hleft : ∀ pair∈S.left.records, TernaryBank.rank (S.front.E.word (S.left.key pair.2))=a)
    (hright : ∀ pair∈S.right.records, TernaryBank.rank (S.front.E.word (S.right.key pair.2))=b)
    (hQ : ∀ j<S.front.count, TernaryBank.rank (S.front.Q j)=a+b)
    (hcountTwo : ∀ j<S.front.count, digitCount (S.front.Q j) 2=t) :
    Light.Meets lim (program S K) 138 d
      [config,ls,S.left.NL,rs,S.right.NL,J,S.left.weightBase,S.right.weightBase,
        tensorBase,S.front.count,S.front.dst,quad,powers,cols,potPowers] μ
      (LightTernaryTensorDriver.time K J S.left.NL S.right.NL S.front.count S.runtime)
      (fun r ν => r=((2 : ℤ)^t)^K*(pairedPotential S K J L R : ℤ) ∧
        LightTernaryTensorDriver.InputKept μ ν quad tensorBase S.front.count ((J+2)^4)) := by
  simpa only [pairedPotential,Nat.cast_sum] using (H.run_scaled hleft hright hQ (fun i : Fin S.front.count => Pair S i.val)
    (fun i => originalLeft S J L i.val) (fun i => originalRight S J R i.val) ((2 : ℤ)^t)
    (by
      intro i a b c e
      rw [score_eq_original_tensor,TernaryConvolution.factorial_eq_power_two,hcountTwo i.val i.isLt]))

end ThreeSum.TernaryNativeTensorScore
