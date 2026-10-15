import Submission.ThreeSum.LightTernaryScalarChannel

/-! Literal original B/C power-and-binomial source weight initializers. -/
namespace ThreeSum.LightTernaryMomentChannels
open Light LightFixedArithmetic TernaryWeightChannels

theorem powerCircuit_bound (e : Circuit) (k : ℕ) (U : ℤ) :
    (powerCircuit e k).bound U=2*(e.bound U)^k := by
  induction k with
  | zero => norm_num [powerCircuit,Circuit.bound]
  | succ k ih => simp only [powerCircuit,Circuit.bound,ih,pow_succ]; ring

theorem left_bound (k j : ℕ) (U : ℤ) :
    (leftMoment k j).bound U=2*((k.choose j : ℤ)+1)*(U+2)^j := by
  simp only [leftMoment,Circuit.bound,powerCircuit_bound,Int.abs_natCast]
  ring

theorem right_bound (k j : ℕ) (U : ℤ) :
    (rightMoment k j).bound U=2*(U+1)^(k-j) := by
  simp only [rightMoment,scalarPower,powerCircuit_bound,Circuit.bound]

variable {lim : Limits} {P : Program} {d : ℕ}

theorem left_meets {k j p src n dst U : ℕ}
    (hmain : P[p]?=some (LightTernaryScalarChannel.body (leftMoment k j)))
    (μ : ℕ→ℤ) (B : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hsrc : src+n≤lim.space) (hdst : dst+n≤lim.space)
    (hsep : LightArray.SourceSafe src dst n)
    (hread : ∀ i<n, μ (src+i)=B i) (hB : ∀ i<n, |B i|≤(U : ℤ))
    (hword : max (U : ℤ) (2*((k.choose j : ℤ)+1)*((U : ℤ)+2)^j)≤lim.word) :
    Meets lim P p d [src,n,dst] μ (LightTernaryScalarChannel.time (leftMoment k j) n)
      (fun _ ν => (∀ i<n, ν (dst+i)=(k.choose j : ℤ)*(-(B i))^j) ∧ SameOutside μ ν dst n) := by
  have hh : max (U : ℤ) ((leftMoment k j).bound U)≤lim.word := by rwa [left_bound]
  simpa only [leftMoment_eval] using LightTernaryScalarChannel.meets (leftMoment k j)
    hmain μ B hw hsrc hdst hsep hread hB hh

theorem right_meets {k j p src n dst U : ℕ}
    (hmain : P[p]?=some (LightTernaryScalarChannel.body (rightMoment k j)))
    (μ : ℕ→ℤ) (C : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hsrc : src+n≤lim.space) (hdst : dst+n≤lim.space)
    (hsep : LightArray.SourceSafe src dst n)
    (hread : ∀ i<n, μ (src+i)=C i) (hC : ∀ i<n, |C i|≤(U : ℤ))
    (hword : max (U : ℤ) (2*((U : ℤ)+1)^(k-j))≤lim.word) :
    Meets lim P p d [src,n,dst] μ (LightTernaryScalarChannel.time (rightMoment k j) n)
      (fun _ ν => (∀ i<n, ν (dst+i)=(C i)^(k-j)) ∧ SameOutside μ ν dst n) := by
  have hh : max (U : ℤ) ((rightMoment k j).bound U)≤lim.word := by rwa [right_bound]
  simpa only [rightMoment_eval] using LightTernaryScalarChannel.meets (rightMoment k j)
    hmain μ C hw hsrc hdst hsep hread hC hh

/-- Original-position gathering in the weighted bank reads initialized
weights, including repeated source-word occurrences. -/
theorem initialized_weight_gather {μ : ℕ→ℤ} {dst originalCount count : ℕ}
    (weight : ℕ→ℤ) (originalPosition : ℕ→ℕ)
    (hinit : ∀ i<originalCount, μ (dst+i)=weight i)
    (hpos : ∀ i<count, originalPosition i<originalCount) :
    ∀ i<count, μ (dst+originalPosition i)=weight (originalPosition i) := by
  intro i hi
  exact hinit _ (hpos i hi)

end ThreeSum.LightTernaryMomentChannels
