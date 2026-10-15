import Submission.ThreeSum.LightTernarySeedScore

namespace ThreeSum.TernarySeedScoreRecords

def Holds (flags scoresB scoresC scoresP completed : ℕ)
    (flag fB fC fP : ℕ → ℤ) (μ : ℕ → ℤ) : Prop :=
  ∀ i<completed, μ (flags+i)=flag i ∧ μ (scoresB+i)=fB i ∧
    μ (scoresC+i)=fC i ∧ μ (scoresP+i)=fP i

def write (μ : ℕ → ℤ) (flags scoresB scoresC scoresP i : ℕ)
    (flag b c paired : ℤ) : ℕ → ℤ :=
  Function.update (Function.update (Function.update (Function.update μ
    (flags+i) flag) (scoresB+i) b) (scoresC+i) c) (scoresP+i) paired

/-- Writing the four actual score outputs extends the completed prefix by
one. Equal numerical seed scores remain separate array entries. -/
theorem Holds.next {flags scoresB scoresC scoresP n i : ℕ}
    {flag fB fC fP : ℕ → ℤ} {μ : ℕ → ℤ}
    (h : Holds flags scoresB scoresC scoresP i flag fB fC fP μ) (hi : i<n)
    (hFB : flags+n≤scoresB) (hBC : scoresB+n≤scoresC) (hCP : scoresC+n≤scoresP) :
    Holds flags scoresB scoresC scoresP (i+1) flag fB fC fP
      (write μ flags scoresB scoresC scoresP i (flag i) (fB i) (fC i) (fP i)) := by
  intro j hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj|rfl
  · have hold := h j hj
    simpa only [write,Function.update_of_ne (show flags+j≠scoresP+i by omega),
      Function.update_of_ne (show flags+j≠scoresC+i by omega),
      Function.update_of_ne (show flags+j≠scoresB+i by omega),
      Function.update_of_ne (show flags+j≠flags+i by omega),
      Function.update_of_ne (show scoresB+j≠scoresP+i by omega),
      Function.update_of_ne (show scoresB+j≠scoresC+i by omega),
      Function.update_of_ne (show scoresB+j≠scoresB+i by omega),
      Function.update_of_ne (show scoresB+j≠flags+i by omega),
      Function.update_of_ne (show scoresC+j≠scoresP+i by omega),
      Function.update_of_ne (show scoresC+j≠scoresC+i by omega),
      Function.update_of_ne (show scoresC+j≠scoresB+i by omega),
      Function.update_of_ne (show scoresC+j≠flags+i by omega),
      Function.update_of_ne (show scoresP+j≠scoresP+i by omega),
      Function.update_of_ne (show scoresP+j≠scoresC+i by omega),
      Function.update_of_ne (show scoresP+j≠scoresB+i by omega),
      Function.update_of_ne (show scoresP+j≠flags+i by omega)] using hold
  · simp only [write,Function.update_of_ne (show flags+j≠scoresP+j by omega),
      Function.update_of_ne (show flags+j≠scoresC+j by omega),
      Function.update_of_ne (show flags+j≠scoresB+j by omega),Function.update_self,
      Function.update_of_ne (show scoresB+j≠scoresP+j by omega),
      Function.update_of_ne (show scoresB+j≠scoresC+j by omega),
      Function.update_of_ne (show scoresC+j≠scoresP+j by omega),and_self]

theorem Holds.transfer {flags scoresB scoresC scoresP n i cutoff : ℕ}
    {flag fB fC fP : ℕ → ℤ} {μ ν : ℕ → ℤ}
    (h : Holds flags scoresB scoresC scoresP i flag fB fC fP μ)
    (hi : i≤n) (hF : flags+n≤cutoff) (hB : scoresB+n≤cutoff)
    (hC : scoresC+n≤cutoff) (hP : scoresP+n≤cutoff)
    (hk : Light.Kept μ ν cutoff) :
    Holds flags scoresB scoresC scoresP i flag fB fC fP ν := by
  intro j hj
  rw [hk _ (by omega),hk _ (by omega),hk _ (by omega),hk _ (by omega)]
  exact h j hj

end ThreeSum.TernarySeedScoreRecords
