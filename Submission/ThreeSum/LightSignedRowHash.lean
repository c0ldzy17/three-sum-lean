import Submission.ThreeSum.LightReportingAffine
import Submission.ThreeSum.LightNaturalDot

namespace ThreeSum.LightSignedRowHash
open Light
set_option maxHeartbeats 2000000

/-- Adding p to every signed digit gives nonnegative words with the same Fp
image.  The pass includes tags and does not need a conditional or modulus. -/
def lifted (p : ℕ) (z : ℤ) : ℕ := ((p : ℤ)+z).toNat

def body (pLift pDot : ℕ) : Stmt :=
  .call pLift [v 0,v 2,v 3,v 4,k 1] 5 ;;
  .call pDot [v 1,v 2,v 3,v 4] 0

def time (n p b : ℕ) : ℕ := LightReportingAffine.time n+LightNaturalDot.reducedTime n p (p+b)+100

def word (n p b : ℕ) : ℕ := 20*((n+1)*(p+1)*(p+b+1)+p+10)+100

structure Procs (P : Program) (main : ℕ) where
  lift : ℕ
  dot : ℕ
  rawDot : ℕ
  digit : ℕ
  divide : ℕ
  mainBody : P[main]?=some (body lift dot)
  liftBody : P[lift]?=some LightReportingAffine.body
  dotBody : P[dot]?=some (LightNaturalDot.reducedBody rawDot digit)
  rawBody : P[rawDot]?=some LightNaturalDot.body
  digitBody : P[digit]?=some (LightRadixDigit.body divide)
  divideBody : P[divide]?=some LightSmallDivide.body

variable {lim : Limits} {P : Program} {depth : ℕ}

theorem Procs.meets {main src row dst n p b : ℕ} (S : Procs P main)
    (μ : ℕ → ℤ) (z : ℕ → ℤ) (coeff : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+2<lim.depth) (hbp : b<p)
    (hsrc : src+n≤dst) (hrow : row+n≤dst) (hspace : dst+n≤lim.space)
    (hzRead : ∀ i<n, μ (src+i)=z i) (hcRead : ∀ i<n, μ (row+i)=(coeff i : ℤ))
    (hzBound : ∀ i<n, |z i|≤(b : ℤ)) (hcBound : ∀ i<n, coeff i≤p)
    (hword : (word n p b : ℤ)≤lim.word) :
    Meets lim P main depth [src,row,dst,n,p] μ (time n p b)
      (fun r ν => r=(((LightNaturalDot.dot coeff (fun i => lifted p (z i)) n)%p : ℕ) : ℤ) ∧
        SameOutside μ ν dst n) := by
  have hwDot : ((20*((n+1)*(p+1)*(p+b+1)+p+10) : ℕ) : ℤ)≤lim.word := by unfold word at hword; omega
  have hpb : p+b≤20*((n+1)*(p+1)*(p+b+1)+p+10)+100 := by
    have hh : p+b+1≤(n+1)*(p+1)*(p+b+1) := Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have hpbWord : ((p+b : ℕ) : ℤ)≤lim.word := (Int.ofNat_le.mpr hpb).trans hword
  have hpWord : (p : ℤ)≤lim.word := by omega
  have hbWord : (b : ℤ)≤lim.word := by omega
  have h1 : (1 : ℤ)≤lim.word := by omega
  have hnat (i : ℕ) (hi : i<n) : 0≤(p : ℤ)+z i := by have hh := (abs_le.mp (hzBound i hi)).1; omega
  have hlift (i : ℕ) (hi : i<n) : (lifted p (z i) : ℤ)=(p : ℤ)+z i := Int.toNat_of_nonneg (hnat i hi)
  have hliftBound (i : ℕ) (hi : i<n) : lifted p (z i)≤p+b := by
    have hh := (abs_le.mp (hzBound i hi)).2
    have he := hlift i hi
    omega
  have hmul (i : ℕ) (hi : i<n) : |(1 : ℤ)*μ (src+i)|≤lim.word := by
    simpa [hzRead i hi] using (hzBound i hi).trans hbWord
  have hsum (i : ℕ) (hi : i<n) : |(p : ℤ)+(1 : ℤ)*μ (src+i)|≤lim.word := by
    rw [hzRead i hi,one_mul,abs_of_nonneg (hnat i hi)]
    have hh := (abs_le.mp (hzBound i hi)).2
    omega
  apply Meets.of_body S.mainBody
  unfold body time
  light_call (LightReportingAffine.meets (d := depth+1) (src := src) (dst := dst) (n := n)
    (b := (p : ℤ)) (c := 1) S.liftBody hw (by omega) hspace (Or.inr (Or.inl hsrc)) hmul hsum)
    using LightReportingAffine.time,LightNaturalDot.reducedTime
    with a ν ⟨liftValues,keep⟩
  have coeffValues (i : ℕ) (hi : i<n) : ν (row+i)=(coeff i : ℤ) :=
    (keep _ (Or.inl (by omega))).trans (hcRead i hi)
  have liftedValues (i : ℕ) (hi : i<n) : ν (dst+i)=(lifted p (z i) : ℤ) := by
    rw [liftValues i hi,hzRead i hi,one_mul,hlift i hi]
  light_call (LightNaturalDot.reduced_meets (depth := depth+1)
    S.dotBody S.rawBody S.digitBody S.divideBody ν coeff (fun i => lifted p (z i)) hw (by omega)
    (by omega) hspace coeffValues liftedValues hcBound hliftBound hwDot)
    using LightReportingAffine.time,LightNaturalDot.reducedTime
    with r ξ ⟨hr,hξ⟩
  subst ξ
  exact ⟨hr,keep⟩

def program : Program := [body 1 2,LightReportingAffine.body,LightNaturalDot.reducedBody 3 4,
  LightNaturalDot.body,LightRadixDigit.body 5,LightSmallDivide.body]

def procs : Procs program 0 where
  lift := 1
  dot := 2
  rawDot := 3
  digit := 4
  divide := 5
  mainBody := rfl
  liftBody := rfl
  dotBody := rfl
  rawBody := rfl
  digitBody := rfl
  divideBody := rfl

end ThreeSum.LightSignedRowHash
