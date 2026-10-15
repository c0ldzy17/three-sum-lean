import Submission.ThreeSum.LightTernarySignedRow

/-! Executed carry correction of an original requester digit row. -/
namespace ThreeSum.LightTernaryCarryApply
open Light TernarySignedDigits TernarySignedReduction TernarySignedModes

set_option maxHeartbeats 1800000
set_option maxRecDepth 7000

/-- The carry array is [c_J=0,c_(J-1),...,c_0]. Two linear passes
produce digit(A+U) - base*c_(j+1) + c_j in the actual row cells. -/
def body (pLinear : ℕ) : Stmt :=
  .call pLinear [v 0,v 1,v 0,v 2,k 0 -' v 3] 4 ;;
  .call pLinear [v 0,v 1 +' k 1,v 0,v 2,k 1] 0

def time (J : ℕ) : ℕ := 2*LightArray.linearTime J+60

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain pLinear : ℕ}
    (hmain : P[pMain]?=some (body pLinear))
    (hlinear : P[pLinear]?=some LightArray.linearBody)
    {μ : ℕ→ℤ} {U radix J dst carry : ℕ} (a : ℤ) (c : CarryWord J)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d<lim.depth) (hb : 1<radix)
    (hsep : carry+J+1≤dst ∨ dst+J+2≤carry)
    (hspace : max (carry+J+1) (dst+J+2)≤lim.space)
    (hword : (4*(radix : ℤ)+8)≤lim.word)
    (hA : ∀ k<J, μ (dst+k)=(digit radix (shiftOne U a) (J-1-k) : ℤ))
    (hcarry : ∀ k≤J, μ (carry+k)=carryAt c (J-k))
    (ht0 : μ (dst+J)=1) (ht1 : μ (dst+J+1)=1) :
    Meets lim P pMain d [dst,carry,J,radix] μ (time J)
      (fun _ ν => LightTernarySignedRow.Row ν dst J (requesterRaw U radix J a c) ∧
        Kept μ ν dst) := by
  have hB : (radix : ℤ)≤lim.word := by omega
  have h1 : (1 : ℤ)≤lim.word := by omega
  have hD : dst+J≤lim.space := by omega
  have hC : carry+J≤lim.space := by omega
  have hsrc : LightArray.SourceSafe carry dst J := by
    right
    rcases hsep with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have hmul1 : ∀ k<J, |-(radix : ℤ)*μ (carry+k)|≤lim.word := by
    intro k hk
    rw [hcarry k hk.le]
    have hc := carryAt_bounds c (J-k)
    have hm : (radix : ℤ)*carryAt c (J-k)≤radix := by nlinarith
    have hm0 : (0 : ℤ)≤(radix : ℤ)*carryAt c (J-k) :=
      mul_nonneg (Int.natCast_nonneg _) hc.1
    rw [neg_mul,abs_neg,abs_of_nonneg hm0]
    exact hm.trans hB
  have hsum1 : ∀ k<J, |μ (dst+k)+ -(radix : ℤ)*μ (carry+k)|≤lim.word := by
    intro k hk
    rw [hA k hk,hcarry k hk.le]
    have hc := carryAt_bounds c (J-k)
    have hd : (digit radix (shiftOne U a) (J-1-k) : ℤ)<radix := by
      exact_mod_cast digit_lt (by omega : 0<radix) _ _
    have hd0 : (0 : ℤ)≤digit radix (shiftOne U a) (J-1-k) := by positivity
    apply (abs_le.mpr ⟨by nlinarith,by nlinarith⟩).trans hB
  apply Meets.of_body hmain
  unfold body time
  light_call (LightArray.linear_meets (d := d+1) (μ := μ)
    (srcA := dst) (srcB := carry) (dst := dst) (n := J) (c := -(radix : ℤ))
    hlinear hw hD hC hD (Or.inl rfl) hsrc hmul1 hsum1)
    using LightArray.linearTime with r ν ⟨hfirst,hkeep1⟩
  have hcRead : ∀ k≤J, ν (carry+k)=carryAt c (J-k) := by
    intro k hk
    have hout : carry+k<dst ∨ dst+J≤carry+k := by
      rcases hsep with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    rw [hkeep1 _ hout,hcarry k hk]
  have hfirst' : ∀ k<J, ν (dst+k)=
      (digit radix (shiftOne U a) (J-1-k) : ℤ)-
        (radix : ℤ)*carryAt c (J-k) := by
    intro k hk
    rw [hfirst k hk,hA k hk,hcarry k hk.le]
    ring
  have hmul2 : ∀ k<J, |(1 : ℤ)*ν (carry+1+k)|≤lim.word := by
    intro k hk
    have hread : ν (carry+1+k)=carryAt c (J-(k+1)) := by
      rw [show carry+1+k=carry+(k+1) by omega,hcRead _ (by omega)]
    rw [one_mul,hread,abs_of_nonneg (carryAt_bounds c _).1]
    exact (carryAt_bounds c _).2.trans h1
  have hsum2 : ∀ k<J, |ν (dst+k)+(1 : ℤ)*ν (carry+1+k)|≤lim.word := by
    intro k hk
    rw [hfirst' k hk,one_mul,show carry+1+k=carry+(k+1) by omega,hcRead _ (by omega)]
    have hc0 := carryAt_bounds c (J-k)
    have hc1 := carryAt_bounds c (J-(k+1))
    have hd : (digit radix (shiftOne U a) (J-1-k) : ℤ)<radix := by
      exact_mod_cast digit_lt (by omega : 0<radix) _ _
    have hd0 : (0 : ℤ)≤digit radix (shiftOne U a) (J-1-k) := by positivity
    have hd1 : (digit radix (shiftOne U a) (J-1-k) : ℤ)≤(radix : ℤ)-1 := by omega
    apply (abs_le.mpr ⟨by nlinarith,by nlinarith⟩).trans hB
  light_call (LightArray.linear_meets (d := d+1) (μ := ν)
    (srcA := dst) (srcB := carry+1) (dst := dst) (n := J) (c := (1 : ℤ))
    hlinear hw hD (by omega) hD (Or.inl rfl)
    (by
      right
      rcases hsep with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)) hmul2 hsum2)
    using LightArray.linearTime with r' ξ ⟨hsecond,hkeep2⟩
  change LightTernarySignedRow.Row ξ dst J (requesterRaw U radix J a c) ∧ Kept μ ξ dst
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · intro j
    have hk : J-1-j.val<J := by omega
    have he : dst+J-1-j.val=dst+(J-1-j.val) := by omega
    rw [he,hsecond _ hk,hfirst' _ hk,one_mul,
      show carry+1+(J-1-j.val)=carry+(J-j.val) by omega,hcRead _ (by omega)]
    simp only [requesterRaw]
    rw [show J-1-(J-1-j.val)=j.val by omega,
      show J-(J-1-j.val)=j.val+1 by omega,
      show J-(J-j.val)=j.val by omega]
    ring
  · simp only [requesterRaw]
    rw [hkeep2 _ (Or.inr (by omega)),hkeep1 _ (Or.inr (by omega)),ht0]
  · simp only [requesterRaw]
    rw [hkeep2 _ (Or.inr (by omega)),hkeep1 _ (Or.inr (by omega)),ht1]
  · intro i hi
    rw [hkeep2 _ (Or.inl hi),hkeep1 _ (Or.inl hi)]

def program : Program := [body 1,LightArray.linearBody]

end ThreeSum.LightTernaryCarryApply
