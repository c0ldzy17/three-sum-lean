import Submission.ThreeSum.TernaryMomentSchedule
import Submission.ThreeSum.LightTernaryMomentAccumulate

/-! The exact partial-moment invariant of the actual signed channel driver. -/
namespace ThreeSum.TernaryMomentMatrixInvariant
open Light TernaryMomentSchedule

def Holds (reference : ℕ→ℤ) (matrix count terms boundary : ℕ)
    (done : List (ℕ×ℕ)) (score : ℕ→ℕ→ℕ→ℤ) (μ : ℕ→ℤ) : Prop :=
  (∀ k<terms, ∀ i<count, μ (matrix+k*count+i)=aggregate done score k i) ∧
  ∀ a<boundary, (a<matrix ∨ matrix+terms*count≤a) → μ a=reference a

theorem zero {reference μ : ℕ→ℤ} {matrix count terms boundary : ℕ}
    (score : ℕ→ℕ→ℕ→ℤ)
    (hzero : ∀ k<terms, ∀ i<count, μ (matrix+k*count+i)=0)
    (hkeep : SameOutside reference μ matrix (terms*count)) :
    Holds reference matrix count terms boundary [] score μ := by
  refine ⟨?_,?_⟩
  · simpa only [aggregate_nil] using hzero
  · intro a ha haway
    exact hkeep a haway

theorem advance {reference μ ν : ℕ→ℤ} {matrix count terms boundary k j : ℕ}
    (done : List (ℕ×ℕ)) (score : ℕ→ℕ→ℕ→ℤ)
    (hk : k<terms) (hwindow : matrix+terms*count≤boundary)
    (hI : Holds reference matrix count terms boundary done score μ)
    (hrow : ∀ i<count, ν (matrix+k*count+i)=aggregate done score k i+score k j i)
    (hkeep : ∀ a<boundary, (a<matrix+k*count ∨ matrix+k*count+count≤a) → ν a=μ a) :
    Holds reference matrix count terms boundary (done++[(k,j)]) score ν := by
  constructor
  · intro l hl i hi
    have hm := Nat.mul_le_mul_right count (show l+1≤terms by omega)
    simp only [Nat.add_mul,one_mul] at hm
    have hbefore : matrix+l*count+i<boundary := by omega
    by_cases hkl : k=l
    · subst l
      simpa only [aggregate_append,aggregate_cons,aggregate_nil,ite_true,add_zero]
        using hrow i hi
    · have haway : matrix+l*count+i<matrix+k*count ∨
          matrix+k*count+count≤matrix+l*count+i := by
        by_cases hlk : l<k
        · left
          have hh := Nat.mul_le_mul_right count (show l+1≤k by omega)
          simp only [Nat.add_mul,one_mul] at hh
          omega
        · right
          have hh := Nat.mul_le_mul_right count (show k+1≤l by omega)
          simp only [Nat.add_mul,one_mul] at hh
          omega
      rw [hkeep _ hbefore haway,hI.1 l hl i hi]
      simp only [aggregate_append,aggregate_cons,aggregate_nil,hkl,ite_false,add_zero]
  · intro a ha haway
    have hm := Nat.mul_le_mul_right count (show k+1≤terms by omega)
    simp only [Nat.add_mul,one_mul] at hm
    have hr : a<matrix+k*count ∨ matrix+k*count+count≤a := by rcases haway with h|h <;> omega
    exact (hkeep a ha hr).trans (hI.2 a ha haway)

theorem aggregate_abs_le (done : List (ℕ×ℕ)) (score : ℕ→ℕ→ℕ→ℤ)
    (k i V : ℕ) (hscore : ∀ c∈done, |score c.1 c.2 i|≤(V : ℤ)) :
    |aggregate done score k i|≤(done.length : ℤ)*V := by
  induction done with
  | nil => simp
  | cons c cs ih =>
    have ht := ih (fun d hd => hscore d (by simp [hd]))
    have hc := hscore c (by simp)
    rw [aggregate_cons]
    have hs : |(if c.1=k then score c.1 c.2 i else 0 : ℤ)|≤(V : ℤ) := by
      split_ifs <;> first | exact hc | simp
    have hb := (abs_add_le _ _).trans (add_le_add hs ht)
    simpa only [List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm] using hb

theorem complete {reference μ : ℕ→ℤ} {matrix count terms boundary : ℕ}
    (score : ℕ→ℕ→ℕ→ℤ)
    (hI : Holds reference matrix count terms boundary (channels terms) score μ) :
    ∀ k<terms, ∀ i<count,
      μ (matrix+k*count+i)=∑ j∈Finset.range (k+1), score k j i := by
  intro k hk i hi
  rw [hI.1 k hk i hi,channel_rows,if_pos hk]

end ThreeSum.TernaryMomentMatrixInvariant
