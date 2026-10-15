import Submission.ThreeSum.TernaryParameters
import Submission.ThreeSum.TernaryBank
import Submission.ThreeSum.TernaryLocalParameters

/-! Literal compressed bank and query dimensions in the exact schedule. -/
noncomputable section
namespace ThreeSum.TernaryDimensionBounds
open TernaryJointType TernaryLocalParameters TernaryBank TernaryParameters

def bankCut (m j : ℕ) : ℕ := 20384999*j*m
def queryDeficit (m j : ℕ) : ℕ := 1344845*j*m+1
def bankSize (m j : ℕ) : ℕ := (bank (fixedLength (j*m)) (bankCut m j)).card

theorem bank_pos (N T : ℕ) : 0 < (bank N T).card := by
  classical
  apply Finset.card_pos.mpr
  refine ⟨fun _ => 0, ?_⟩
  apply mem_bank.mpr
  simp [rank]

theorem near_pos {N : ℕ} (Q : TritWord N) (D : ℕ) : 0 < (nearWords Q D).card := by
  classical
  apply Finset.card_pos.mpr
  refine ⟨Q, ?_⟩
  apply mem_nearWords.mpr
  exact ⟨fun _ => le_rfl, by simp [TernaryBank.deficit]⟩

theorem rank_eq_counts {N : ℕ} (Q : TritWord N) :
    rank Q = digitCount Q 1+2*digitCount Q 2 := by
  have hlocal (i : Fin N) : (Q i).val = (if Q i=1 then 1 else 0)+
      2*(if Q i=2 then 1 else 0 : ℕ) := by generalize Q i=d; fin_cases d <;> decide
  simp_rw [rank, hlocal]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rfl

theorem output_rank {m j : ℕ} {Q : TritWord (fixedLength (j*m))}
    (hQ : HasType Q (fixedPi (j*m))) : rank Q = 21729844*j*m := by
  rw [rank_eq_counts, hQ 1, hQ 2]
  simp [fixedPi]
  ring

theorem query_boundary {m j : ℕ} {Q : TritWord (fixedLength (j*m))}
    (hQ : HasType Q (fixedPi (j*m))) : rank Q+1-bankCut m j=queryDeficit m j := by
  rw [output_rank hQ]
  unfold bankCut queryDeficit
  ring_nf
  omega

theorem endpoint_in_bank {m j : ℕ} {A : TritWord (fixedLength (j*m))}
    (hA : HasType A (fixedAlpha (j*m))) : A ∈ bank (fixedLength (j*m)) (bankCut m j) := by
  apply mem_bank.mpr
  rw [rank_eq_counts,hA 1,hA 2]
  simp [fixedAlpha,bankCut]
  ring_nf
  omega

theorem bank_log_bound (m j : ℕ) :
    Real.log (bankSize m j : ℝ) ≤ (fixedLength (j*m) : ℝ)*Real.log 2*bankEntropy := by
  have hy := gibbs_parameters
  have hc : 0 < (bankSize m j : ℝ) := by exact_mod_cast bank_pos (fixedLength (j*m)) (bankCut m j)
  have hg := bank_card_gibbs (fixedLength (j*m)) (bankCut m j) y hy.1.le hy.2.1.le
  have hh := Real.log_le_log (mul_pos hc (pow_pos hy.1 _)) hg
  rw [Real.log_mul hc.ne' (pow_pos hy.1 _).ne', Real.log_pow, Real.log_pow,
    ← generating_polynomials.1] at hh
  change Real.log (bankSize m j : ℝ)+(bankCut m j : ℝ)*Real.log y ≤
    (fixedLength (j*m) : ℝ)*Real.log bankArg at hh
  have he : (fixedLength (j*m) : ℝ)*Real.log 2*bankEntropy =
      (fixedLength (j*m) : ℝ)*Real.log bankArg-(bankCut m j : ℝ)*Real.log y := by
    unfold bankEntropy mean pi1 pi2 TernaryParameters.deficit bankCut fixedLength
    push_cast
    field_simp
    ring
  rw [he]
  linarith

theorem query_log_bound {m j : ℕ} (Q : TritWord (fixedLength (j*m)))
    (hQ : HasType Q (fixedPi (j*m))) :
    Real.log ((nearWords Q (queryDeficit m j)).card : ℝ) ≤
      (fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy-Real.log z := by
  have hz := gibbs_parameters
  have hc : 0 < ((nearWords Q (queryDeficit m j)).card : ℝ) := by exact_mod_cast near_pos Q _
  have hg := nearWords_card_gibbs_counts Q (queryDeficit m j) z hz.2.2.1.le hz.2.2.2.le
  rw [hQ 1,hQ 2] at hg
  have hh := Real.log_le_log (mul_pos hc (pow_pos hz.2.2.1 _)) hg
  have ha1 : 0 < 1+z := by linarith [hz.2.2.1]
  have ha2 : 0 < 1+z+z^2 := by nlinarith [sq_nonneg z]
  rw [Real.log_mul hc.ne' (pow_pos hz.2.2.1 _).ne', Real.log_pow,
    Real.log_mul (pow_pos ha1 _).ne' (pow_pos ha2 _).ne',Real.log_pow,Real.log_pow,
    ← generating_polynomials.2.2,← generating_polynomials.2.1] at hh
  have he : (fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy-Real.log z =
      (fixedPi (j*m) 1 : ℝ)*Real.log queryArg1+(fixedPi (j*m) 2 : ℝ)*Real.log queryArg2-
        (queryDeficit m j : ℝ)*Real.log z := by
    unfold queryEntropy pi1 pi2 TernaryParameters.deficit queryDeficit fixedLength fixedPi
    norm_num
    push_cast
    field_simp
    ring
  rw [he]
  linarith

end ThreeSum.TernaryDimensionBounds
