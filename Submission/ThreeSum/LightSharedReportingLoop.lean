import Submission.ThreeSum.SharedReportingBankData

/-! # Counting loops with the sum of the actual per-index budgets -/

namespace ThreeSum.LightSharedReportingLoop

open Light

theorem forSum {lim : Limits} {P : Program} {d : ℕ}
    {σ : State} {i : ℕ} {hi : Expr} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → State → Prop) (n : ℕ) (b : ℕ → ℕ)
    (start : I 0 {σ with loc := Function.update σ.loc i 0})
    (round : ∀ (j : ℕ) (σ : State), j < n → σ.loc i=(j : ℤ) → I j σ →
      Ends lim P d body σ (b j) (fun σ' =>
        σ'.loc i=(j : ℤ) ∧ I (j+1) {σ' with loc := Function.update σ'.loc i ((j : ℤ)+1)}))
    (done : ∀ (σ : State), σ.loc i=(n : ℤ) → I n σ → Q σ)
    (bound : ∀ (j : ℕ) (σ : State), j ≤ n → σ.loc i=(j : ℤ) → I j σ →
      hi.Safe lim σ ∧ hi.val σ=(n : ℤ))
    (hn : (n : ℤ) ≤ lim.word)
    (hT : (∑ j ∈ Finset.range n, (hi.cost+b j+7))+hi.cost+5 ≤ T) :
    Ends lim P d (Stmt.for i hi body) σ T Q := by
  have h0 : (0 : ℤ) ≤ lim.word := (Int.natCast_nonneg n).trans hn
  refine Ends.seq 2 ((∑ j ∈ Finset.range n, (hi.cost+b j+7))+hi.cost+3)
    (Ends.set (by simpa using h0) (by simp) ?_) (by omega)
  have H := Ends.while (lim := lim) (P := P) (d := d) (Q := Q)
    (σ := {σ with loc := Function.update σ.loc i 0})
    (c := v i <' hi) (s := body ;; .set i (v i +' k 1))
    (fun j σ => σ.loc i=(j : ℤ) ∧ I j σ) n (fun j => b j+4)
    (by exact ⟨by simp,by simpa using start⟩) ?round ?done
  · refine H.mono ?_ (fun _ h => h)
    simp only [Cond.cost,Expr.cost]
    have hsum : (∑ j ∈ Finset.range n, (1+hi.cost+1+1+(b j+4)))=
        ∑ j ∈ Finset.range n, (hi.cost+b j+7) := by
      apply Finset.sum_congr rfl
      intro j hj
      omega
    rw [hsum]
    omega
  case round =>
    rintro j σ hj ⟨hc,hI⟩
    obtain ⟨hs,hv⟩ := bound j σ hj.le hc hI
    refine ⟨⟨trivial,hs⟩,?_,Ends.seq (b j) 4 ((round j σ hj hc hI).mono le_rfl ?_) le_rfl⟩
    · change σ.loc i < hi.val σ
      rw [hc,hv]
      exact_mod_cast hj
    · rintro σ' ⟨hc',hI'⟩
      have hval : (v i +' k 1).val σ'=(j : ℤ)+1 := by simp [hc']
      have hj' : (j : ℤ)+1 ≤ n := by exact_mod_cast hj
      refine Ends.set ⟨trivial,?_,?_⟩ (by simp) ⟨?_,?_⟩
      · change ((1 : ℕ) : ℤ) ≤ lim.word
        push_cast
        omega
      · change |(v i +' k 1).val σ'| ≤ lim.word
        rw [hval,abs_of_nonneg (by omega)]
        omega
      · simp [hc']
      · rw [hval]
        exact hI'
  case done =>
    rintro σ ⟨hc,hI⟩
    obtain ⟨hs,hv⟩ := bound n σ le_rfl hc hI
    refine ⟨⟨trivial,hs⟩,?_,done σ hc hI⟩
    change ¬ σ.loc i < hi.val σ
    rw [hc,hv]
    exact lt_irrefl _

end ThreeSum.LightSharedReportingLoop
