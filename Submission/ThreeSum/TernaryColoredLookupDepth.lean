import Submission.ThreeSum.TernaryColoredPostABI

namespace ThreeSum.TernaryColoredLookupDepth
open Light LightTernaryColoredSolver
set_option maxHeartbeats 1000000

theorem compute {lim : Limits} {P : Program} {d header len r : ℕ}
    (loc μ : ℕ→ℤ) (hloc : loc 5=(header : ℤ))
    (hread : μ (header+15)=(r : ℤ)) (hspace : header+16≤lim.space)
    (hw : (lim.space : ℤ)≤lim.word)
    (hword : ((len+2*len*r+16 : ℕ) : ℤ)≤lim.word) :
    Ends lim P d (.set 13 (k len *' H 15) ;; .set 14 (k 2 *' v 13)) ⟨loc,μ⟩ 11
      (fun σ=>σ.loc 13=(len*r : ℕ) ∧ σ.loc 14=(2*(len*r) : ℕ) ∧
        (∀i,i≠13→i≠14→σ.loc i=loc i) ∧ σ.mem=μ) := by
  have hprod : ((len*r : ℕ) : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (show len*r≤len+2*len*r+16 by rw [Nat.mul_assoc]; omega)).trans hword
  have hdouble : ((2*(len*r) : ℕ) : ℤ)≤lim.word := by
    simpa only [Nat.mul_assoc] using (Int.ofNat_le.mpr (show 2*len*r≤len+2*len*r+16 by omega)).trans hword
  have he : (k len *' H 15).Gives lim ⟨loc,μ⟩ (len*r : ℕ) := by
    constructor
    · simp only [H,k,M,v,Expr.Safe,Expr.val,Limits.Addr,Op.eval,hloc,
        ←Int.natCast_add,Int.toNat_natCast,hread,←Int.natCast_mul]
      have hptr : ((header+15 : ℕ) : ℤ)<(lim.space : ℤ) := by exact_mod_cast (show header+15<lim.space by omega)
      simp only [abs_of_nonneg (Int.natCast_nonneg _)]
      repeat' apply And.intro
      all_goals first | trivial | omega
    · change (len : ℤ)*μ ((loc 5+15).toNat)=_
      rw [hloc,show ((header : ℤ)+15).toNat=header+15 by omega,hread]
      exact (Nat.cast_mul len r).symm
  apply Ends.setValThen (len*r : ℕ) (he := he) (hT := by simp [H,Expr.cost,k,M,v])
  apply Ends.setLast
  · refine ⟨?_,?_,?_,rfl⟩
    · simp
    · simp [Nat.cast_mul]
    · intro i h13 h14
      simp [Function.update_of_ne h13,Function.update_of_ne h14]
  · change (2 : ℤ)≤lim.word ∧ True ∧ |(2 : ℤ)*(Function.update loc 13 (len*r : ℕ)) 13|≤lim.word
    simp only [Function.update_self,true_and]
    change (2 : ℤ)≤lim.word ∧ |((2*(len*r) : ℕ) : ℤ)|≤lim.word
    rw [abs_of_nonneg (Int.natCast_nonneg _)]
    exact ⟨by omega,hdouble⟩
  · simp [H,M,Expr.cost,k,v]

end ThreeSum.TernaryColoredLookupDepth
