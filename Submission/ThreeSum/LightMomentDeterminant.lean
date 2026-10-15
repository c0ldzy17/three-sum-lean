import Submission.ThreeSum.LightFixedArithmetic
import Submission.ThreeSum.FiniteMomentZeroDetector

namespace ThreeSum.LightMomentDeterminant
open Light Matrix ThreeSum.LightFixedArithmetic
open scoped BigOperators

noncomputable def sumCircuits (es : List Circuit) : Circuit := es.foldr Circuit.add (.literal 0)
noncomputable def prodCircuits (es : List Circuit) : Circuit := es.foldr Circuit.mul (.literal 1)

@[simp] theorem eval_sumCircuits (es : List Circuit) (x : ℕ → ℤ) :
    (sumCircuits es).eval x=(es.map (fun e => e.eval x)).sum := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change e.eval x+(sumCircuits es).eval x=_
    simpa only [List.map_cons,List.sum_cons,ih]

@[simp] theorem eval_prodCircuits (es : List Circuit) (x : ℕ → ℤ) :
    (prodCircuits es).eval x=(es.map (fun e => e.eval x)).prod := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change e.eval x*(prodCircuits es).eval x=_
    simpa only [List.map_cons,List.prod_cons,ih]

noncomputable def determinant (d : ℕ) (entry : Fin d → Fin d → Circuit) : Circuit :=
  sumCircuits ((Finset.univ : Finset (Equiv.Perm (Fin d))).toList.map (fun σ =>
    .mul (.literal (Equiv.Perm.sign σ : ℤ))
      (prodCircuits ((Finset.univ : Finset (Fin d)).toList.map (fun i => entry (σ i) i)))))

theorem eval_determinant (d : ℕ) (entry : Fin d → Fin d → Circuit) (x : ℕ → ℤ) :
    (determinant d entry).eval x=Matrix.det (Matrix.of (fun i j => (entry i j).eval x)) := by
  classical
  simp only [determinant,eval_sumCircuits,List.map_map,Circuit.eval,eval_prodCircuits,
    Function.comp_apply,Finset.prod_map_toList,Finset.sum_map_toList,Matrix.det_apply',Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro σ hσ
  simp [Function.comp_apply,Circuit.eval,eval_prodCircuits,List.map_map]

noncomputable def leading (d : ℕ) : Circuit :=
  determinant d (fun i j => .atom (i.val+j.val+1))

noncomputable def modified (d : ℕ) : Circuit :=
  determinant d (fun i j =>
    .add (.sub (.atom (i.val+j.val+3))
      (.mul (.mul (.literal 2) (.atom 0)) (.atom (i.val+j.val+2))))
      (.mul (.mul (.atom 0) (.atom 0)) (.atom (i.val+j.val+1))))

theorem eval_leading (d : ℕ) (x : ℕ → ℤ) :
    (leading d).eval x=Matrix.det (Matrix.of (fun (i j : Fin d) => x (i.val+j.val+1))) := by
  rw [leading,eval_determinant]
  rfl

theorem eval_modified (d : ℕ) (x : ℕ → ℤ) :
    (modified d).eval x=Matrix.det (Matrix.of (fun (i j : Fin d) =>
      x (i.val+j.val+3)-2*x 0*x (i.val+j.val+2)+(x 0)^2*x (i.val+j.val+1))) := by
  rw [modified,eval_determinant]
  congr 1
  funext i j
  simp only [Circuit.eval,pow_two]

/-- The fixed sequence of conditional tests actually evaluates every necessary
leading determinant; no rank or determinant operation is added to the language. -/
noncomputable def body (atoms : ℕ → Expr) : ℕ → Stmt
  | 0 => .set 0 (k 0)
  | h+1 => .ite (.eq ((leading (h+1)).compile atoms) (k 0)) (body atoms h)
      (.ite (.eq ((modified (h+1)).compile atoms) (k 0))
        (.set 0 (k 1)) (.set 0 (k 0)))

noncomputable def time (atoms : ℕ → Expr) : ℕ → ℕ
  | 0 => 2
  | h+1 => ((leading (h+1)).compile atoms).cost+3+time atoms h+
      ((modified (h+1)).compile atoms).cost+7

noncomputable def wordBound (U : ℤ) : ℕ → ℤ
  | 0 => 1
  | h+1 => max (wordBound U h) (max ((leading (h+1)).bound U) ((modified (h+1)).bound U))

theorem wordBound_one (U : ℤ) (h : ℕ) : 1≤wordBound U h := by
  induction h with
  | zero => exact le_rfl
  | succ h ih => exact ih.trans (le_max_left _ _)

noncomputable def wordCoefficient : ℕ → ℤ
  | 0 => 1
  | h+1 => wordCoefficient h+(leading (h+1)).coefficient+(modified (h+1)).coefficient

noncomputable def wordDegree : ℕ → ℕ
  | 0 => 0
  | h+1 => wordDegree h+(leading (h+1)).degree+(modified (h+1)).degree

theorem wordCoefficient_pos (h : ℕ) : 1≤wordCoefficient h := by
  induction h with
  | zero => exact le_rfl
  | succ h ih =>
    have := (leading (h+1)).coefficient_pos
    have := (modified (h+1)).coefficient_pos
    simp only [wordCoefficient]
    omega

theorem wordBound_polynomial (h : ℕ) {U : ℤ} (hU : 0≤U) :
    wordBound U h≤wordCoefficient h*(U+1)^wordDegree h := by
  have hbase : 1≤U+1 := by omega
  induction h with
  | zero => simp [wordBound,wordCoefficient,wordDegree]
  | succ h ih =>
    have hco := wordCoefficient_pos h
    have hcl := (leading (h+1)).coefficient_pos
    have hcm := (modified (h+1)).coefficient_pos
    have hlo := (leading (h+1)).bound_polynomial hU
    have hmo := (modified (h+1)).bound_polynomial hU
    have hpold : (U+1)^wordDegree h≤(U+1)^wordDegree (h+1) :=
      pow_le_pow_right₀ hbase (by simp only [wordDegree]; omega)
    have hplead : (U+1)^(leading (h+1)).degree≤(U+1)^wordDegree (h+1) :=
      pow_le_pow_right₀ hbase (by simp only [wordDegree]; omega)
    have hpmod : (U+1)^(modified (h+1)).degree≤(U+1)^wordDegree (h+1) :=
      pow_le_pow_right₀ hbase (by simp only [wordDegree]; omega)
    have hpow : 0≤(U+1)^wordDegree (h+1) := le_trans (by decide : (0 : ℤ)≤1) (one_le_pow₀ hbase)
    change max (wordBound U h) (max ((leading (h+1)).bound U) ((modified (h+1)).bound U))≤_
    apply max_le
    · exact ih.trans ((mul_le_mul_of_nonneg_left hpold (by omega)).trans
        (mul_le_mul_of_nonneg_right (by simp [wordCoefficient]; omega) hpow))
    · apply max_le
      · exact hlo.trans ((mul_le_mul_of_nonneg_left hplead (by omega)).trans
          (mul_le_mul_of_nonneg_right (by simp [wordCoefficient]; omega) hpow))
      · exact hmo.trans ((mul_le_mul_of_nonneg_left hpmod (by omega)).trans
          (mul_le_mul_of_nonneg_right (by simp [wordCoefficient]; omega) hpow))

open FiniteMomentZeroDetector in
theorem body_ends (h : ℕ) {t : ℕ} (v w : Fin t → ℤ) (a : ℤ)
    (hv : Function.Injective v) (hw : ∀ s, w s≠0) (hth : t≤h)
    (atoms : ℕ → Expr) (σ : State) {lim : Limits} {P : Program} {d : ℕ}
    (U : ℤ) (hU : 0≤U)
    (hs : ∀ i, (atoms i).Safe lim σ)
    (hx : ∀ i, |(atoms i).val σ|≤U)
    (hword : wordBound U h≤lim.word)
    (hlead : ∀ k≤h, (leading k).eval (fun i => (atoms i).val σ)=(hankel v w k).det)
    (hmod : ∀ k≤h, (modified k).eval (fun i => (atoms i).val σ)=(modifiedHankel v w a k).det) :
    Ends lim P d (body atoms h) σ (time atoms h)
      (fun τ => τ.loc 0=(if ∃ s, v s=a then 1 else 0 : ℤ) ∧ τ.mem=σ.mem) := by
  classical
  induction h with
  | zero =>
    have ht : t=0 := by omega
    have hn : ¬∃ s, v s=a := by
      rintro ⟨s,hs⟩
      have := s.isLt
      omega
    unfold body time
    apply Ends.set (by change (0 : ℤ)≤lim.word; exact (by have := wordBound_one U 0; omega)) le_rfl
    simp [hn]
  | succ h ih =>
    have hwold : wordBound U h≤lim.word := (le_max_left _ _).trans hword
    have hwlead : (leading (h+1)).bound U≤lim.word :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hword)
    have hwmod : (modified (h+1)).bound U≤lim.word :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hword)
    have hslead := (leading (h+1)).compile_safe atoms σ hU hs hx hwlead
    have hsmod := (modified (h+1)).compile_safe atoms σ hU hs hx hwmod
    have hnonneg : 1≤lim.word := (wordBound_one U (h+1)).trans hword
    unfold body time
    refine Ends.iteLast ?_ ?_ ⟨hslead,by change (0 : ℤ)≤lim.word; omega⟩ (by simp [Cond.cost]; omega)
    · intro hz
      have hzero : (hankel v w (h+1)).det=0 := by
        change ((leading (h+1)).compile atoms).val σ=0 at hz
        rwa [Circuit.compile_val,hlead (h+1) (by omega)] at hz
      have hsmall : t≤h := by
        by_contra hn
        have ht : t=h+1 := by omega
        have hne := det_hankel_support_ne_zero v w hv hw
        rw [←ht] at hzero
        exact hne hzero
      exact (ih hsmall hwold (fun k hk => hlead k (by omega))
        (fun k hk => hmod k (by omega))).mono (by simp [Cond.cost]; omega) (fun τ hτ => hτ)
    · intro hnz
      have hnonzero : (hankel v w (h+1)).det≠0 := by
        change ¬((leading (h+1)).compile atoms).val σ=0 at hnz
        rwa [Circuit.compile_val,hlead (h+1) (by omega)] at hnz
      have ht : h+1=t := by
        by_contra hn
        have hlt : t<h+1 := by omega
        exact hnonzero (det_hankel_eq_zero_of_support_lt v w hlt)
      have hziff : ((modified (h+1)).compile atoms).val σ=0 ↔ ∃ s, v s=a := by
        rw [Circuit.compile_val,hmod (h+1) (by omega),ht]
        exact modified_det_zero_iff v w a hv hw
      refine Ends.iteLast ?_ ?_ ⟨hsmod,by change (0 : ℤ)≤lim.word; omega⟩ (by simp [Cond.cost]; omega)
      · intro hz
        have he : ∃ s, v s=a := hziff.mp hz
        apply Ends.set (by change (1 : ℤ)≤lim.word; omega) (by simp [Cond.cost,Expr.cost]; omega)
        simp [he]
      · intro hn
        have he : ¬∃ s, v s=a := fun he => hn (hziff.mpr he)
        apply Ends.set (by change (0 : ℤ)≤lim.word; omega) (by simp [Cond.cost,Expr.cost]; omega)
        simp [he]

end ThreeSum.LightMomentDeterminant
