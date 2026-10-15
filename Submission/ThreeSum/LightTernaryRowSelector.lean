import Submission.ThreeSum.LightArray
import Submission.ThreeSum.TernaryPairedSelector

/-! An actual linear scan chooses a row satisfying all three normalized
contraction inequalities. Tests use integer cross multiplication only.
The result is an ordinal plus one, with zero denoting no accepted row. -/

namespace ThreeSum.LightTernaryRowSelector

open Light

def Good (flag f₀ f₁ f₂ : ℕ → ℤ) (d₀ d₁ d₂ t₀ t₁ t₂ : ℕ) (i : ℕ) : Prop :=
  flag i ≠ 0 ∧ f₀ i*d₀ ≤ t₀ ∧ f₁ i*d₁ ≤ t₁ ∧ f₂ i*d₂ ≤ t₂

instance (flag f₀ f₁ f₂ : ℕ → ℤ) (d₀ d₁ d₂ t₀ t₁ t₂ i : ℕ) :
    Decidable (Good flag f₀ f₁ f₂ d₀ d₁ d₂ t₀ t₁ t₂ i) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def pick (good : ℕ → Prop) [DecidablePred good] : ℕ → ℕ
  | 0 => 0
  | n+1 => if good n then n+1 else pick good n

theorem pick_le (good : ℕ → Prop) [DecidablePred good] (n : ℕ) : pick good n ≤ n := by
  induction n with
  | zero => simp [pick]
  | succ n ih => simp only [pick]; split_ifs <;> omega

theorem pick_pos_iff (good : ℕ → Prop) [DecidablePred good] (n : ℕ) :
    0 < pick good n ↔ ∃ i < n, good i := by
  induction n with
  | zero => simp [pick]
  | succ n ih =>
    rw [pick]
    split_ifs with hn
    · constructor
      · intro h; exact ⟨n,by omega,hn⟩
      · intro h; omega
    · rw [ih]
      constructor
      · rintro ⟨i,hi,hg⟩; exact ⟨i,by omega,hg⟩
      · rintro ⟨i,hi,hg⟩
        refine ⟨i, ?_,hg⟩
        by_contra h
        have : i=n := by omega
        exact hn (this ▸ hg)

theorem pick_good (good : ℕ → Prop) [DecidablePred good] (n : ℕ) (h : 0 < pick good n) :
    good (pick good n-1) := by
  induction n with
  | zero => simp [pick] at h
  | succ n ih =>
    rw [pick] at h ⊢
    split_ifs at h ⊢ with hn
    · simpa using hn
    · exact ih h

def scanBody : Stmt :=
  .ite (M (v 0 +' v 11) =' k 0) .skip (
    .ite (v 8 <' M (v 1 +' v 11) *' v 5) .skip (
      .ite (v 9 <' M (v 2 +' v 11) *' v 6) .skip (
        .ite (v 10 <' M (v 3 +' v 11) *' v 7) .skip (.set 12 (v 11 +' k 1)))))

def body : Stmt := .set 12 (k 0) ;; .for 11 (v 4) scanBody ;; .set 0 (v 12)

def time (n : ℕ) : ℕ := 160*n+40

def word (n U d₀ d₁ d₂ t₀ t₁ t₂ : ℕ) : ℕ :=
  U*(d₀+d₁+d₂+1)+t₀+t₁+t₂+d₀+d₁+d₂+n+2

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {p flagBase a₀ a₁ a₂ n U d₀ d₁ d₂ t₀ t₁ t₂ : ℕ}
    (hprog : P[p]? = some body) (μ : ℕ → ℤ)
    (flag f₀ f₁ f₂ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hflagSpace : flagBase+n ≤ lim.space) (h₀ : a₀+n ≤ lim.space)
    (h₁ : a₁+n ≤ lim.space) (h₂ : a₂+n ≤ lim.space)
    (hflag : ∀ i<n, μ (flagBase+i)=flag i ∧ |flag i|≤1)
    (hread₀ : ∀ i<n, μ (a₀+i)=f₀ i ∧ |f₀ i|≤U)
    (hread₁ : ∀ i<n, μ (a₁+i)=f₁ i ∧ |f₁ i|≤U)
    (hread₂ : ∀ i<n, μ (a₂+i)=f₂ i ∧ |f₂ i|≤U)
    (hword : (word n U d₀ d₁ d₂ t₀ t₁ t₂ : ℤ) ≤ lim.word) :
    Meets lim P p d [flagBase,a₀,a₁,a₂,n,d₀,d₁,d₂,t₀,t₁,t₂] μ (time n)
      (fun r μ' => r=(pick (Good flag f₀ f₁ f₂ d₀ d₁ d₂ t₀ t₁ t₂) n : ℤ) ∧ μ'=μ) := by
  let good := Good flag f₀ f₁ f₂ d₀ d₁ d₂ t₀ t₁ t₂
  have hbudget (x : ℕ) (hx : x ≤ word n U d₀ d₁ d₂ t₀ t₁ t₂) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hden₀ := hbudget d₀ (by unfold word; omega)
  have hden₁ := hbudget d₁ (by unfold word; omega)
  have hden₂ := hbudget d₂ (by unfold word; omega)
  have htar₀ := hbudget t₀ (by unfold word; omega)
  have htar₁ := hbudget t₁ (by unfold word; omega)
  have htar₂ := hbudget t₂ (by unfold word; omega)
  have hone := hbudget 1 (by unfold word; omega)
  have hU := hbudget U (by unfold word; nlinarith)
  have hmul₀ := hbudget (U*d₀) (by unfold word; nlinarith)
  have hmul₁ := hbudget (U*d₁) (by unfold word; nlinarith)
  have hmul₂ := hbudget (U*d₂) (by unfold word; nlinarith)
  apply Meets.of_body hprog
  unfold body time
  light_set 0
  refine Ends.pieceThen (Ends.for (T := 140*n+10)
    (Q := fun σ => σ=⟨frame [flagBase,a₀,a₁,a₂,n,d₀,d₁,d₂,t₀,t₁,t₂,n,pick good n],μ⟩)
    (fun j σ => σ=⟨frame [flagBase,a₀,a₁,a₂,n,d₀,d₁,d₂,t₀,t₁,t₂,j,pick good j],μ⟩)
    n 130 ?_ ?_ ?_ ?_ (hT := by light_time)) ?_
  · simp [pick,update_frame_setLocal,frame_append_zeros]
  · rintro j _ hj _ rfl
    have hpick := pick_le good j
    have hflagj := hflag j hj
    have hr₀ := hread₀ j hj
    have hr₁ := hread₁ j hj
    have hr₂ := hread₂ j hj
    have hb₀ : |f₀ j*(d₀ : ℤ)|≤lim.word := by
      rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _)]
      exact (mul_le_mul_of_nonneg_right hr₀.2 (Int.natCast_nonneg _)).trans (by exact_mod_cast hmul₀)
    have hb₁ : |f₁ j*(d₁ : ℤ)|≤lim.word := by
      rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _)]
      exact (mul_le_mul_of_nonneg_right hr₁.2 (Int.natCast_nonneg _)).trans (by exact_mod_cast hmul₁)
    have hb₂ : |f₂ j*(d₂ : ℤ)|≤lim.word := by
      rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _)]
      exact (mul_le_mul_of_nonneg_right hr₂.2 (Int.natCast_nonneg _)).trans (by exact_mod_cast hmul₂)
    have ⟨hprod₀lo,hprod₀hi⟩ := abs_le.mp hb₀
    have ⟨hprod₁lo,hprod₁hi⟩ := abs_le.mp hb₁
    have ⟨hprod₂lo,hprod₂hi⟩ := abs_le.mp hb₂
    have ⟨hflaglo,hflaghi⟩ := abs_le.mp hflagj.2
    have ⟨hf₀lo,hf₀hi⟩ := abs_le.mp hr₀.2
    have ⟨hf₁lo,hf₁hi⟩ := abs_le.mp hr₁.2
    have ⟨hf₂lo,hf₂hi⟩ := abs_le.mp hr₂.2
    unfold scanBody
    light_if hf hnf : flag j=0 using hflagj,hr₀,hr₁,hr₂
    · apply Ends.skip
      simp [pick,good,Good,hf,update_frame_setLocal]
    · light_if hc₀ hnc₀ : (t₀ : ℤ)<f₀ j*d₀ using hflagj,hr₀,hr₁,hr₂
      · apply Ends.skip
        simp [pick,good,Good,not_le.mpr hc₀,update_frame_setLocal]
      · light_if hc₁ hnc₁ : (t₁ : ℤ)<f₁ j*d₁ using hflagj,hr₀,hr₁,hr₂
        · apply Ends.skip
          simp [pick,good,Good,not_le.mpr hc₁,update_frame_setLocal]
        · light_if hc₂ hnc₂ : (t₂ : ℤ)<f₂ j*d₂ using hflagj,hr₀,hr₁,hr₂
          · apply Ends.skip
            simp [pick,good,Good,not_le.mpr hc₂,update_frame_setLocal]
          · have hg : good j := ⟨hnf,le_of_not_gt hnc₀,le_of_not_gt hnc₁,le_of_not_gt hnc₂⟩
            light_set (j+1 : ℕ)
            simp [pick,hg,update_frame_setLocal]
  · intro σ hcounter hshape
    exact hshape
  · rintro j _ hj _ rfl
    light_side
  · intro σ hshape
    rw [hshape]
    light_set (pick good n)
    exact ⟨rfl,rfl⟩

def program : Program := [body]

end ThreeSum.LightTernaryRowSelector
