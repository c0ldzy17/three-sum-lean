import Submission.ThreeSum.LightFiniteTable

/-! Literal signed tables are fixed program text, including repeated entries. -/
namespace ThreeSum.LightSignedFiniteTable
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

def literal (z : ℤ) : Expr := k z.toNat -' k (-z).toNat

def stores : ℕ → List ℤ → Stmt
  | _, [] => .skip
  | offset, x :: xs => .store (v 0 +' k offset) (literal x) ;; stores (offset+1) xs

theorem stores_ends (xs : List ℤ) (base offset : ℕ) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : base+offset+xs.length ≤ lim.space)
    (hvalues : ∀ x ∈ xs, |x| ≤ lim.word) :
    Ends lim P d (stores offset xs) ⟨frame [base],μ⟩ (7*xs.length)
      (fun σ => σ.loc=frame [base] ∧ Seg σ.mem (base+offset) xs ∧
        SameOutside μ σ.mem (base+offset) xs.length) := by
  induction xs generalizing offset μ with
  | nil => exact Ends.skip ⟨rfl,Seg.nil,SameOutside.refl⟩
  | cons x xs ih =>
    have haddr : base+offset < lim.space := by simp only [List.length_cons] at hspace; omega
    have haddrWord : ((base+offset : ℕ) : ℤ) ≤ lim.word := by
      exact (show ((base+offset : ℕ) : ℤ) ≤ (lim.space : ℤ) by exact_mod_cast (Nat.le_of_lt haddr)).trans hw
    have hoffWord : (offset : ℤ) ≤ lim.word := by omega
    have hxWord := hvalues x (by simp)
    have hpos : (x.toNat : ℤ) ≤ lim.word := by have h := le_abs_self x; omega
    have hneg : ((-x).toNat : ℤ) ≤ lim.word := by have h := neg_le_abs x; omega
    have hx : (x.toNat : ℤ)-((-x).toNat : ℤ) = x := Int.toNat_sub_toNat_neg x
    rw [stores]
    refine Ends.seq 7 (7*xs.length) ?_ (by simp; omega)
    refine Ends.storeTo (base+offset) x ?_
      (by light_side [literal,haddrWord,hoffWord,hxWord,haddr,hpos,hneg,hx]) (by light_time [literal])
    · have hh := ih (offset+1) (Function.update μ (base+offset) x)
        (by simp only [List.length_cons] at hspace; omega)
        (fun y hy => hvalues y (by simp [hy]))
      apply hh.mono le_rfl
      rintro σ ⟨hloc,hseg,hsame⟩
      refine ⟨hloc,?_,?_⟩
      · rw [seg_cons]
        constructor
        · have ha := hsame (base+offset) (Or.inl (by omega))
          simpa using ha
        · simpa only [Nat.add_assoc] using hseg
      · intro a ha
        have houtside : a < base+(offset+1) ∨ base+(offset+1)+xs.length ≤ a := by
          simp only [List.length_cons] at ha; omega
        rw [hsame a houtside]
        exact Function.update_of_ne (by simp only [List.length_cons] at ha; omega) _ _

def body (xs : List ℤ) : Stmt := stores 0 xs ;; .set 0 (k xs.length)

theorem meets {p : ℕ} {xs : List ℤ} (hprog : P[p]? = some (body xs))
    (base : ℕ) (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : base+xs.length ≤ lim.space) (hvalues : ∀ x ∈ xs, |x| ≤ lim.word) :
    Meets lim P p d [base] μ (7*xs.length+2)
      (fun r ν => r=(xs.length : ℤ) ∧ Seg ν base xs ∧ SameOutside μ ν base xs.length) := by
  have hlenWord : (xs.length : ℤ) ≤ lim.word := by
    exact (show (xs.length : ℤ) ≤ (lim.space : ℤ) by exact_mod_cast (show xs.length ≤ lim.space by omega)).trans hw
  apply Meets.of_body hprog
  unfold body
  refine Ends.seq (7*xs.length) 2 ?_ le_rfl
  have hh := stores_ends (P := P) (d := d) xs base 0 μ hw (by simpa using hspace) hvalues
  apply hh.mono le_rfl
  rintro σ ⟨hloc,hseg,hsame⟩
  cases σ with
  | mk loc mem =>
    dsimp only at hloc hseg hsame ⊢
    subst loc
    light_set (xs.length : ℕ)
    exact ⟨rfl,by simpa using hseg,by simpa using hsame⟩

def program (xs : List ℤ) : Program := [body xs]
theorem program_meets (xs : List ℤ) (base : ℕ) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : base+xs.length ≤ lim.space)
    (hvalues : ∀ x ∈ xs, |x| ≤ lim.word) :
    Meets lim (program xs) 0 d [base] μ (7*xs.length+2)
      (fun r ν => r=(xs.length : ℤ) ∧ Seg ν base xs ∧ SameOutside μ ν base xs.length) :=
  meets rfl base μ hw hspace hvalues
end ThreeSum.LightSignedFiniteTable
