import Submission.ThreeSum.LightSubsetAddress

/-!
# Initialization of an arbitrary fixed finite table

The table is part of the finite program text.  The procedure writes every
entry using literal store instructions; no input-dependent advice is read.
-/

namespace ThreeSum.LightFiniteTable

open Light

variable {lim : Limits} {P : Program} {d : ℕ}

def stores : ℕ → List ℕ → Stmt
  | _, [] => .skip
  | offset, x :: xs => .store (v 0 +' k offset) (k x) ;; stores (offset+1) xs

theorem stores_ends (xs : List ℕ) (base offset : ℕ) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : base+offset+xs.length ≤ lim.space)
    (hvalues : ∀ x ∈ xs, (x : ℤ) ≤ lim.word) :
    Ends lim P d (stores offset xs) ⟨frame [base],μ⟩ (5*xs.length)
      (fun σ => σ.loc=frame [base] ∧
        Seg σ.mem (base+offset) (xs.map (fun (x : ℕ) => (x : ℤ))) ∧
        SameOutside μ σ.mem (base+offset) xs.length) := by
  induction xs generalizing offset μ with
  | nil =>
    exact Ends.skip ⟨rfl,Seg.nil,SameOutside.refl⟩
  | cons x xs ih =>
    have haddr : base+offset < lim.space := by simp only [List.length_cons] at hspace; omega
    have haddrWord : ((base+offset : ℕ) : ℤ) ≤ lim.word := by
      exact (show ((base+offset : ℕ) : ℤ) ≤ (lim.space : ℤ) by exact_mod_cast (Nat.le_of_lt haddr)).trans hw
    have hoffWord : (offset : ℤ) ≤ lim.word := by
      have hle : (offset : ℤ) ≤ ((base+offset : ℕ) : ℤ) := by omega
      exact hle.trans haddrWord
    have hxWord := hvalues x (by simp)
    rw [stores]
    refine Ends.seq 5 (5*xs.length) ?_ (by simp; omega)
    refine Ends.storeTo (base+offset) (x : ℤ) ?_
      (by light_side [haddrWord,hoffWord,hxWord,haddr]) (by light_time)
    · have hh := ih (offset+1) (Function.update μ (base+offset) (x : ℤ))
        (by simp only [List.length_cons] at hspace; omega)
        (fun y hy => hvalues y (by simp [hy]))
      apply hh.mono le_rfl
      rintro σ ⟨hloc,hseg,hsame⟩
      refine ⟨hloc,?_,?_⟩
      · rw [List.map_cons,seg_cons]
        constructor
        · have ha := hsame (base+offset) (Or.inl (by omega))
          simpa using ha
        · simpa only [Nat.add_assoc] using hseg
      · intro a ha
        have houtside : a < base+(offset+1) ∨ base+(offset+1)+xs.length ≤ a := by
          simp only [List.length_cons] at ha
          omega
        rw [hsame a houtside]
        exact Function.update_of_ne (by simp only [List.length_cons] at ha; omega) _ _

def body (xs : List ℕ) : Stmt := stores 0 xs ;; .set 0 (k xs.length)

theorem meets {p : ℕ} {xs : List ℕ} (hprog : P[p]? = some (body xs))
    (base : ℕ) (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : base+xs.length ≤ lim.space)
    (hvalues : ∀ x ∈ xs, (x : ℤ) ≤ lim.word) :
    Meets lim P p d [base] μ (5*xs.length+2)
      (fun r ν => r=(xs.length : ℤ) ∧
        Seg ν base (xs.map (fun (x : ℕ) => (x : ℤ))) ∧
        SameOutside μ ν base xs.length) := by
  have hlenWord : (xs.length : ℤ) ≤ lim.word := by
    exact (show (xs.length : ℤ) ≤ (lim.space : ℤ) by exact_mod_cast (show xs.length ≤ lim.space by omega)).trans hw
  apply Meets.of_body hprog
  unfold body
  refine Ends.seq (5*xs.length) 2 ?_ le_rfl
  have hh := stores_ends (P := P) (d := d) xs base 0 μ hw (by simpa using hspace) hvalues
  apply hh.mono le_rfl
  rintro σ ⟨hloc,hseg,hsame⟩
  cases σ with
  | mk loc mem =>
    dsimp only at hloc hseg hsame ⊢
    subst loc
    light_set (xs.length : ℕ)
    exact ⟨rfl,by simpa using hseg,by simpa using hsame⟩

def program (xs : List ℕ) : Program := [body xs]

theorem program_meets (xs : List ℕ) (base : ℕ) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : base+xs.length ≤ lim.space)
    (hvalues : ∀ x ∈ xs, (x : ℤ) ≤ lim.word) :
    Meets lim (program xs) 0 d [base] μ (5*xs.length+2)
      (fun r ν => r=(xs.length : ℤ) ∧
        Seg ν base (xs.map (fun (x : ℕ) => (x : ℤ))) ∧
        SameOutside μ ν base xs.length) :=
  meets rfl base μ hw hspace hvalues

end ThreeSum.LightFiniteTable
