import Submission.ThreeSum.LightFiniteTable

/-! Fixed-length runtime metadata headers are written by actual store instructions. -/
namespace ThreeSum.LightArgumentTable
open Light

def stores (offset : ℕ) : ℕ → Stmt
  | 0 => .skip
  | n+1 => .store (v 0 +' k offset) (v (offset+1)) ;; stores (offset+1) n

variable {lim : Limits} {P : Program} {depth : ℕ}

theorem stores_ends (xs : List ℤ) (base offset : ℕ) (loc μ : ℕ → ℤ)
    (hbase : loc 0=(base : ℤ))
    (hread : ∀ (i : ℕ) (hi : i<xs.length), loc (offset+i+1)=xs.getD i 0)
    (hw : (lim.space : ℤ)≤lim.word) (hspace : base+offset+xs.length≤lim.space) :
    Ends lim P depth (stores offset xs.length) ⟨loc,μ⟩ (5*xs.length)
      (fun σ => σ.loc=loc ∧ Seg σ.mem (base+offset) xs ∧
        SameOutside μ σ.mem (base+offset) xs.length) := by
  induction xs generalizing offset μ with
  | nil => exact Ends.skip ⟨rfl,Seg.nil,SameOutside.refl⟩
  | cons x xs ih =>
    have haddr : base+offset<lim.space := by simp only [List.length_cons] at hspace; omega
    have haddrWord : ((base+offset : ℕ) : ℤ)≤lim.word :=
      (Int.ofNat_le.mpr (Nat.le_of_lt haddr)).trans hw
    have hoff : (offset : ℤ)≤lim.word := by omega
    have hx : loc (offset+1)=x := by simpa only [Nat.add_zero,List.getD_cons_zero] using hread 0 (by simp)
    simp only [List.length_cons,stores]
    refine Ends.seq 5 (5*xs.length) ?_ (by omega)
    refine Ends.storeLast ?_ (hs := by light_side [hbase,hx,haddr,haddrWord,hoff]) (hT := by light_time)
    have hrest := ih (offset+1) (Function.update μ (base+offset) x)
      (fun i hi => by simpa only [List.getD_cons_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hread (i+1) (by simpa only [List.length_cons] using Nat.succ_lt_succ hi))
      (by simp only [List.length_cons] at hspace; omega)
    simp only [Expr.val,Op.eval,hbase,hx,←Nat.cast_add,Int.toNat_natCast]
    apply hrest.mono le_rfl
    rintro σ ⟨hloc,hseg,hkeep⟩
    refine ⟨hloc,?_,?_⟩
    · rw [seg_cons]
      refine ⟨?_,?_⟩
      · have hh := hkeep (base+offset) (Or.inl (by omega))
        simpa using hh
      · simpa only [Nat.add_assoc] using hseg
    · intro a ha
      rw [hkeep a (by omega)]
      exact Function.update_of_ne (by omega) _ _

theorem meets {proc N : ℕ} (hp : P[proc]?=some (stores 0 N))
    (xs : List ℤ) (hlen : xs.length=N) (base : ℕ) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hspace : base+N≤lim.space) :
    Meets lim P proc depth ((base : ℤ)::xs) μ (5*N)
      (fun z ν => z=(base : ℤ) ∧ Seg ν base xs ∧ SameOutside μ ν base N) := by
  apply Meets.of_body hp
  have hh := stores_ends (P := P) (depth := depth) xs base 0 (frame ((base : ℤ)::xs)) μ rfl
    (fun i hi => by simp [frame]) hw (by simpa [hlen] using hspace)
  rw [hlen] at hh
  apply hh.mono le_rfl
  rintro σ ⟨hloc,hseg,hkeep⟩
  refine ⟨?_,by simpa using hseg,by simpa using hkeep⟩
  rw [hloc]
  rfl

end ThreeSum.LightArgumentTable
