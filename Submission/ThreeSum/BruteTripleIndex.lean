import Submission.ThreeSum.Coloring

/-! # A literal order of all original-position triples for the finite fallback -/

namespace ThreeSum.BruteTripleIndex

def first (n t : ℕ) : ℕ := t/n/n
def second (n t : ℕ) : ℕ := t/n%n
def third (n t : ℕ) : ℕ := t%n

theorem bounds {n t : ℕ} (hn : 0 < n) (ht : t < n^3) :
    first n t < n ∧ second n t < n ∧ third n t < n := by
  have ht' : t < (n*n)*n := by simpa only [pow_succ,pow_zero,one_mul] using ht
  have hq : t/n < n*n := (Nat.div_lt_iff_lt_mul hn).mpr ht'
  exact ⟨(Nat.div_lt_iff_lt_mul hn).mpr hq,Nat.mod_lt _ hn,Nat.mod_lt _ hn⟩

def code {n : ℕ} (i j k : Fin n) : ℕ := (i.val*n+j.val)*n+k.val

theorem code_lt {n : ℕ} (i j k : Fin n) : code i j k < n^3 := by
  have hpair : i.val*n+j.val < n*n := by
    calc
      _ < i.val*n+n := Nat.add_lt_add_left j.isLt _
      _ = (i.val+1)*n := by ring
      _ ≤ n*n := Nat.mul_le_mul_right n (by omega)
  calc
    code i j k < (i.val*n+j.val)*n+n := Nat.add_lt_add_left k.isLt _
    _ = (i.val*n+j.val+1)*n := by ring
    _ ≤ (n*n)*n := Nat.mul_le_mul_right n (by omega)
    _ = n^3 := by ring

theorem decode_code {n : ℕ} (i j k : Fin n) :
    first n (code i j k)=i.val ∧ second n (code i j k)=j.val ∧ third n (code i j k)=k.val := by
  have hn : 0 < n := by have := i.isLt; omega
  have hq : code i j k/n=i.val*n+j.val := by
    unfold code
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hn,Nat.div_eq_of_lt k.isLt]
    simp
  have hi : (i.val*n+j.val)/n=i.val := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hn,Nat.div_eq_of_lt j.isLt]
    simp
  have hj : (i.val*n+j.val)%n=j.val := by
    rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt j.isLt]
  have hk : code i j k%n=k.val := by
    unfold code
    rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt k.isLt]
  exact ⟨by simp only [first,hq,hi],by simp only [second,hq,hj],hk⟩

def witness {n t : ℕ} (x : Fin n → ℤ) (hn : 0 < n) (ht : t < n^3) : Prop :=
  let a : Fin n := ⟨first n t,(bounds hn ht).1⟩
  let b : Fin n := ⟨second n t,(bounds hn ht).2.1⟩
  let c : Fin n := ⟨third n t,(bounds hn ht).2.2⟩
  a≠b ∧ a≠c ∧ b≠c ∧ x a+x b+x c=0

def Hit {n : ℕ} (x : Fin n → ℤ) (hn : 0 < n) (t : ℕ) : Prop :=
  ∃ i, ∃ hi : i < n^3, i < t ∧ witness x hn hi

theorem hit_zero {n : ℕ} (x : Fin n → ℤ) (hn : 0 < n) : ¬ Hit x hn 0 := by
  rintro ⟨_,_,hlt,_⟩
  omega

theorem hit_succ {n t : ℕ} (x : Fin n → ℤ) (hn : 0 < n) (ht : t < n^3) :
    Hit x hn (t+1) ↔ Hit x hn t ∨ witness x hn ht := by
  constructor
  · rintro ⟨i,hi,hlt,hx⟩
    by_cases he : i=t
    · subst i
      exact Or.inr hx
    · exact Or.inl ⟨i,hi,by omega,hx⟩
  · rintro (⟨i,hi,hlt,hx⟩ | hx)
    · exact ⟨i,hi,by omega,hx⟩
    · exact ⟨t,ht,by omega,hx⟩

theorem hit_complete {n : ℕ} (x : Fin n → ℤ) (hn : 0 < n) :
    Hit x hn (n^3) ↔ Coloring.DistinctZeroSum x := by
  constructor
  · rintro ⟨i,hi,_,hx⟩
    exact ⟨⟨first n i,(bounds hn hi).1⟩,⟨second n i,(bounds hn hi).2.1⟩,
      ⟨third n i,(bounds hn hi).2.2⟩,hx⟩
  · rintro ⟨i,j,k,hij,hik,hjk,hzero⟩
    refine ⟨code i j k,code_lt i j k,code_lt i j k,?_⟩
    have ha : (⟨first n (code i j k),(bounds hn (code_lt i j k)).1⟩ : Fin n)=i :=
      Fin.ext (decode_code i j k).1
    have hb : (⟨second n (code i j k),(bounds hn (code_lt i j k)).2.1⟩ : Fin n)=j :=
      Fin.ext (decode_code i j k).2.1
    have hc : (⟨third n (code i j k),(bounds hn (code_lt i j k)).2.2⟩ : Fin n)=k :=
      Fin.ext (decode_code i j k).2.2
    simpa only [witness,ha,hb,hc] using And.intro hij (And.intro hik (And.intro hjk hzero))

end ThreeSum.BruteTripleIndex
