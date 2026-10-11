import Submission.ThreeSum.GlobalEncoding
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.TakeDrop

/-!
# Exact product-list semantics for global radix-key construction

The key list retains every local occurrence, even when several records have
the same integer key. Each stage prepends one local record and computes its
positional hash. This is the order used by the concrete row constructor.
-/

namespace ThreeSum.RadixKeyLists

variable {α β : Type*}

theorem flatMap_length_uniform (xs : List α) (f : α → List β) (q : ℕ)
    (h : ∀ x ∈ xs, (f x).length=q) : (xs.flatMap f).length=xs.length*q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,
      h x (by simp),ih (by intro a ha; exact h a (by simp [ha]))]
    ring

def step (p : ℤ) (base prev : List ℤ) : List ℤ :=
  base.flatMap fun x => prev.map fun y => x+p*y

theorem step_length (p : ℤ) (base prev : List ℤ) :
    (step p base prev).length=base.length*prev.length :=
  flatMap_length_uniform base _ prev.length (by simp)

theorem step_take_succ (p : ℤ) (base prev : List ℤ) {i : ℕ} (hi : i < base.length) :
    step p (base.take (i+1)) prev = step p (base.take i) prev ++
      prev.map (fun y => base[i]+p*y) := by
  rw [List.take_succ_eq_append_getElem hi]
  simp only [step,List.flatMap_append,List.flatMap_singleton]

def values (p : ℤ) (base : List ℤ) : ℕ → List ℤ
  | 0 => [0]
  | j+1 => step p base (values p base j)

theorem values_length (p : ℤ) (base : List ℤ) (j : ℕ) :
    (values p base j).length=base.length^j := by
  induction j with
  | zero => simp [values]
  | succ j ih => rw [values,step_length,ih,pow_succ']

/-- Original records, before taking integer keys. Distinct records remain
distinct even if their keys coincide. -/
def tuples (base : List α) : ℕ → List (List α)
  | 0 => [[]]
  | j+1 => base.flatMap fun a => (tuples base j).map (List.cons a)

theorem tuples_length (base : List α) (j : ℕ) :
    (tuples base j).length=base.length^j := by
  induction j with
  | zero => simp [tuples]
  | succ j ih =>
    rw [tuples,flatMap_length_uniform base _ (base.length^j) (by simp [ih]),pow_succ']

theorem mem_tuples (base : List α) (j : ℕ) (xs : List α) :
    xs ∈ tuples base j ↔ xs.length=j ∧ ∀ a ∈ xs, a ∈ base := by
  induction j generalizing xs with
  | zero => cases xs <;> simp [tuples]
  | succ j ih =>
    cases xs with
    | nil => simp [tuples]
    | cons a xs =>
      simp only [tuples,List.mem_flatMap,List.mem_map,List.cons.injEq,
        ih,List.length_cons,Nat.add_right_cancel_iff,List.mem_cons,forall_eq_or_imp]
      constructor
      · rintro ⟨b,hb,ys,⟨hlen,hsub⟩,rfl,rfl⟩
        exact ⟨hlen,hb,hsub⟩
      · rintro ⟨hlen,hb,hsub⟩
        exact ⟨a,hb,xs,⟨hlen,hsub⟩,rfl,rfl⟩

theorem tuples_nodup (base : List α) (hbase : base.Nodup) (j : ℕ) :
    (tuples base j).Nodup := by
  induction j with
  | zero => simp [tuples]
  | succ j ih =>
    apply List.nodup_flatMap.mpr
    constructor
    · intro a ha
      exact ih.map (fun xs ys he => (List.cons.inj he).2)
    · exact hbase.imp (fun {a b} hab xs hxs hys => by
        obtain ⟨tail,_,rfl⟩ := List.mem_map.mp hxs
        obtain ⟨other,_,he⟩ := List.mem_map.mp hys
        exact hab (List.cons.inj he).1.symm)

theorem values_eq_map (p : ℤ) (raw : α → ℤ) (base : List α) (j : ℕ) :
    values p (base.map raw) j = (tuples base j).map (Radix.positionalHash p raw) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [values,step,tuples,List.flatMap_map,List.map_flatMap,List.map_map,ih]
    apply List.flatMap_congr
    intro a ha
    simp only [Function.comp_def,Radix.positionalHash]

theorem values_bounded (p U : ℕ) (base : List ℤ)
    (hbase : ∀ x ∈ base, |x| ≤ (U : ℤ)) (j : ℕ) :
    ∀ z ∈ values (p : ℤ) base j, |z| ≤ ((U*(p+1)^j : ℕ) : ℤ) := by
  induction j with
  | zero =>
    intro z hz
    have hz0 : z=0 := by simpa only [values,List.mem_singleton] using hz
    subst z
    simp
  | succ j ih =>
    intro z hz
    obtain ⟨a,ha,hz⟩ := List.mem_flatMap.mp hz
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hz
    have hkey := hbase a ha
    have htail := ih y hy
    have hpow : 1 ≤ (p+1)^j := one_le_pow₀ (by omega)
    have hU : (U : ℤ) ≤ ((U*(p+1)^j : ℕ) : ℤ) := by
      exact_mod_cast (Nat.le_mul_of_pos_right U (by omega : 0 < (p+1)^j))
    calc
      |a+(p : ℤ)*y| ≤ |a|+(p : ℤ)*|y| := by
        simpa only [abs_mul,Int.abs_natCast] using abs_add_le a ((p : ℤ)*y)
      _ ≤ (U : ℤ)+(p : ℤ)*((U*(p+1)^j : ℕ) : ℤ) :=
        add_le_add hkey (mul_le_mul_of_nonneg_left htail (Int.natCast_nonneg _))
      _ ≤ ((U*(p+1)^j : ℕ) : ℤ)+(p : ℤ)*((U*(p+1)^j : ℕ) : ℤ) :=
        add_le_add hU le_rfl
      _ = ((U*(p+1)^(j+1) : ℕ) : ℤ) := by push_cast; rw [pow_succ]; ring

end ThreeSum.RadixKeyLists
