import Submission.ThreeSum.LightClassFilter
import Submission.ThreeSum.LightColorIndex

/-!
# Exact original-position semantics of the constructed color-class lists

The machine keeps repeated values within a class and negates the third
class. The list membership witnesses are original positions. Any binary
width large enough for the indices suffices for the deterministic family.
-/

namespace ThreeSum.ColorClassLists

open LightClassFilter

def value {n : ℕ} (x : Fin n → ℤ) (i : ℕ) : ℤ := if hi : i < n then x ⟨i,hi⟩ else 0

@[simp] theorem value_fin {n : ℕ} (x : Fin n → ℤ) (i : Fin n) : value x i.val = x i := by
  simp [value,i.isLt]

def indexColor {n W : ℕ} (p : Coloring.Parameter W) (i : Fin n) : Fin 3 :=
  p.2 (i.val.testBit p.1.1.val,i.val.testBit p.1.2.val)

def classList {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) : List ℤ :=
  items (value x) (LightColorIndex.color p) c scale n

theorem mem_classList {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (c : Fin 3) (z : ℤ) :
    z ∈ classList p x c.val 1 ↔ z ∈ Coloring.values x (indexColor p) c := by
  rw [classList,mem_items,Coloring.mem_values]
  simp only [one_mul]
  constructor
  · rintro ⟨i,hi,hc,hx⟩
    refine ⟨⟨i,hi⟩,Fin.ext hc,?_⟩
    simpa only [← value_fin x ⟨i,hi⟩] using hx
  · rintro ⟨i,hc,hx⟩
    exact ⟨i.val,i.isLt,congrArg Fin.val hc,by simpa using hx⟩

theorem mem_negClassList {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ) (z : ℤ) :
    z ∈ classList p x 2 (-1) ↔ z ∈ Coloring.negValues x (indexColor p) := by
  rw [classList,mem_items,Coloring.mem_negValues]
  simp only [neg_one_mul]
  constructor
  · rintro ⟨i,hi,hc,hx⟩
    refine ⟨⟨i,hi⟩,Fin.ext hc,?_⟩
    simpa only [← value_fin x ⟨i,hi⟩] using hx
  · rintro ⟨i,hc,hx⟩
    exact ⟨i.val,i.isLt,congrArg Fin.val hc,by simpa using hx⟩

theorem length_classList_le {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) : (classList p x c scale).length ≤ n :=
  items_length_le ..

theorem items_lengths_sum (x : ℕ → ℤ) (color : ℕ → ℕ) (hcolor : ∀ i, color i < 3) (n : ℕ) :
    (items x color 0 1 n).length + (items x color 1 1 n).length +
      (items x color 2 (-1) n).length = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc := hcolor n
    have hc' : color n = 0 ∨ color n = 1 ∨ color n = 2 := by omega
    rcases hc' with he | he | he <;>
      simp only [items_succ,he] <;> norm_num at * <;> omega

theorem class_lengths_sum {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ) :
    (classList p x 0 1).length + (classList p x 1 1).length +
      (classList p x 2 (-1)).length = n :=
  items_lengths_sum _ _ (LightColorIndex.color_lt p) n

def witness {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ) : Prop :=
  ∃ a ∈ classList p x 0 1, ∃ b ∈ classList p x 1 1,
    ∃ c ∈ classList p x 2 (-1), a+b=c

theorem witness_iff {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ) :
    witness p x ↔ Coloring.ThreeSetWitness
      (Coloring.values x (indexColor p) 0) (Coloring.values x (indexColor p) 1)
      (Coloring.negValues x (indexColor p)) := by
  unfold witness Coloring.ThreeSetWitness
  have h0 (z : ℤ) : z ∈ classList p x 0 1 ↔ z ∈ Coloring.values x (indexColor p) 0 :=
    mem_classList p x (0 : Fin 3) z
  have h1 (z : ℤ) : z ∈ classList p x 1 1 ↔ z ∈ Coloring.values x (indexColor p) 1 :=
    mem_classList p x (1 : Fin 3) z
  simp only [h0,h1,mem_negClassList]

theorem bits_injective {n W : ℕ} (hn : n ≤ 2^W) :
    Function.Injective (fun i : Fin n => fun j : Fin W => i.val.testBit j.val) := by
  intro i j he
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < W
  · exact congrFun he ⟨k,hk⟩
  · have hp : 2^W ≤ 2^k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (i.isLt.trans_le (hn.trans hp)),
      Nat.testBit_eq_false_of_lt (j.isLt.trans_le (hn.trans hp))]

/-- Every original distinct-position zero sum appears in one of the actual
list triples, for any machine-computed sufficient width. -/
theorem reduction_correct {n W : ℕ} (x : Fin n → ℤ) (hn : n ≤ 2^W) :
    Coloring.DistinctZeroSum x ↔ ∃ p : Coloring.Parameter W, witness p x := by
  constructor
  · rintro ⟨i,j,k,hij,hik,hjk,hsum⟩
    obtain ⟨p,hi,hj,hk⟩ := Coloring.exists_separating_parameter
      (fun he => hij (bits_injective hn he)) (fun he => hik (bits_injective hn he))
      (fun he => hjk (bits_injective hn he))
    refine ⟨p,(witness_iff p x).mpr ?_⟩
    refine ⟨x i,(Coloring.mem_values x (indexColor p) 0 _).mpr ⟨i,hi,rfl⟩,
      x j,(Coloring.mem_values x (indexColor p) 1 _).mpr ⟨j,hj,rfl⟩,
      -x k,(Coloring.mem_negValues x (indexColor p) _).mpr ⟨k,hk,rfl⟩,?_⟩
    omega
  · rintro ⟨p,hp⟩
    obtain ⟨a,ha,b,hb,c,hc,he⟩ := (witness_iff p x).mp hp
    obtain ⟨i,hi,rfl⟩ := (Coloring.mem_values x (indexColor p) 0 a).mp ha
    obtain ⟨j,hj,rfl⟩ := (Coloring.mem_values x (indexColor p) 1 b).mp hb
    obtain ⟨k,hk,rfl⟩ := (Coloring.mem_negValues x (indexColor p) c).mp hc
    exact ⟨i,j,k,by intro heq; subst j; simp_all,
      by intro heq; subst k; simp_all,
      by intro heq; subst k; simp_all,by omega⟩

end ThreeSum.ColorClassLists
