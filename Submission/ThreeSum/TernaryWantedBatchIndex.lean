import Submission.ThreeSum.LightTernaryWantedBatch
import Submission.ThreeSum.TernaryWantedBatchCount

/-! Literal query triples indexed in the actual wanted-batch emission order. -/
noncomputable section
namespace ThreeSum.TernaryWantedBatchIndex
open Light TernaryWantedLittleEndian

abbrev Entry := ℕ × ℕ × ℕ

def entries (P R S J : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ → ℤ) (positions : ℕ → ℕ) : ℕ → List Entry
  | 0 => []
  | n+1 => entries P R S J raws words maps targets positions n ++
      (wantedCodes (P : ℤ) raws words maps J (targets n) R S 0 1 0 1).map
        (fun wg => (positions n,wg.1,wg.2))

def cells (xs : List Entry) : List ℤ :=
  xs.flatMap fun e => [(e.1 : ℤ),e.2.1,e.2.2]

def get (xs : List Entry) (i : ℕ) : Entry := xs.getD i (0,0,0)

theorem mem_entries (P R S J : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ → ℤ) (positions : ℕ → ℕ) (n : ℕ) (e : Entry) :
    e ∈ entries P R S J raws words maps targets positions n ↔
      ∃ t < n, e.1 = positions t ∧ (e.2.1,e.2.2) ∈
        wantedCodes (P : ℤ) raws words maps J (targets t) R S 0 1 0 1 := by
  induction n with
  | zero => simp [entries]
  | succ n ih =>
    rw [entries,List.mem_append,ih]
    constructor
    · rintro (⟨t,ht,hp,hw⟩ | hm)
      · exact ⟨t,by omega,hp,hw⟩
      · obtain ⟨wg,hw,he⟩ := List.mem_map.mp hm
        subst e
        exact ⟨n,by omega,rfl,hw⟩
    · rintro ⟨t,ht,hp,hw⟩
      by_cases h : t < n
      · exact Or.inl ⟨t,h,hp,hw⟩
      · have he : t = n := by omega
        subst t
        apply Or.inr
        refine List.mem_map.mpr ⟨(e.2.1,e.2.2),hw,?_⟩
        rcases e with ⟨pos,w,g⟩
        simpa only [Prod.mk.injEq, true_and, and_true] using hp.symm

theorem cells_append (xs ys : List Entry) : cells (xs++ys) = cells xs++cells ys :=
  List.flatMap_append ..

theorem cells_entries_eq_rows (P R S J : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ → ℤ) (positions : ℕ → ℕ) (n : ℕ) :
    cells (entries P R S J raws words maps targets positions n) =
      LightTernaryWantedBatch.rows P R S J raws words maps targets positions n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [entries,cells_append,ih,LightTernaryWantedBatch.rows]
    congr 1
    simp only [cells,List.flatMap_map,Function.comp_def,TernaryWantedCanonicalPairs.rowCells]

@[simp] theorem cells_length (xs : List Entry) : (cells xs).length = 3*xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [cells,ih]; omega

theorem get_mem {xs : List Entry} {i : ℕ} (hi : i < xs.length) : get xs i ∈ xs := by
  rw [get,List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem entries_length_eq_count (P R S J : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ → ℤ) (positions : ℕ → ℕ) (n : ℕ) :
    (entries P R S J raws words maps targets positions n).length =
      TernaryWantedBatchCount.count P R S J raws words maps targets n := by
  have hh := congrArg List.length (cells_entries_eq_rows P R S J raws words maps targets positions n)
  rw [cells_length,TernaryWantedBatchCount.rows_length] at hh
  omega

theorem exists_index {xs : List Entry} {e : Entry} (he : e ∈ xs) :
    ∃ i < xs.length, get xs i = e := by
  obtain ⟨i,hi,hh⟩ := List.mem_iff_getElem.mp he
  exact ⟨i,hi,by rw [get,List.getD_eq_getElem _ _ hi]; exact hh⟩

theorem read_three {μ : ℕ → ℤ} {base : ℕ} (xs : List Entry)
    (h : Seg μ base (cells xs)) {i : ℕ} (hi : i < xs.length) :
    μ (base+3*i) = ((get xs i).1 : ℤ) ∧
    μ (base+3*i+1) = ((get xs i).2.1 : ℤ) ∧
    μ (base+3*i+2) = ((get xs i).2.2 : ℤ) := by
  induction xs generalizing base i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      refine ⟨?_,?_,?_⟩
      · simpa [get,cells] using h 0 (by simp [cells])
      · simpa [get,cells] using h 1 (by simp [cells])
      · simpa [get,cells] using h 2 (by simp [cells])
    | succ i =>
      have ht : Seg μ (base+3) (cells xs) := by
        simpa [cells] using h.drop 3
      have hh := ih ht (show i < xs.length by simpa using hi)
      simpa only [get,List.getD_cons_succ,Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm,
        Nat.add_left_comm] using hh

theorem read_rows {μ : ℕ → ℤ} {base : ℕ} (P R S J : ℕ) (raws : List ℤ)
    (words maps : List ℕ) (targets : ℕ → ℤ) (positions : ℕ → ℕ) (n : ℕ)
    (h : Seg μ base (LightTernaryWantedBatch.rows P R S J raws words maps targets positions n))
    {i : ℕ} (hi : i < (entries P R S J raws words maps targets positions n).length) :
    let e := get (entries P R S J raws words maps targets positions n) i
    μ (base+3*i) = (e.1 : ℤ) ∧ μ (base+3*i+1) = (e.2.1 : ℤ) ∧ μ (base+3*i+2) = (e.2.2 : ℤ) := by
  apply read_three _ _ hi
  rwa [cells_entries_eq_rows]

end ThreeSum.TernaryWantedBatchIndex
