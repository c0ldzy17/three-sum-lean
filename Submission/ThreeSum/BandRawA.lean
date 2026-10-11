import Submission.ThreeSum.BandCandidateRowsMemory
import Submission.ThreeSum.BandPartition

/-!
# Exact A-value incidences of the physical band-owner catalog

Each successful owner contributes only its A band. Labels retain the
physical owner slot and the coordinate in the retained sorted A array.
Equal values and equal triples in different owner slots remain distinct.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows BandEnumeration BandPartition

set_option maxHeartbeats 1600000
set_option maxRecDepth 7000

structure Label where
  owner : ℕ
  position : ℕ
  deriving DecidableEq, Inhabited

def bandLength (n g a : ℕ) : ℕ := stop n g a-start g a

theorem bandLength_eq_min (n g a : ℕ) : bandLength n g a=min g (n-start g a) := by
  unfold bandLength stop start
  simp only [Nat.add_mul,Nat.one_mul]
  omega

def row (n g owner : ℕ) (r : Record) : List Label :=
  if r.flag=1 then
    (List.range (bandLength n g r.a)).map (fun j => ⟨owner,start g r.a+j⟩)
  else []

def firstRows (n g : ℕ) (rs : List Record) (i : ℕ) : List Label :=
  (List.range i).flatMap fun owner => row n g owner (rs.getD owner default)

def items (n g : ℕ) (rs : List Record) : List Label := firstRows n g rs rs.length

def count (n g : ℕ) (rs : List Record) (i : ℕ) : ℕ := (firstRows n g rs i).length

def values (f : ℕ → ℤ) (ls : List Label) : List ℤ := ls.map (fun l => f l.position)
def ownerLabels (ls : List Label) : List ℤ := ls.map (fun l => (l.owner : ℤ))
def positionLabels (ls : List Label) : List ℤ := ls.map (fun l => (l.position : ℤ))

theorem row_length (n g owner : ℕ) (r : Record) :
    (row n g owner r).length=if r.flag=1 then bandLength n g r.a else 0 := by
  unfold row
  split_ifs <;> simp

theorem row_length_le (n g owner : ℕ) (r : Record) : (row n g owner r).length ≤ g := by
  rw [row_length]
  split_ifs
  · exact BandPartition.length_le n g r.a
  · omega

theorem row_getElem {n g owner j : ℕ} {r : Record} (hj : j < (row n g owner r).length) :
    (row n g owner r)[j]=⟨owner,start g r.a+j⟩ := by
  unfold row at hj ⊢
  split_ifs with hf
  · simp only [List.getElem_map,List.getElem_range]
  · simp [hf] at hj

@[simp] theorem firstRows_zero (n g : ℕ) (rs : List Record) : firstRows n g rs 0=[] := rfl

theorem firstRows_succ (n g : ℕ) (rs : List Record) (i : ℕ) :
    firstRows n g rs (i+1)=firstRows n g rs i++row n g i (rs.getD i default) := by
  simp only [firstRows,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]

@[simp] theorem count_zero (n g : ℕ) (rs : List Record) : count n g rs 0=0 := rfl

theorem count_succ (n g : ℕ) (rs : List Record) (i : ℕ) :
    count n g rs (i+1)=count n g rs i+(row n g i (rs.getD i default)).length := by
  simp only [count,firstRows_succ,List.length_append]

theorem count_mono (n g : ℕ) (rs : List Record) : Monotone (count n g rs) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [count_succ]
  omega

theorem count_bound (n g : ℕ) (rs : List Record) (i : ℕ) : count n g rs i ≤ g*i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [count_succ]
    have hh := row_length_le n g i (rs.getD i default)
    nlinarith

theorem items_length_le (n g : ℕ) (rs : List Record) : (items n g rs).length ≤ g*rs.length :=
  count_bound n g rs rs.length

theorem values_length (f : ℕ → ℤ) (ls : List Label) : (values f ls).length=ls.length := List.length_map ..
theorem ownerLabels_length (ls : List Label) : (ownerLabels ls).length=ls.length := List.length_map ..
theorem positionLabels_length (ls : List Label) : (positionLabels ls).length=ls.length := List.length_map ..

theorem mem_row {n g owner : ℕ} {r : Record} {l : Label} :
    l ∈ row n g owner r ↔
      r.flag=1 ∧ l.owner=owner ∧ start g r.a ≤ l.position ∧ l.position < stop n g r.a := by
  unfold row
  by_cases hf : r.flag=1
  · rw [if_pos hf]
    constructor
    · intro hl
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hl
      have hj' : j < bandLength n g r.a := List.mem_range.mp hj
      refine ⟨hf,rfl,?_,?_⟩
      · change start g r.a ≤ start g r.a+j
        omega
      · change start g r.a+j < stop n g r.a
        unfold bandLength at hj'
        omega
    · rintro ⟨_,ho,hs,he⟩
      apply List.mem_map.mpr
      refine ⟨l.position-start g r.a,List.mem_range.mpr (by unfold bandLength; omega),?_⟩
      cases l
      simp only [Label.mk.injEq] at *
      exact ⟨ho.symm,by omega⟩
  · rw [if_neg hf]
    simp [hf]

theorem mem_firstRows {n g i : ℕ} {rs : List Record} {l : Label} :
    l ∈ firstRows n g rs i ↔
      l.owner < i ∧ l ∈ row n g l.owner (rs.getD l.owner default) := by
  constructor
  · intro hl
    obtain ⟨owner,ho,hl⟩ := List.mem_flatMap.mp hl
    have he := (mem_row.mp hl).2.1
    subst owner
    exact ⟨List.mem_range.mp ho,hl⟩
  · rintro ⟨ho,hl⟩
    exact List.mem_flatMap.mpr ⟨l.owner,List.mem_range.mpr ho,hl⟩

theorem position_lt {n g i : ℕ} {rs : List Record} {l : Label}
    (hl : l ∈ firstRows n g rs i) : l.position < n := by
  have hh := (mem_row.mp (mem_firstRows.mp hl).2).2.2.2
  exact hh.trans_le (stop_le n g _)

theorem owner_lt {n g : ℕ} {rs : List Record} {l : Label}
    (hl : l ∈ items n g rs) : l.owner < rs.length := (mem_firstRows.mp hl).1

theorem values_bounded {n g i U : ℕ} {rs : List Record} {f : ℕ → ℤ}
    (hf : ∀ j < n, |f j| ≤ (U : ℤ)) :
    ∀ v ∈ values f (firstRows n g rs i), |v| ≤ (U : ℤ) := by
  intro v hv
  obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hv
  exact hf l.position (position_lt hl)

theorem label_covers {n g s p : ℕ} {rs : List Record}
    (hs : s < rs.length) (hf : (rs.getD s default).flag=1)
    (hp : start g (rs.getD s default).a ≤ p)
    (he : p < stop n g (rs.getD s default).a) :
    (⟨s,p⟩ : Label) ∈ items n g rs :=
  mem_firstRows.mpr ⟨hs,mem_row.mpr ⟨hf,rfl,hp,he⟩⟩

theorem owner_covers {A B C : Family} {n g p : ℕ} (t : Triple A B C)
    (ht : relevant A B C t) (hp : start g t.1.val ≤ p) (he : p < stop n g t.1.val) :
    (⟨slot A B C (owner A B C t),p⟩ : Label) ∈ items n g (records A B C) := by
  have hs : slot A B C (owner A B C t) < (records A B C).length := by
    rw [records_length]
    exact slot_lt A B C _
  have hr := BandCandidateRows.owner_covers A B C t ht
  apply label_covers hs
  · rw [hr]; rfl
  · simpa only [hr,fromTriple] using hp
  · simpa only [hr,fromTriple] using he

theorem incidence_bound {A B C : Family} {n g m : ℕ}
    (hA : A.size ≤ m) (hB : B.size ≤ m) (hC : C.size ≤ m) :
    (items n g (records A B C)).length ≤ 3*m^2*g := by
  have hc := BandCandidateRows.count_bound hA hB hC
  have hi := items_length_le n g (records A B C)
  nlinarith

theorem three_lifts_bound {A B C : Family} {n g m : ℕ}
    (hA : A.size ≤ m) (hB : B.size ≤ m) (hC : C.size ≤ m) :
    3*(items n g (records A B C)).length ≤ 9*m^2*g := by
  have hh := incidence_bound (n := n) (g := g) hA hB hC
  nlinarith

end ThreeSum.BandRawA
