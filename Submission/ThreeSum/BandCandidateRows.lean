import Submission.ThreeSum.LightBandEnumeration
import Submission.ThreeSum.OutputDecodeOrder

/-!
# The exact physical band-owner record order

There is one four-cell record for every owner-table cell, in BC, AB, AC
rectangle order. A zero flag is a lookup miss. Successful records retain
their physical owner slot even when several owners produce the same triple.
-/

namespace ThreeSum.BandCandidateRows

open BandEnumeration

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000

inductive Mode where
  | bc | ab | ac
  deriving DecidableEq

structure Record where
  flag : ℕ
  a : ℕ
  b : ℕ
  c : ℕ
  deriving DecidableEq, Inhabited

def make (mode : Mode) (i j r : ℕ) : Record :=
  match mode with
  | .bc => ⟨if 0 < r then 1 else 0,r-1,i,j⟩
  | .ab => ⟨if 0 < r then 1 else 0,i,j,r-1⟩
  | .ac => ⟨if 0 < r then 1 else 0,i,r-1,j⟩

def Record.cells (r : Record) : List ℤ := [r.flag,r.a,r.b,r.c]

def bc (A B C : Family) (j k : ℕ) : Record :=
  make .bc j k (LightBandLookup.result A.lower A.upper A.size (C.lower k-B.upper j))

def ab (A B C : Family) (i j : ℕ) : Record :=
  make .ab i j (LightBandLookup.result C.lower C.upper C.size (A.lower i+B.lower j))

def ac (A B C : Family) (i k : ℕ) : Record :=
  make .ac i k (LightBandLookup.result B.lower B.upper B.size (C.lower k-A.lower i))

def rect (m n : ℕ) (F : ℕ → ℕ → Record) : List Record :=
  (List.range m).flatMap fun i => (List.range n).map (F i)

def records (A B C : Family) : List Record :=
  rect B.size C.size (bc A B C) ++
    (rect A.size B.size (ab A B C) ++ rect A.size C.size (ac A B C))

def cells (rs : List Record) : List ℤ := rs.flatMap Record.cells

def slot (A B C : Family) : Owner A B C → ℕ
  | .inl (j,k) => j.val*C.size+k.val
  | .inr (i,.inl j) => B.size*C.size+i.val*B.size+j.val
  | .inr (i,.inr k) => B.size*C.size+A.size*B.size+i.val*C.size+k.val

def fromOwner (A B C : Family) : Owner A B C → Record
  | .inl (j,k) => bc A B C j.val k.val
  | .inr (i,.inl j) => ab A B C i.val j.val
  | .inr (i,.inr k) => ac A B C i.val k.val

def fromTriple {A B C : Family} (t : Triple A B C) : Record :=
  ⟨1,t.1.val,t.2.1.val,t.2.2.val⟩

theorem rect_length (m n : ℕ) (F : ℕ → ℕ → Record) : (rect m n F).length=m*n := by
  simp [rect,List.length_flatMap]

theorem records_length (A B C : Family) :
    (records A B C).length=LightBandEnumeration.count A.size B.size C.size := by
  simp only [records,List.length_append,rect_length,LightBandEnumeration.count]
  omega

theorem cells_length (rs : List Record) : (cells rs).length=4*rs.length := by
  induction rs with
  | nil => simp [cells]
  | cons r rs ih => simp only [cells,List.flatMap_cons,List.length_append,Record.cells,
      List.length_cons,List.length_nil] at *; omega

theorem index_lt {i j m n : ℕ} (hi : i < m) (hj : j < n) : i*n+j < m*n := by
  have hh := Nat.mul_le_mul_right n (show i+1 ≤ m by omega)
  simp only [Nat.add_mul,Nat.one_mul] at hh
  omega

theorem rect_getD {m n i j : ℕ} (F : ℕ → ℕ → Record) (hi : i < m) (hj : j < n) :
    (rect m n F).getD (i*n+j) default=F i j := by
  have hi' : i < (List.range m).length := by simpa using hi
  have hj' : j < (List.range n).length := by simpa using hj
  rw [rect,OutputDecodeOrder.getD_flatMap_uniform _ _ n (by simp) 0 default hi' hj]
  rw [List.getD_eq_getElem _ _ hi']
  simp only [List.getElem_range]
  rw [List.getD_map_of_lt _ hj' 0 default,List.getD_eq_getElem _ _ hj']
  simp only [List.getElem_range]

theorem slot_lt (A B C : Family) (o : Owner A B C) :
    slot A B C o < LightBandEnumeration.count A.size B.size C.size := by
  rcases o with ⟨j,k⟩ | ⟨i,j | k⟩
  · have hh := index_lt j.isLt k.isLt
    simp only [slot,LightBandEnumeration.count]
    omega
  · have hh := index_lt i.isLt j.isLt
    simp only [slot,LightBandEnumeration.count]
    omega
  · have hh := index_lt i.isLt k.isLt
    simp only [slot,LightBandEnumeration.count]
    omega

theorem records_getD_slot (A B C : Family) (o : Owner A B C) :
    (records A B C).getD (slot A B C o) default=fromOwner A B C o := by
  rcases o with ⟨j,k⟩ | ⟨i,j | k⟩
  · simp only [records,slot,fromOwner]
    rw [List.getD_append _ _ _ _ (by rw [rect_length]; exact index_lt j.isLt k.isLt)]
    exact rect_getD _ j.isLt k.isLt
  · simp only [records,slot,fromOwner]
    rw [List.getD_append_right _ _ _ _ (by rw [rect_length]; omega),rect_length]
    have hoff : B.size*C.size+i.val*B.size+j.val-B.size*C.size=i.val*B.size+j.val := by omega
    rw [hoff,List.getD_append _ _ _ _ (by rw [rect_length]; exact index_lt i.isLt j.isLt)]
    exact rect_getD _ i.isLt j.isLt
  · simp only [records,slot,fromOwner]
    rw [List.getD_append_right _ _ _ _ (by rw [rect_length]; omega),rect_length]
    have hoff : B.size*C.size+A.size*B.size+i.val*C.size+k.val-B.size*C.size=
        A.size*B.size+i.val*C.size+k.val := by omega
    rw [hoff,List.getD_append_right _ _ _ _ (by rw [rect_length]; omega),rect_length]
    have hoff' : A.size*B.size+i.val*C.size+k.val-A.size*B.size=i.val*C.size+k.val := by omega
    rw [hoff']
    exact rect_getD _ i.isLt k.isLt

theorem make_flag (mode : Mode) (i j r : ℕ) :
    (make mode i j r).flag=0 ∨ (make mode i j r).flag=1 := by
  cases mode <;> simp only [make] <;> split_ifs <;> simp

theorem make_flag_one_iff (mode : Mode) (i j r : ℕ) :
    (make mode i j r).flag=1 ↔ 0 < r := by
  cases mode <;> simp only [make] <;> split_ifs <;> simp_all

theorem fromOwner_sound (A B C : Family) (o : Owner A B C)
    (hf : (fromOwner A B C o).flag=1) :
    let r := fromOwner A B C o
    r.a < A.size ∧ r.b < B.size ∧ r.c < C.size ∧
      Bands.Relevant A.lower A.upper B.lower B.upper C.lower C.upper (r.a,r.b,r.c) := by
  rcases o with ⟨j,k⟩ | ⟨i,j | k⟩
  · have hp := (make_flag_one_iff .bc j.val k.val _).mp hf
    let r := LightBandLookup.result A.lower A.upper A.size (C.lower k-B.upper j)
    have hr : r=(r-1)+1 := by omega
    have hs := LightBandEnumeration.lookup_sound A (i := r-1) hr
    have hB := B.nonempty j j.isLt
    have hC := C.nonempty k k.isLt
    refine ⟨hs.1,j.isLt,k.isLt,?_⟩
    change A.lower (r-1) ≤ C.upper k-B.lower j ∧ C.lower k-B.upper j ≤ A.upper (r-1)
    omega
  · have hp := (make_flag_one_iff .ab i.val j.val _).mp hf
    let r := LightBandLookup.result C.lower C.upper C.size (A.lower i+B.lower j)
    have hr : r=(r-1)+1 := by omega
    have hs := LightBandEnumeration.lookup_sound C (i := r-1) hr
    have hA := A.nonempty i i.isLt
    have hB := B.nonempty j j.isLt
    refine ⟨i.isLt,j.isLt,hs.1,?_⟩
    change A.lower i ≤ C.upper (r-1)-B.lower j ∧ C.lower (r-1)-B.upper j ≤ A.upper i
    omega
  · have hp := (make_flag_one_iff .ac i.val k.val _).mp hf
    let r := LightBandLookup.result B.lower B.upper B.size (C.lower k-A.lower i)
    have hr : r=(r-1)+1 := by omega
    have hs := LightBandEnumeration.lookup_sound B (i := r-1) hr
    have hA := A.nonempty i i.isLt
    have hC := C.nonempty k k.isLt
    refine ⟨i.isLt,hs.1,k.isLt,?_⟩
    change A.lower i ≤ C.upper k-B.lower (r-1) ∧ C.lower k-B.upper (r-1) ≤ A.upper i
    omega

theorem lookup_result (A : Family) (x : ℤ) (i : A.Index) (hi : A.lookup x=some i) :
    LightBandLookup.result A.lower A.upper A.size x=i.val+1 :=
  LightBandEnumeration.lookup_complete A i.isLt (A.lookup_sound x i hi).1 (A.lookup_sound x i hi).2

theorem fromOwner_of_candidate (A B C : Family) (o : Owner A B C) (t : Triple A B C)
    (hc : candidate A B C o=some t) : fromOwner A B C o=fromTriple t := by
  rcases o with ⟨j,k⟩ | ⟨i,j | k⟩
  · simp only [candidate] at hc
    cases he : A.lookup (C.lo k-B.hi j) with
    | none => simp [he] at hc
    | some a =>
      have ht : (a,j,k)=t := by simpa only [he,Option.map_some,Option.some.injEq] using hc
      subst t
      have hr := lookup_result A _ a he
      change LightBandLookup.result A.lower A.upper A.size (C.lower k-B.upper j)=a.val+1 at hr
      simp [fromOwner,bc,make,hr,fromTriple]
  · simp only [candidate] at hc
    cases he : C.lookup (A.lo i+B.lo j) with
    | none => simp [he] at hc
    | some c =>
      have ht : (i,j,c)=t := by simpa only [he,Option.map_some,Option.some.injEq] using hc
      subst t
      have hr := lookup_result C _ c he
      change LightBandLookup.result C.lower C.upper C.size (A.lower i+B.lower j)=c.val+1 at hr
      simp [fromOwner,ab,make,hr,fromTriple]
  · simp only [candidate] at hc
    cases he : B.lookup (C.lo k-A.lo i) with
    | none => simp [he] at hc
    | some b =>
      have ht : (i,b,k)=t := by simpa only [he,Option.map_some,Option.some.injEq] using hc
      subst t
      have hr := lookup_result B _ b he
      change LightBandLookup.result B.lower B.upper B.size (C.lower k-A.lower i)=b.val+1 at hr
      simp [fromOwner,ac,make,hr,fromTriple]

theorem owner_covers (A B C : Family) (t : Triple A B C) (ht : relevant A B C t) :
    (records A B C).getD (slot A B C (owner A B C t)) default=fromTriple t := by
  rw [records_getD_slot]
  exact fromOwner_of_candidate A B C _ t (candidate_owner A B C t ht)

theorem count_bound {A B C : Family} {m : ℕ}
    (hA : A.size ≤ m) (hB : B.size ≤ m) (hC : C.size ≤ m) :
    (records A B C).length ≤ 3*m^2 := by
  rw [records_length]
  have hh := LightBandEnumeration.count_mono hA hB hC
  calc
    _ ≤ LightBandEnumeration.count m m m := hh
    _ = 3*m^2 := by unfold LightBandEnumeration.count; ring

end ThreeSum.BandCandidateRows
