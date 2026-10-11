import Submission.ThreeSum.RadixKeyLists
import Submission.ThreeSum.GlobalKeyEnumeration
import Submission.ThreeSumApsp.Util.List

/-!
# Exact physical tuple indices for output decoding

The product enumerator is lexicographic: its first block is the outermost
choice. Repeated integer key values have no role in these index equations.
The recursive decoder takes the final coordinate by division and remainder.
-/

namespace ThreeSum.OutputDecodeOrder

open RadixKeyLists

set_option maxHeartbeats 1800000
set_option maxRecDepth 6000

variable {α β : Type*}

theorem getD_flatMap_uniform (xs : List α) (f : α → List β) (q : ℕ)
    (hf : ∀ x ∈ xs, (f x).length=q) (da : α) (db : β)
    {z r : ℕ} (hz : z < xs.length) (hr : r < q) :
    (xs.flatMap f).getD (z*q+r) db = (f (xs.getD z da)).getD r db := by
  induction xs generalizing z with
  | nil => simp at hz
  | cons x xs ih =>
    have hlen : (f x).length=q := hf x (by simp)
    have htail : ∀ a ∈ xs, (f a).length=q := fun a ha => hf a (by simp [ha])
    cases z with
    | zero =>
      simp only [Nat.zero_mul,Nat.zero_add,List.getD_cons_zero,List.flatMap_cons]
      exact List.getD_append _ _ _ _ (by omega)
    | succ z =>
      have hz' : z < xs.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hz
      have hoff : (z+1)*q+r-q=z*q+r := by simp only [Nat.add_mul,one_mul]; omega
      rw [List.flatMap_cons,List.getD_append_right _ _ _ _ (by
        rw [hlen]
        simp only [Nat.succ_eq_add_one,Nat.add_mul,one_mul]
        omega),hlen]
      rw [hoff,List.getD_cons_succ]
      exact ih htail hz'

theorem tuples_succ_right (base : List α) (J : ℕ) :
    tuples base (J+1) = (tuples base J).flatMap fun xs => base.map fun a => xs++[a] := by
  induction J with
  | zero =>
    have hh : base.flatMap (fun a => [[a]]) = base.map (fun a => [a]) := by
      induction base with
      | nil => rfl
      | cons a xs ih => simp [ih]
    simpa [tuples] using hh
  | succ J ih =>
    calc
      _ = base.flatMap (fun a => (tuples base (J+1)).map (List.cons a)) := rfl
      _ = base.flatMap (fun a => ((tuples base J).flatMap
          (fun xs => base.map (fun b => xs++[b]))).map (List.cons a)) := by rw [ih]
      _ = (base.flatMap (fun a => (tuples base J).map (List.cons a))).flatMap
          (fun xs => base.map (fun a => xs++[a])) := by
        simp only [List.map_flatMap,List.flatMap_assoc,List.flatMap_map,List.map_map,Function.comp_def,
          List.cons_append]
      _ = _ := rfl

def indices (m : ℕ) : ℕ → ℕ → List ℕ
  | 0,_ => []
  | J+1,k => indices m J (k/m)++[k%m]

theorem indices_length (m J k : ℕ) : (indices m J k).length=J := by
  induction J generalizing k with
  | zero => rfl
  | succ J ih => simp [indices,ih]

theorem indices_lt {m : ℕ} (hm : 0 < m) (J k : ℕ) :
    ∀ a ∈ indices m J k, a < m := by
  induction J generalizing k with
  | zero => simp [indices]
  | succ J ih =>
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact ih _ a ha
    · have he : a=k%m := by simpa using ha
      subst a
      exact Nat.mod_lt _ hm

theorem indices_getD_lt {m J k j : ℕ} (hm : 0 < m) (hj : j < J) :
    (indices m J k).getD j 0 < m := by
  rw [List.getD_eq_getElem _ _ (by rw [indices_length]; exact hj)]
  exact indices_lt hm J k _ (List.getElem_mem _)

theorem indices_getD_reverse (m J k : ℕ) {j : ℕ} (hj : j < J) :
    (indices m J k).getD (J-1-j) 0 = (k/m^j)%m := by
  induction J generalizing k j with
  | zero => omega
  | succ J ih =>
    cases j with
    | zero =>
      have hlen := indices_length m J (k/m)
      simp only [indices,Nat.succ_eq_add_one,Nat.add_sub_cancel,Nat.sub_zero,pow_zero,Nat.div_one]
      rw [List.getD_append_right _ _ _ _ (by omega),hlen,Nat.sub_self]
      rfl
    | succ j =>
      have hj' : j < J := by omega
      have he : J+1-1-(j+1)=J-1-j := by omega
      simp only [indices,Nat.succ_eq_add_one]
      rw [he,List.getD_append _ _ _ _ (by rw [indices_length]; omega),ih (k/m) hj']
      rw [Nat.div_div_eq_div_mul,pow_succ']

theorem tuples_getD_indices (base : List α) (da : α) (hm : 0 < base.length)
    (J k : ℕ) (hk : k < base.length^J) :
    (tuples base J).getD k [] = (indices base.length J k).map (fun i => base.getD i da) := by
  induction J generalizing k with
  | zero =>
    have hk0 : k=0 := by simpa using hk
    subst k
    rfl
  | succ J ih =>
    have hq : k/base.length < base.length^J :=
      (Nat.div_lt_iff_lt_mul hm).mpr (by simpa only [pow_succ] using hk)
    have hr : k%base.length < base.length := Nat.mod_lt _ hm
    have hi : k/base.length < (tuples base J).length := by rwa [tuples_length]
    have hidx : k/base.length*base.length+k%base.length=k := by
      simpa only [Nat.mul_comm] using Nat.div_add_mod k base.length
    conv_lhs => rw [tuples_succ_right,← hidx]
    rw [getD_flatMap_uniform _ _ base.length (by simp) [] [] hi hr]
    rw [List.getD_map_of_lt _ hr da []]
    rw [ih _ hq]
    simp only [indices,List.map_append,List.map_cons,List.map_nil]

end ThreeSum.OutputDecodeOrder
