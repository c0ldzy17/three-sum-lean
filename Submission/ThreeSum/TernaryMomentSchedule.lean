import Submission.ThreeSum.TernaryWeightChannels

/-! A finite, fixed-degree binomial channel schedule and its exact sums. -/
namespace ThreeSum.TernaryMomentSchedule
open Finset TernaryJointType
open scoped BigOperators

def row (k : ℕ) : List (ℕ×ℕ) := (List.range (k+1)).map (fun j => (k,j))

def channels : ℕ→List (ℕ×ℕ)
  | 0 => []
  | t+1 => channels t++row t

def aggregate (xs : List (ℕ×ℕ)) (score : ℕ→ℕ→ℕ→ℤ) (k i : ℕ) : ℤ :=
  (xs.map (fun c => if c.1=k then score c.1 c.2 i else 0)).sum

@[simp] theorem aggregate_nil (score : ℕ→ℕ→ℕ→ℤ) (k i : ℕ) :
    aggregate [] score k i=0 := rfl

@[simp] theorem aggregate_cons (c : ℕ×ℕ) (xs : List (ℕ×ℕ))
    (score : ℕ→ℕ→ℕ→ℤ) (k i : ℕ) :
    aggregate (c::xs) score k i=
      (if c.1=k then score c.1 c.2 i else 0)+aggregate xs score k i := rfl

@[simp] theorem aggregate_append (xs ys : List (ℕ×ℕ))
    (score : ℕ→ℕ→ℕ→ℤ) (k i : ℕ) :
    aggregate (xs++ys) score k i=aggregate xs score k i+aggregate ys score k i := by
  simp [aggregate,List.map_append]

theorem aggregate_row (score : ℕ→ℕ→ℕ→ℤ) (l k i : ℕ) :
    aggregate (row l) score k i=
      if l=k then ∑ j∈range (l+1), score l j i else 0 := by
  classical
  by_cases h : l=k
  · subst k
    simp only [aggregate,row,List.map_map,Function.comp_def,if_pos rfl,ite_true]
    simpa only [List.toFinset_range] using
      (List.sum_toFinset (fun j => score l j i) (List.nodup_range (n := l+1))).symm
  · simp [aggregate,row,List.map_map,Function.comp_def,h]

theorem channel_rows (terms k i : ℕ) (score : ℕ→ℕ→ℕ→ℤ) :
    aggregate (channels terms) score k i=
      if k<terms then ∑ j∈range (k+1), score k j i else 0 := by
  classical
  induction terms with
  | zero => simp [channels]
  | succ t ih =>
    rw [channels,aggregate_append,ih,aggregate_row]
    by_cases hkt : k<t
    · have hne : t≠k := by omega
      simp [hkt,hne,show k<t+1 by omega]
    · by_cases hke : k=t
      · subst k; simp
      · have hne : t≠k := by omega
        simp [hkt,hne,show ¬k<t+1 by omega]

theorem mem_channels {terms k j : ℕ} :
    (k,j)∈channels terms ↔ k<terms ∧ j≤k := by
  induction terms with
  | zero => simp [channels]
  | succ t ih =>
    simp only [channels,List.mem_append,ih,row,List.mem_map,List.mem_range,Prod.mk.injEq]
    constructor
    · rintro (⟨hk,hj⟩ | ⟨l,hl,hk,hj⟩)
      · exact ⟨by omega,hj⟩
      · subst k; subst l; exact ⟨by omega,by omega⟩
    · rintro ⟨hk,hj⟩
      by_cases hkt : k<t
      · exact Or.inl ⟨hkt,hj⟩
      · have hke : k=t := by omega
        subst k
        exact Or.inr ⟨j,by omega,rfl,rfl⟩

theorem length_le (terms : ℕ) : (channels terms).length≤terms^2 := by
  induction terms with
  | zero => simp [channels]
  | succ t ih =>
    simp only [channels,List.length_append,row,List.length_map,List.length_range]
    nlinarith

theorem scaled_physical_moments {ι κ : Type*} {N : ℕ}
    (S : Finset ι) (T : Finset κ) (left : ι→TritWord N) (right : κ→TritWord N)
    (B : ι→ℤ) (C : κ→ℤ) (Q : ℕ→TritWord N) (scale : ℕ→ℤ)
    (terms k i : ℕ) (hk : k<terms) :
    aggregate (channels terms)
      (fun k j i => scale i*TernaryConvolution.convolution
        (TernaryWeightedPhysicalSources.histogram S left
          (fun b => (TernaryWeightChannels.leftMoment k j).eval (fun _ => B b)))
        (TernaryWeightedPhysicalSources.histogram T right
          (fun c => (TernaryWeightChannels.rightMoment k j).eval (fun _ => C c))) (Q i)) k i=
      scale i*∑ b∈S, ∑ c∈T,
        if TernaryConvolution.Adds (left b) (right c) (Q i) then (C c-B b)^k else 0 := by
  rw [channel_rows,if_pos hk,← mul_sum]
  exact congrArg (fun x : ℤ => scale i*x)
    (TernaryWeightChannels.convolution_moment_channels S T left right B C (Q i) k)

end ThreeSum.TernaryMomentSchedule
