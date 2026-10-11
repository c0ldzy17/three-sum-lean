import Submission.ThreeSum.LightReportingPairRows

/-! # The constructed local pair arrays are aligned segments in one exact record order -/

namespace ThreeSum.ReportingHostPairSegments

open Light ThreeSum.SubsetAddress ReportingHostPairEnumeration

set_option linter.unusedSimpArgs false

variable {α β : Type*}

theorem seg_flatMap_uniform {μ : ℕ → ℤ} {dst n : ℕ} (xs : List α) (f : α → List ℤ)
    (hlen : ∀ x ∈ xs, (f x).length = n)
    (hout : ∀ i (hi : i < xs.length), ∀ j (hj : j < n),
      μ (dst+i*n+j) = (f xs[i])[j]'(by rw [hlen _ (List.getElem_mem hi)]; exact hj)) :
    Seg μ dst (xs.flatMap f) := by
  induction xs generalizing dst with
  | nil => simp [Seg,SegN]
  | cons x xs ih =>
    rw [List.flatMap_cons]
    apply seg_append.mpr
    constructor
    · intro j hj
      have hn : j < n := by rw [← hlen x (by simp)]; exact hj
      have hh := hout 0 (by simp) j hn
      simp only [Nat.zero_mul,Nat.add_zero] at hh
      change μ (dst+j) = (f x)[j] at hh
      exact hh
    · rw [hlen x (by simp)]
      apply ih (by intro a ha; exact hlen a (by simp [ha]))
      intro i hi j hj
      have hh := hout (i+1) (by simpa using hi) j hj
      simpa only [List.getElem_cons_succ,Nat.add_mul,Nat.one_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
        using hh

def leftMasks (L h : ℕ) : List ℤ := (pairs L h).map fun p => (subsetMask p.1 : ℤ)
def rightMasks (L h : ℕ) : List ℤ := (pairs L h).map fun p => (subsetMask p.2 : ℤ)

@[simp] theorem leftMasks_length (L h : ℕ) : (leftMasks L h).length = L.choose (2*h)*(2*h).choose h := by
  simp [leftMasks,pairs_length]

@[simp] theorem rightMasks_length (L h : ℕ) : (rightMasks L h).length = L.choose (2*h)*(2*h).choose h := by
  simp [rightMasks,pairs_length]

theorem leftMasks_bounded (L h : ℕ) : ∀ x ∈ leftMasks L h, |x| ≤ ((2^L : ℕ) : ℤ) := by
  intro x hx
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
  rw [Int.abs_natCast]
  exact Int.ofNat_le.mpr (Nat.le_of_lt (subsetMask_isMask p.1).1)

theorem rightMasks_bounded (L h : ℕ) : ∀ x ∈ rightMasks L h, |x| ≤ ((2^L : ℕ) : ℤ) := by
  intro x hx
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
  rw [Int.abs_natCast]
  exact Int.ofNat_le.mpr (Nat.le_of_lt (subsetMask_isMask p.2).1)

theorem leftMasks_of_rows {μ : ℕ → ℤ} {L h dst : ℕ}
    (hout : ∀ i < L.choose h, ∀ j < (L-h).choose h,
      μ (dst+i*(L-h).choose h+j) = (subsetMask (leftAt L h i) : ℤ)) :
    Seg μ dst (leftMasks L h) := by
  unfold leftMasks pairs
  rw [List.map_flatMap]
  simp only [List.map_map,Function.comp_def]
  apply seg_flatMap_uniform (n := (L-h).choose h) (lefts L h)
    (fun S => (rights S h).map (fun _ => (subsetMask S : ℤ)))
    (by intro S hS; simpa using rights_length S ((lefts_mem S).mp hS))
  intro i hi j hj
  have hin : i < L.choose h := by simpa using hi
  have hh := hout i hin j hj
  simpa only [List.getElem_map,leftAt_eq_get hin] using hh

theorem rightMasks_of_rows {μ : ℕ → ℤ} {L h dst : ℕ}
    (hout : ∀ i < L.choose h, ∀ j < (L-h).choose h,
      μ (dst+i*(L-h).choose h+j) = (subsetMask (rightAt L h i j) : ℤ)) :
    Seg μ dst (rightMasks L h) := by
  unfold rightMasks pairs
  rw [List.map_flatMap]
  simp only [List.map_map,Function.comp_def]
  apply seg_flatMap_uniform (n := (L-h).choose h) (lefts L h)
    (fun S => (rights S h).map (fun R => (subsetMask R : ℤ)))
    (by intro S hS; simpa using rights_length S ((lefts_mem S).mp hS))
  intro i hi j hj
  have hin : i < L.choose h := by simpa using hi
  have hh := hout i hin j hj
  simpa only [List.getElem_map,rightAt_eq_get hin hj,leftAt_eq_get hin] using hh

theorem program_meets {lim : Limits} {μ : ℕ → ℤ} {L h srcS dstL dstR work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hh : 2*h ≤ L)
    (hS : srcS+L.choose h ≤ dstL)
    (hL : dstL+L.choose h*(L-h).choose h ≤ dstR)
    (hR : dstR+L.choose h*(L-h).choose h ≤ work)
    (hspace : work+2*L+2 ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+L+3 ≤ lim.depth) :
    Meets lim LightReportingPairRows.program 7 d [L,h,srcS,dstL,dstR,work]
      μ (LightReportingPairRows.time L h)
      (fun r μ' => r = (L.choose (2*h)*(2*h).choose h : ℤ) ∧
        Seg μ' dstL (leftMasks L h) ∧ Seg μ' dstR (rightMasks L h) ∧ Kept μ μ' srcS) := by
  apply (LightReportingPairRows.program_meets hw hh hS hL hR hspace hword hd).mono le_rfl
  rintro r μ' ⟨hr,_,hout,hkeep⟩
  exact ⟨hr,leftMasks_of_rows (by intro i hi j hj; exact (hout i hi j hj).1),
    rightMasks_of_rows (by intro i hi j hj; exact (hout i hi j hj).2),hkeep⟩

end ThreeSum.ReportingHostPairSegments
