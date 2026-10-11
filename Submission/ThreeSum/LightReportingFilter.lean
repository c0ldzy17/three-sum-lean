import Submission.ThreeSum.LightReportingAffine

/-!
# Actual positive-query filtering for a reporting frontier

The scan writes exactly the indices of positive stored query counts, in input
order. Its cost is linear in the candidate count, and original input arrays
are preserved. It does not recompute or assume the query implementation.
-/

namespace ThreeSum.LightReportingFilter

open Light

variable {lim : Limits} {P : Program}

def selected (count : ℕ → ℕ) (j : ℕ) : List ℕ :=
  (List.range j).filter fun i => 0 < count i

@[simp] theorem selected_zero (count : ℕ → ℕ) : selected count 0 = [] := by
  simp [selected]

theorem selected_length_le (count : ℕ → ℕ) (j : ℕ) : (selected count j).length ≤ j := by
  exact (List.length_filter_le _ _).trans_eq List.length_range

theorem selected_succ_pos (count : ℕ → ℕ) (j : ℕ) (hj : 0 < count j) :
    selected count (j+1) = selected count j ++ [j] := by
  simp [selected,List.range_succ,List.filter_append,hj]

theorem selected_succ_zero (count : ℕ → ℕ) (j : ℕ) (hj : count j = 0) :
    selected count (j+1) = selected count j := by
  simp [selected,List.range_succ,List.filter_append,hj]

@[simp] theorem mem_selected (count : ℕ → ℕ) (j i : ℕ) :
    i ∈ selected count j ↔ i < j ∧ 0 < count i := by
  simp [selected]

theorem selected_nodup (count : ℕ → ℕ) (j : ℕ) : (selected count j).Nodup :=
  List.nodup_range.filter _

def roundBody : Stmt :=
  .ite (k 0 <' M (v 1 +' v 4))
    (.store (v 2 +' v 3) (v 4) ;; .set 3 (v 3 +' k 1))
    .skip

/-- Number of candidates, stored query counts, selected-index output. -/
def body : Stmt :=
  .set 3 (k 0) ;;
  .for 4 (v 0) roundBody ;;
  .set 0 (v 3)

def time (n : ℕ) : ℕ := 100*n+40

def Inv (μ : ℕ → ℤ) (count : ℕ → ℕ) (n src dst j : ℕ) (σ : State) : Prop :=
  ∃ μ' : ℕ → ℤ,
    σ = ⟨frame [n,src,dst,(selected count j).length,j],μ'⟩ ∧
    SegN μ' dst (selected count j) ∧ SameOutside μ μ' dst n

theorem meets {p n src dst d : ℕ} {μ : ℕ → ℤ} (count : ℕ → ℕ)
    (hp : P[p]? = some body)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+n ≤ lim.space) (hdst : dst+n ≤ lim.space)
    (hsep : Apart src n dst n)
    (hword : ∀ i < n, (count i : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src+i) = (count i : ℤ)) :
    Meets lim P p d [n,src,dst] μ (time n)
      (fun r μ' => r = ((selected count n).length : ℤ) ∧
        SegN μ' dst (selected count n) ∧ SameOutside μ μ' dst n) := by
  have hzero : (0 : ℤ) ≤ lim.word := le_trans (by positivity) hw
  apply Meets.of_body hp
  unfold body time
  light_set (0 : ℕ)
  refine Ends.pieceThen (Ends.for (lim := lim) (P := P) (d := d) (i := 4) (hi := v 0) (body := roundBody)
    (T := 100*n+20) (Q := Inv μ count n src dst n)
    (Inv μ count n src dst) n 80 ?start ?round ?done ?bound (hT := by light_time)) ?after
  case start =>
    refine ⟨μ,?_,by simp [SegN],SameOutside.refl⟩
    simp [update_frame_setLocal]
  case round =>
    rintro j _ hj _ ⟨μ',rfl,hseg,hkeep⟩
    have hlen := selected_length_le count j
    have hreadj : μ' (src+j) = (count j : ℤ) := by
      rw [hkeep (src+j) (by omega),hread j hj]
    have hcword := hword j hj
    unfold roundBody
    light_if hpos hnot : (0 : ℤ) < (count j : ℤ) using hreadj
    · have hposN : 0 < count j := by exact_mod_cast hpos
      have hnext := selected_succ_pos count j hposN
      light_store (dst+(selected count j).length) (j : ℕ)
      light_set ((selected count j).length+1 : ℕ)
      refine ⟨by simp,Function.update μ' (dst+(selected count j).length) (j : ℤ),?_,?_,?_⟩
      · simp [update_frame_setLocal,hnext]
      · rw [hnext]
        exact SegN.snoc hseg j
      · exact hkeep.update ⟨by omega,by omega⟩ j
    · have hzeroN : count j = 0 := by omega
      have hnext := selected_succ_zero count j hzeroN
      light_skip
      exact ⟨by simp,μ',by simp [update_frame_setLocal,hnext],hnext ▸ hseg,hkeep⟩
  case done =>
    intro σ _ hh
    exact hh
  case bound =>
    rintro j _ hj _ ⟨μ',rfl,_,_⟩
    light_side
  case after =>
    rintro _ ⟨μ',rfl,hseg,hkeep⟩
    have hlen := selected_length_le count n
    light_set ((selected count n).length : ℕ)
    exact ⟨by simp,hseg,hkeep⟩

def program : Program := [body]

theorem program_meets {n src dst d : ℕ} {μ : ℕ → ℤ} (count : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+n ≤ lim.space) (hdst : dst+n ≤ lim.space)
    (hsep : Apart src n dst n)
    (hword : ∀ i < n, (count i : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src+i) = (count i : ℤ)) :
    Meets lim program 0 d [n,src,dst] μ (time n)
      (fun r μ' => r = ((selected count n).length : ℤ) ∧
        SegN μ' dst (selected count n) ∧ SameOutside μ μ' dst n) :=
  meets count rfl hw hsrc hdst hsep hword hread

end ThreeSum.LightReportingFilter
