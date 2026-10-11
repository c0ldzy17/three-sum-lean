import Submission.ThreeSum.LightArray

/-!
# Gathering selected coefficient rows

The selection array contains ordinary candidate indices. This fixed program
reads each selected index and copies its whole coefficient row into the
corresponding schedule occurrence. Repeated selections are retained.
-/

namespace ThreeSum.LightWeightGather

open Light

set_option maxHeartbeats 1000000

def body (pCopy : ℕ) : Stmt :=
  .for 5 (v 3) (
    .set 6 (M (v 0 +' v 5)) ;;
    .call pCopy [v 1 +' v 6 *' v 4,v 2 +' v 5 *' v 4,v 4] 7)

def time (rows width : ℕ) : ℕ := rows*(copyTime width+100)+6
def word (N rows width : ℕ) : ℕ := N+rows+width+1

def Inv (μ : ℕ → ℤ) (indices src dst rows width : ℕ) (select : ℕ → ℕ)
    (i : ℕ) (σ : State) : Prop :=
  ∃ (x r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [indices,src,dst,rows,width,i,x,r],μ'⟩ ∧
    (∀ j < i, ∀ a < width, μ' (dst+j*width+a) = μ (src+select j*width+a)) ∧
    SameOutside μ μ' dst (rows*width)

structure Procs (P : Program) (pMain : ℕ) where
  pCopy : ℕ
  copy : P[pCopy]? = some copyBody
  main : P[pMain]? = some (body pCopy)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {indices src dst N rows width : ℕ} (select : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hindices : indices+rows ≤ dst) (hsrc : src+N*width ≤ dst)
    (hspace : dst+rows*width ≤ lim.space)
    (hword : (word N rows width : ℤ) ≤ lim.word)
    (hselect : ∀ i < rows, select i < N)
    (hread : ∀ i < rows, μ (indices+i) = (select i : ℤ)) :
    Meets lim P pMain d [indices,src,dst,rows,width] μ (time rows width)
      (fun _ μ' =>
        (∀ i < rows, ∀ a < width, μ' (dst+i*width+a) = μ (src+select i*width+a)) ∧
        SameOutside μ μ' dst (rows*width)) := by
  have hbudget (x : ℕ) (hx : x ≤ word N rows width) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hNWord := hbudget N (by unfold word; omega)
  have hrowsWord := hbudget rows (by unfold word; omega)
  have hwidthWord := hbudget width (by unfold word; omega)
  have h1Word := hbudget 1 (by unfold word; omega)
  apply Meets.of_body S.main
  unfold body time
  refine Ends.for (Inv μ indices src dst rows width select) rows
    (copyTime width+92) ?_ ?_ ?_ ?_
  · refine ⟨0,0,μ,?_,?_,SameOutside.refl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : State))
        ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 2).symm)
    · intro j hj; omega
  · rintro i _ hi _ ⟨x,r,μ',rfl,written,kept⟩
    have hs := hselect i hi
    have hsi := Nat.mul_le_mul_right width (show select i+1 ≤ N by omega)
    have hdi := Nat.mul_le_mul_right width (show i+1 ≤ rows by omega)
    simp only [Nat.add_mul,one_mul] at hsi hdi
    have hsource : src+select i*width+width ≤ dst := by omega
    have hdest : dst+i*width+width ≤ lim.space := by omega
    have hselWord : (select i : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (Nat.le_of_lt hs)).trans hNWord
    have hmulSrc : (select i : ℤ)*width ≤ lim.word := by
      have h : select i*width ≤ lim.space := by omega
      exact (by exact_mod_cast h : (select i : ℤ)*width ≤ (lim.space : ℤ)).trans hw
    have hmulDst : (i : ℤ)*width ≤ lim.word := by
      have h : i*width ≤ lim.space := by omega
      exact (by exact_mod_cast h : (i : ℤ)*width ≤ (lim.space : ℤ)).trans hw
    have hr : μ' (indices+i) = (select i : ℤ) := by
      rw [kept _ (Or.inl (by omega))]
      exact hread i hi
    have hsourceAddr : ((src : ℤ)+(select i : ℤ)*width).toNat = src+select i*width := by
      norm_cast
    have hdestAddr : ((dst : ℤ)+(i : ℤ)*width).toNat = dst+i*width := by norm_cast
    light_set (select i : ℕ) using hr
    have hcall := copy_meets (d := d+1) (μ := μ')
      (src := src+select i*width) (dst := dst+i*width) (n := width)
      S.copy hw (by omega) hdest (Or.inl (by omega))
    light_call hcall using hsourceAddr,hdestAddr with value μ₁ ⟨hcopied,hkept⟩
    refine ⟨by simp,select i,value,μ₁,by simp [update_frame_setLocal],?_,?_⟩
    · intro j hj a ha
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · have hjm := Nat.mul_le_mul_right width (show j+1 ≤ i by omega)
        simp only [Nat.add_mul,one_mul] at hjm
        rw [hkept _ (Or.inl (by omega))]
        exact written j hj a ha
      · rw [hcopied a ha,kept _ (Or.inl (by omega))]
    · intro a ha
      rw [hkept a (by unfold Outside at *; omega)]
      exact kept a ha
  · rintro _ _ ⟨x,r,μ',rfl,written,kept⟩
    exact ⟨written,kept⟩
  · rintro i _ _ _ ⟨x,r,μ',rfl,_,_⟩
    light_side

def program : Program := [body 1,copyBody]

def programProcs : Procs program 0 := ⟨1,rfl,rfl⟩

theorem time_bound (rows width : ℕ) :
    time rows width ≤ 130*(rows+1)*(width+1) := by
  unfold time copyTime
  nlinarith

end ThreeSum.LightWeightGather
