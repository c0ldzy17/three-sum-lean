import Submission.ThreeSum.LightLocalKeyRow

/-!
# Complete occurrence-by-output local key array

The loop reads the two stored coefficient rows for each schedule occurrence,
constructs every signed local output key, and copies that row into the final
contiguous array. It reuses the row scratch and preserves earlier rows.
-/

namespace ThreeSum.LightLocalKeys

open Light

set_option maxHeartbeats 2500000
set_option maxRecDepth 10000

/-- Width, masks, masks per row, packed coefficient rows, occurrences, output, free. -/
def body (pRow pCopy : ℕ) : Stmt :=
  .for 7 (v 4) (
    .call pRow [v 0,v 1,v 2,v 3 +' v 7 *' (k 2 *' v 0),
      v 3 +' v 7 *' (k 2 *' v 0) +' v 0,v 6] 8 ;;
    .call pCopy [v 8,v 5 +' v 7 *' v 2,v 2] 9)

def time (L n rows : ℕ) : ℕ := rows*(LightLocalKeyRow.time L n+copyTime n+130)+20
def word (L U rows : ℕ) : ℕ := LightLocalKeyRow.word L U+rows+2*L+1

def Inv (μ : ℕ → ℤ) (L masks n maps rows dst free : ℕ)
    (mask : ℕ → ℕ) (wFalse wTrue : ℕ → ℕ → ℕ) (j : ℕ) (σ : State) : Prop :=
  ∃ (r s : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [L,masks,n,maps,rows,dst,free,j,r,s],ν⟩ ∧
    (∀ k < j, ∀ i < n, ν (dst+k*n+i)=
      (OneHotMask.eval (wTrue k) (fun _ => 0) L (mask i) : ℤ)-
      (OneHotMask.eval (wFalse k) (fun _ => 0) L (mask i) : ℤ)) ∧ Kept μ ν dst

structure Procs (P : Program) (pMain : ℕ) where
  pRow : ℕ
  pCopy : ℕ
  main : P[pMain]? = some (body pRow pCopy)
  row : LightLocalKeyRow.Procs P pRow
  copy : P[pCopy]? = some copyBody

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {L masks n maps rows dst free U : ℕ}
    (mask : ℕ → ℕ) (wFalse wTrue : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+3 ≤ lim.depth)
    (hspace : LightLocalKeyRow.space free L n ≤ lim.space)
    (hmasks : masks+n ≤ dst) (hmaps : maps+rows*(2*L) ≤ dst) (hdst : dst+rows*n ≤ free)
    (hword : (word L U rows : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < n, μ (masks+i)=(mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^L)
    (hreadFalse : ∀ j < rows, ∀ i < L, μ (maps+j*(2*L)+i)=(wFalse j i : ℤ))
    (hreadTrue : ∀ j < rows, ∀ i < L, μ (maps+j*(2*L)+L+i)=(wTrue j i : ℤ))
    (hboundFalse : ∀ j < rows, ∀ i < L, wFalse j i ≤ U)
    (hboundTrue : ∀ j < rows, ∀ i < L, wTrue j i ≤ U) :
    Meets lim P pMain d [L,masks,n,maps,rows,dst,free] μ (time L n rows)
      (fun _ ν =>
        (∀ j < rows, ∀ i < n, ν (dst+j*n+i)=
          (OneHotMask.eval (wTrue j) (fun _ => 0) L (mask i) : ℤ)-
          (OneHotMask.eval (wFalse j) (fun _ => 0) L (mask i) : ℤ)) ∧ Kept μ ν dst) := by
  have hs : free+L+2*n+(L+1) ≤ lim.space := hspace
  have hrowWord : (LightLocalKeyRow.word L U : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show LightLocalKeyRow.word L U ≤ word L U rows by unfold word; omega)).trans hword
  have hrowsWord : (rows : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show rows ≤ word L U rows by unfold word; omega)).trans hword
  have hwidthWord : (2 : ℤ)*L ≤ lim.word := by
    have hh : 2*L ≤ word L U rows := by unfold word; omega
    exact (by exact_mod_cast hh : (2 : ℤ)*L ≤ (word L U rows : ℤ)).trans hword
  have htwoWord : (2 : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show 2 ≤ LightLocalKeyRow.word L U by
      unfold LightLocalKeyRow.word; omega)).trans hrowWord
  apply Meets.of_body S.main
  unfold body time
  refine Ends.for (Inv μ L masks n maps rows dst free mask wFalse wTrue) rows
    (LightLocalKeyRow.time L n+copyTime n+120) ?_ ?_ ?_ ?_
  · refine ⟨0,0,μ,?_,?_,by intro a ha; rfl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : State))
        ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 2).symm)
    · intro j hj; omega
  · rintro j _ hj _ ⟨r,s,ν,rfl,written,kept⟩
    have hmj := Nat.mul_le_mul_right (2*L) (show j+1 ≤ rows by omega)
    have hdj := Nat.mul_le_mul_right n (show j+1 ≤ rows by omega)
    simp only [Nat.add_mul,one_mul] at hmj hdj
    have hmProd : (j : ℤ)*(2*L : ℤ) ≤ lim.word := by
      have hh : j*(2*L) ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (j : ℤ)*(2*L : ℤ) ≤ lim.space).trans hw
    have hmNonnegative : (0 : ℤ) ≤ (j : ℤ)*(2*(L : ℤ)) := by positivity
    have hmAddr : (maps : ℤ)+(j : ℤ)*(2*L : ℤ)+L ≤ lim.word := by
      have hh : maps+j*(2*L)+L ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (maps : ℤ)+(j : ℤ)*(2*L : ℤ)+L ≤ lim.space).trans hw
    have hdProd : (j : ℤ)*n ≤ lim.word := by
      have hh : j*n ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (j : ℤ)*n ≤ lim.space).trans hw
    have hdAddr : (dst : ℤ)+(j : ℤ)*n ≤ lim.word := by
      have hh : dst+j*n ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (dst : ℤ)+(j : ℤ)*n ≤ lim.space).trans hw
    have hmRead (i : ℕ) (hi : i < n) : ν (masks+i)=(mask i : ℤ) :=
      (kept _ (by omega)).trans (hmaskRead i hi)
    have hfRead (i : ℕ) (hi : i < L) : ν (maps+j*(2*L)+i)=(wFalse j i : ℤ) :=
      (kept _ (by omega)).trans (hreadFalse j hj i hi)
    have htRead (i : ℕ) (hi : i < L) : ν (maps+j*(2*L)+L+i)=(wTrue j i : ℤ) :=
      (kept _ (by omega)).trans (hreadTrue j hj i hi)
    have hr := S.row.meets (d := d+1) (μ := ν) (L := L) (masks := masks) (n := n)
      (srcFalse := maps+j*(2*L)) (srcTrue := maps+j*(2*L)+L) (free := free) (U := U)
      mask (wFalse j) (wTrue j) hw (by omega) hspace (by omega) (by omega) (by omega)
      hrowWord hmRead hmaskLt hfRead htRead (hboundFalse j hj) (hboundTrue j hj)
    light_call hr using LightLocalKeyRow.time,LightMaskHashes.time,LightArray.linearTime
      with row μ₁ ⟨hrowPtr,hrow,hkeep₁⟩
    have hc := copy_meets (d := d+1) (μ := μ₁) (src := free+L)
      (dst := dst+j*n) (n := n) S.copy hw (by omega) (by omega) (Or.inr (by omega))
    light_call hc using hrowPtr,LightLocalKeyRow.time,LightMaskHashes.time,LightArray.linearTime
      with copied μ₂ ⟨hcopy,hkeep₂⟩
    refine ⟨by simp,row,copied,μ₂,by simp [update_frame_setLocal],?_,?_⟩
    · intro k hk i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · have hki := Nat.mul_le_mul_right n (show k+1 ≤ j by omega)
        simp only [Nat.add_mul,one_mul] at hki
        rw [hkeep₂ _ (Or.inl (by omega)),hkeep₁ _ (by omega)]
        exact written k hk i hi
      · rw [hcopy i hi,hrow i hi]
    · intro a ha
      rw [hkeep₂ _ (Or.inl (by omega)),hkeep₁ _ (by omega)]
      exact kept a ha
  · rintro _ _ ⟨r,s,ν,rfl,written,kept⟩
    exact ⟨written,kept⟩
  · rintro j _ hj _ ⟨r,s,ν,rfl,_,_⟩
    light_side

def program : Program := [body 1 7,LightLocalKeyRow.body 2 3 6,fillBody,
  LightMaskHashes.body 4 5,powTableBody,LightOneHot.body 5,
  LightArray.linearBody,copyBody]

def programProcs : Procs program 0 :=
  ⟨1,7,rfl,⟨2,3,4,5,6,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩

theorem time_bound (L n rows : ℕ) : time L n rows ≤ 1200*(L+1)*(n+1)*(rows+1) := by
  have hh := LightLocalKeyRow.time_bound L n
  have hper : LightLocalKeyRow.time L n+copyTime n+130 ≤ 1100*(L+1)*(n+1) := by
    unfold copyTime
    nlinarith
  have hm := Nat.mul_le_mul_left rows hper
  have he : 1200*(L+1)*(n+1)*(rows+1) = rows*(1100*(L+1)*(n+1))+20+
      (100*rows*(L+1)*(n+1)+1200*L*n+1200*L+1200*n+1180) := by ring
  unfold time
  rw [he]
  omega

end ThreeSum.LightLocalKeys
