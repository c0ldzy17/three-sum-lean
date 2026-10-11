import Submission.ThreeSum.LightCoverSelect
import Submission.ThreeSum.LightCoverUpdate
import Submission.ThreeSum.BooleanGreedy

/-!
# An actual exhaustive finite greedy-cover program

The candidate matrix is read-only. The routine initializes active targets,
computes every candidate score, chooses the first maximum, stores the
chosen index, and removes its covered targets. Its output is exactly the
pre-existing `Cover.greedyChoices` list, including repeated occurrences.
-/

namespace ThreeSum.LightCoverGreedy

open Light BooleanGreedy

set_option maxHeartbeats 1200000
set_option maxRecDepth 5000

def out (activePtr rows cols : ℕ) : ℕ := activePtr+cols+rows

def total (rows cols rounds : ℕ) : ℕ := cols+rows+rounds

def roundBody (pSelect pUpdate : ℕ) : Stmt :=
  .call pSelect [v 0,v 1,v 5,v 2,v 3] 8 ;;
  .store (v 6 +' v 7) (v 8) ;;
  .call pUpdate [v 0 +' v 8 *' v 3,v 1,v 3] 9

def body (pFill pSelect pUpdate : ℕ) : Stmt :=
  .set 5 (v 1 +' v 3) ;;
  .set 6 (v 5 +' v 2) ;;
  .call pFill [v 1,v 3,k 1] 9 ;;
  .for 7 (v 4) (roundBody pSelect pUpdate) ;;
  .set 0 (v 6)

def roundTime (rows cols : ℕ) : ℕ :=
  LightCoverSelect.time rows cols+LightCoverUpdate.time cols+200

def time (rows cols rounds : ℕ) : ℕ :=
  fillTime cols+rounds*(roundTime rows cols+8)+100

def Inv (μ : ℕ → ℤ) (matrix : ℕ → ℕ → ℕ)
    (src activePtr rows cols rounds i : ℕ) (σ : State) : Prop :=
  ∃ (r v : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [src,activePtr,rows,cols,rounds,activePtr+cols,out activePtr rows cols,i,r,v],μ'⟩ ∧
    (∀ j < cols, μ' (activePtr+j) = (active matrix rows cols i j : ℤ)) ∧
    Seg μ' (out activePtr rows cols) ((choices matrix rows cols i).map (fun x : ℕ => (x : ℤ))) ∧
    SameOutside μ μ' activePtr (total rows cols rounds)

structure Procs (P : Program) (pMain : ℕ) where
  pFill : ℕ
  pSelect : ℕ
  pUpdate : ℕ
  fill : P[pFill]? = some fillBody
  select : LightCoverSelect.Procs P pSelect
  update : P[pUpdate]? = some LightCoverUpdate.body
  main : P[pMain]? = some (body pFill pSelect pUpdate)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {src activePtr rows cols rounds : ℕ}
    (matrix : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hrows : 0 < rows)
    (hsrc : src+rows*cols ≤ activePtr)
    (hspace : activePtr+total rows cols rounds ≤ lim.space)
    (hread : ∀ i < rows, ∀ j < cols, μ (src+i*cols+j) = (matrix i j : ℤ))
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim P pMain d [src,activePtr,rows,cols,rounds] μ (time rows cols rounds)
      (fun r μ' => r = (out activePtr rows cols : ℤ) ∧
        Seg μ' (out activePtr rows cols) ((choices matrix rows cols rounds).map (fun x : ℕ => (x : ℤ))) ∧
        (∀ j < cols, μ' (activePtr+j) = (active matrix rows cols rounds j : ℤ)) ∧
        SameOutside μ μ' activePtr (total rows cols rounds)) := by
  have hspace' : activePtr+cols+rows+rounds ≤ lim.space := by simpa [total,Nat.add_assoc] using hspace
  have hworkSpace : activePtr+cols+rows ≤ lim.space := by omega
  have hactiveSpace : activePtr+cols ≤ lim.space := by omega
  have houtSpace : out activePtr rows cols+rounds ≤ lim.space := by simpa [out] using hspace'
  apply Meets.of_body S.main
  unfold body time
  light_set (activePtr+cols : ℕ) using out,roundTime
  light_set (out activePtr rows cols : ℕ) using out,roundTime
  light_call (fill_meets (d := d+1) (μ := μ) (dst := activePtr) (n := cols) (x := 1)
    S.fill hw hactiveSpace) using out,roundTime
    with vf μ₁ ⟨hfill,hkept⟩
  refine Ends.pieceThen (Ends.for (T := rounds*(roundTime rows cols+8)+6)
    (Q := fun σ => Inv μ matrix src activePtr rows cols rounds rounds σ)
    (Inv μ matrix src activePtr rows cols rounds) rounds (roundTime rows cols)
    ?_ ?_ ?_ ?_ (hT := by light_time [roundTime])) ?_
  · refine ⟨0,vf,μ₁,?_,?_,?_,?_⟩
    · simp [Inv,update_frame_setLocal,out]
    · intro j hj
      rw [active_zero hj]
      exact (hfill j (by simpa using hj)).trans (List.getElem_replicate ..)
    · simp [choices,Cover.greedyChoices]
    · exact hkept.mono le_rfl (by unfold total; omega)
  · rintro i _ hi _ ⟨r,v,μ',rfl,hactive,written,kept⟩
    have hmread : ∀ a < rows, ∀ j < cols, μ' (src+a*cols+j) = (matrix a j : ℤ) := by
      intro a ha j hj
      have hm : (a+1)*cols ≤ rows*cols := Nat.mul_le_mul_right cols (by omega)
      have haddr : src+a*cols+j < activePtr := by nlinarith
      rw [kept _ (Or.inl haddr)]
      exact hread a ha j hj
    have hchoice := choice_lt (matrix := matrix) (cols := cols) hrows i
    have hcWord : (choice matrix rows cols i : ℤ) ≤ lim.word := by
      have hh : choice matrix rows cols i ≤ lim.space := by omega
      exact (Int.ofNat_le.mpr hh).trans hw
    unfold roundBody
    have hs := S.select.meets (d := d+1) (μ := μ')
      (src := src) (activePtr := activePtr) (work := activePtr+cols) (rows := rows) (cols := cols)
      matrix (active matrix rows cols i) hw (by omega) hrows (by omega) le_rfl
      hworkSpace hmread hactive hmatrix (fun j _ => active_le matrix rows cols i j) hword
    light_call hs using roundTime,LightCoverSelect.time,LightCoverScores.time,LightBooleanDot.time,
      LightCoverUpdate.time,LightMinimum.time,out with selected μ₂ ⟨hselected,hkeep₂⟩
    have hselected' : selected = (choice matrix rows cols i : ℤ) := by
      rw [hselected,choice_eq_least hrows hmatrix i]
    have hactive₂ : ∀ j < cols, μ₂ (activePtr+j) = (active matrix rows cols i j : ℤ) := by
      intro j hj
      rw [hkeep₂ _ (Or.inl (by omega))]
      exact hactive j hj
    have hwritten₂ : Seg μ₂ (out activePtr rows cols)
        ((choices matrix rows cols i).map (fun x : ℕ => (x : ℤ))) :=
      written.of_sameOutside hkeep₂ (Or.inr (by unfold out; omega))
    have hkeep₂full : SameOutside μ μ₂ activePtr (total rows cols rounds) := by
      intro a ha
      rw [hkeep₂ _ (by unfold total at ha; omega)]
      exact kept a ha
    light_store (out activePtr rows cols+i) (choice matrix rows cols i : ℕ)
      using hselected',roundTime,LightCoverSelect.time,LightCoverScores.time,LightBooleanDot.time,
        LightCoverUpdate.time,LightMinimum.time,out
    let μ₃ := Function.update μ₂ (out activePtr rows cols+i) (choice matrix rows cols i : ℤ)
    have hchoices₃ : Seg μ₃ (out activePtr rows cols)
        ((choices matrix rows cols (i+1)).map (fun x : ℕ => (x : ℤ))) := by
      have hh := hwritten₂.snoc (choice matrix rows cols i : ℤ)
      simpa [choices_succ,List.map_append,List.map_singleton,choices_length,μ₃] using hh
    have hactive₃ : ∀ j < cols, μ₃ (activePtr+j) = (active matrix rows cols i j : ℤ) := by
      intro j hj
      rw [show μ₃ (activePtr+j) = μ₂ (activePtr+j) by
        unfold μ₃; rw [Function.update_of_ne (by unfold out; omega)]]
      exact hactive₂ j hj
    have hkeep₃ : SameOutside μ μ₃ activePtr (total rows cols rounds) :=
      hkeep₂full.update ⟨by unfold out; omega,by unfold out total; omega⟩ _
    have hmul : (choice matrix rows cols i+1)*cols ≤ rows*cols := Nat.mul_le_mul_right cols (by omega)
    have hrow : src+choice matrix rows cols i*cols+cols ≤ activePtr := by nlinarith
    have hrowSpace : src+choice matrix rows cols i*cols+cols ≤ lim.space := by omega
    have hrowRead : ∀ j < cols,
        μ₃ (src+choice matrix rows cols i*cols+j) = (matrix (choice matrix rows cols i) j : ℤ) := by
      intro j hj
      rw [hkeep₃ _ (Or.inl (by omega))]
      exact hread _ hchoice j hj
    have hmulWord : ((choice matrix rows cols i*cols : ℕ) : ℤ) ≤ lim.word := by
      have hh : choice matrix rows cols i*cols ≤ lim.space := by omega
      exact (Int.ofNat_le.mpr hh).trans hw
    have haddr : ((src : ℤ)+(choice matrix rows cols i : ℤ)*cols).toNat =
        src+choice matrix rows cols i*cols := by
      rw [← Nat.cast_mul,← Nat.cast_add,Int.toNat_natCast]
    have hu := LightCoverUpdate.meets (d := d+1) (μ := μ₃)
      (row := src+choice matrix rows cols i*cols) (activePtr := activePtr) (n := cols)
      S.update (matrix (choice matrix rows cols i)) (active matrix rows cols i) hw hrowSpace
      hactiveSpace (Or.inl hrow) hrowRead hactive₃ (hmatrix _ hchoice)
      (fun j _ => active_le matrix rows cols i j) hword
    light_call hu using hselected',haddr,μ₃,roundTime,LightCoverSelect.time,LightCoverScores.time,
      LightBooleanDot.time,LightCoverUpdate.time,LightMinimum.time,out
      with vnew μ₄ ⟨hnewActive,hkeep₄⟩
    refine ⟨by simp,selected,vnew,μ₄,by simp [update_frame_setLocal],?_,?_,?_⟩
    · intro j hj
      rw [hnewActive j hj,active_succ hrows hmatrix i j hj]
    · exact hchoices₃.of_sameOutside hkeep₄ (Or.inr (by unfold out; omega))
    · intro a ha
      rw [hkeep₄ _ (by unfold total at ha; omega)]
      exact hkeep₃ a ha
  · intro σ hcounter hshape
    exact hshape
  · rintro i _ _ _ ⟨r,v,μ',rfl,_,_,_⟩
    simp
  · rintro σ ⟨r,v,μ',rfl,hactive,written,kept⟩
    light_set (out activePtr rows cols : ℕ) using out,roundTime
    exact ⟨rfl,written,hactive,kept⟩

def program : Program :=
  [body 1 2 6,fillBody,LightCoverSelect.body 3 5,LightCoverScores.body 4,
    LightBooleanDot.body,LightMinimum.body,LightCoverUpdate.body]

def programProcs : Procs program 0 :=
  ⟨1,2,6,rfl,⟨3,4,5,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩

theorem program_meets
    {μ : ℕ → ℤ} {src activePtr rows cols rounds : ℕ}
    (matrix : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hrows : 0 < rows)
    (hsrc : src+rows*cols ≤ activePtr)
    (hspace : activePtr+total rows cols rounds ≤ lim.space)
    (hread : ∀ i < rows, ∀ j < cols, μ (src+i*cols+j) = (matrix i j : ℤ))
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim program 0 d [src,activePtr,rows,cols,rounds] μ (time rows cols rounds)
      (fun r μ' => r = (out activePtr rows cols : ℤ) ∧
        Seg μ' (out activePtr rows cols) ((choices matrix rows cols rounds).map (fun x : ℕ => (x : ℤ))) ∧
        (∀ j < cols, μ' (activePtr+j) = (active matrix rows cols rounds j : ℤ)) ∧
        SameOutside μ μ' activePtr (total rows cols rounds)) :=
  programProcs.meets matrix hw hd hrows hsrc hspace hread hmatrix hword

end ThreeSum.LightCoverGreedy
