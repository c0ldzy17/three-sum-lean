import Submission.ThreeSum.LightTernaryMomentRow

/-! Actual detector calls over literal wanted records and channel-major outputs. -/
noncomputable section
namespace ThreeSum.LightTernaryMomentBatch
open Light FiniteMomentZeroDetector
attribute [local instance] Classical.propDecidable

def flag (hit : ℕ→Prop) (i : ℕ) : ℤ := by
  classical
  exact if ∃ j < i, hit j then 1 else 0

@[simp] theorem flag_zero (hit : ℕ→Prop) : flag hit 0=0 := by simp [flag]
theorem flag_succ (hit : ℕ→Prop) (i : ℕ) :
    flag hit (i+1)=(if hit i then 1 else flag hit i) := by
  classical
  have he : (∃ j < i+1, hit j) ↔ (∃ j < i, hit j) ∨ hit i := by
    constructor
    · rintro ⟨j,hj,hh⟩
      by_cases hji : j < i
      · exact Or.inl ⟨j,hji,hh⟩
      · have : j=i := by omega
        subst j
        exact Or.inr hh
    · rintro (⟨j,hj,hh⟩ | hh)
      · exact ⟨j,by omega,hh⟩
      · exact ⟨i,by omega,hh⟩
  unfold flag
  simp only [he]
  by_cases hi : hit i <;> by_cases hp : ∃ j < i, hit j <;> simp [hi,hp]

def body (H pRow : ℕ) : Stmt :=
  .set 6 (k 0) ;;
  .set 8 (k 0) ;;
  .for 7 (v 1) (
    .call pRow [v 0 +' k 3 *' v 7,v 2,v 3,v 4,v 1,v 7,v 5] 8 ;;
    .ite (k 0 <' v 8) (.set 6 (k 1)) .skip) ;;
  .set 0 (v 6)

def time (H count : ℕ) : ℕ := count*(LightTernaryMomentRow.time H+200)+30

structure Procs (H : ℕ) (P : Program) (pMain : ℕ) where
  pRow : ℕ
  row : LightTernaryMomentRow.Procs H P pRow
  main : P[pMain]?=some (body H pRow)

def Inv (μ : ℕ→ℤ) (hit : ℕ→Prop)
    (records count originalA originalCount matrix scratch i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ→ℤ),
    σ=⟨frame [records,count,originalA,originalCount,matrix,scratch,flag hit i,i,r],ν⟩ ∧
      Kept μ ν scratch

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {H pMain : ℕ} (S : Procs H P pMain)
    {μ : ℕ→ℤ} {records count originalA originalCount matrix scratch U : ℕ}
    (position t : ℕ→ℕ) (A : ℕ→ℤ) (v w : ∀ i, Fin (t i)→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+1<lim.depth)
    (hrecords : records+3*count≤scratch) (hAarray : originalA+originalCount≤scratch)
    (hmatrix : matrix+(2*H+1)*count≤scratch) (hspace : scratch+(2*H+1)≤lim.space)
    (hpositions : ∀ i<count, position i<originalCount)
    (hpositionRead : ∀ i<count, μ (records+3*i)=(position i : ℤ))
    (hAread : ∀ j<originalCount, μ (originalA+j)=A j)
    (hA : ∀ j<originalCount, |A j|≤(U : ℤ))
    (hword : max (U : ℤ) (LightMomentDeterminant.wordBound U H)≤lim.word)
    (hv : ∀ i<count, Function.Injective (v i))
    (hweights : ∀ i<count, ∀ s, w i s≠0) (ht : ∀ i<count, t i≤H)
    (hmabs : ∀ i<count, ∀ k≤2*H, |moment (v i) (w i) k|≤(U : ℤ))
    (hm : ∀ i<count, ∀ k≤2*H, μ (matrix+k*count+i)=moment (v i) (w i) k) :
    Meets lim P pMain d [records,count,originalA,originalCount,matrix,scratch] μ (time H count)
      (fun r ν => r=(if ∃ i<count, ∃ s, v i s=A (position i) then 1 else 0 : ℤ) ∧
        Kept μ ν scratch) := by
  classical
  let hit : ℕ→Prop := fun i => ∃ s, v i s=A (position i)
  have hflag (i : ℕ) : 0≤flag hit i ∧ flag hit i≤1 := by
    unfold flag
    split_ifs <;> omega
  have h1 : (1 : ℤ)≤lim.word := by
    have hlim : (1 : ℕ)≤lim.space := by omega
    exact (Int.ofNat_le.mpr hlim).trans hw
  have hcount : (count : ℤ)≤lim.word := by
    have hh : count≤lim.space := by omega
    exact (Int.ofNat_le.mpr hh).trans hw
  apply Meets.of_body S.main
  unfold body time
  light_set (0 : ℕ) using LightTernaryMomentRow.time
  light_set (0 : ℕ) using LightTernaryMomentRow.time
  refine Ends.pieceThen (Ends.for
    (T := count*(LightTernaryMomentRow.time H+200)+10)
    (Q := fun σ => ∃ r ν,
      σ=⟨frame [records,count,originalA,originalCount,matrix,scratch,flag hit count,count,r],ν⟩ ∧
        Kept μ ν scratch)
    (Inv μ hit records count originalA originalCount matrix scratch) count
    (LightTernaryMomentRow.time H+170) ?start ?round ?done ?bound
    (hT := by light_time)) ?finish
  case start =>
    refine ⟨0,μ,?_,SameOn.refl⟩
    simp [Inv,flag_zero,update_frame_setLocal]
  case round =>
    rintro i _ hi _ ⟨r,ν,rfl,hkeep⟩
    change i<count at hi
    have him := Nat.mul_le_mul_left 3 (show i+1≤count by omega)
    simp only [Nat.mul_add,Nat.mul_one] at him
    have hrecord : records+3*i+3≤scratch := by omega
    have hrpos : ν (records+3*i)=(position i : ℤ) := by
      rw [hkeep _ (by omega)]
      exact hpositionRead i hi
    have htarget : ν (originalA+position i)=A (position i) := by
      rw [hkeep _ (by have := hpositions i hi; omega)]
      exact hAread _ (hpositions i hi)
    have hmrow : ∀ k≤2*H, ν (matrix+k*count+i)=moment (v i) (w i) k := by
      intro k hk
      have hmul := Nat.mul_le_mul_right count (show k+1≤2*H+1 by omega)
      simp only [Nat.add_mul,one_mul] at hmul
      have hmatrix' := hmatrix
      rw [Nat.add_mul,one_mul] at hmatrix'
      rw [hkeep _ (by omega)]
      exact hm i hi k hk
    have hrecordCast : ((records : ℤ)+3*(i : ℤ)).toNat=records+3*i := by norm_cast
    have hmulWord : (3 : ℤ)*i≤lim.word := by
      have hh : 3*i≤lim.space := by omega
      exact (Int.ofNat_le.mpr hh).trans hw
    light_call (S.row.meets (d := d+1) (μ := ν)
      (record := records+3*i) (originalA := originalA) (originalCount := originalCount)
      (matrix := matrix) (count := count) (row := i) (scratch := scratch) (position := position i)
      (U := U) (t := t i) (A (position i)) (v i) (w i) hw (by omega) hi (hpositions i hi)
      hrecord hAarray hmatrix hspace hrpos htarget (hA _ (hpositions i hi)) hword
      (hv i hi) (hweights i hi) (ht i hi) (hmabs i hi) hmrow)
      using hrecordCast,LightTernaryMomentRow.time with r' ξ ⟨hanswer,hkeepRow⟩
    have hkept : Kept μ ξ scratch := by
      intro a ha
      exact (hkeepRow a ha).trans (hkeep a ha)
    light_if hyes hno : (0 : ℤ)<(if hit i then 1 else 0 : ℤ)
      using hanswer,hit,LightTernaryMomentRow.time
    · have hhit : hit i := by by_contra hn; simp [hn] at hyes
      light_set (1 : ℤ) using LightTernaryMomentRow.time
      refine ⟨by simp,r',ξ,?_,hkept⟩
      simp [update_frame_setLocal,flag_succ,hhit]
    · have hmiss : ¬hit i := by intro hh; simp [hh] at hno
      refine Ends.skip ?_
      refine ⟨by simp,r',ξ,?_,hkept⟩
      simp [update_frame_setLocal,flag_succ,hmiss]
  case done =>
    rintro _ _ ⟨r,ν,rfl,hkeep⟩
    exact ⟨r,ν,rfl,hkeep⟩
  case bound =>
    rintro i _ hi _ ⟨r,ν,rfl,hkeep⟩
    light_side
  case finish =>
    rintro _ ⟨r,ν,rfl,hkeep⟩
    have hf := hflag count
    light_set (flag hit count) using LightTernaryMomentRow.time
    exact ⟨by simp [flag,hit],hkeep⟩

def program (H : ℕ) : Program :=
  [body H 1,LightTernaryMomentRow.body H 2 3,LightTernaryMomentGather.body,
    LightMomentDeterminant.body (LightMomentZeroDetector.atoms H) H]

def procs (H : ℕ) : Procs H (program H) 0 where
  pRow := 1
  row := ⟨2,3,rfl,rfl,rfl⟩
  main := rfl

end ThreeSum.LightTernaryMomentBatch
