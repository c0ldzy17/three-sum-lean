import Submission.ThreeSum.LightHistogram

/-! Actual filtering of original record indices by physical hash-bucket size. -/
noncomputable section
namespace ThreeSum.LightOriginalBucketFilter
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def good (keys counts : ℕ → ℕ) (n : ℕ) : List ℕ := (List.range n).filter fun i => counts (keys i)=1
def bad (keys counts : ℕ → ℕ) (n : ℕ) : List ℕ := (List.range n).filter fun i => counts (keys i)≠1

def cells (xs : List ℕ) : List ℤ := xs.map (fun i => (i : ℤ))

@[simp] theorem good_zero (keys counts : ℕ → ℕ) : good keys counts 0=[] := rfl
@[simp] theorem bad_zero (keys counts : ℕ → ℕ) : bad keys counts 0=[] := rfl

theorem lengths (keys counts : ℕ → ℕ) (n : ℕ) :
    (good keys counts n).length≤n ∧ (bad keys counts n).length≤n := by
  constructor <;> apply (List.length_filter_le _ _).trans_eq (List.length_range : (List.range n).length=n)

theorem good_succ (keys counts : ℕ → ℕ) (n : ℕ) :
    good keys counts (n+1)=good keys counts n++if counts (keys n)=1 then [n] else [] := by
  by_cases h : counts (keys n)=1 <;> simp [good,List.range_succ,List.filter_append,h]

theorem bad_succ (keys counts : ℕ → ℕ) (n : ℕ) :
    bad keys counts (n+1)=bad keys counts n++if counts (keys n)=1 then [] else [n] := by
  by_cases h : counts (keys n)=1 <;> simp [bad,List.range_succ,List.filter_append,h]

def roundBody : Stmt :=
  .set 8 (M (v 0 +' v 7)) ;;
  .set 9 (M (v 2 +' v 8)) ;;
  .ite (v 9 =' k 1)
    (.store (v 4 +' v 5) (v 7) ;; .set 5 (v 5 +' k 1))
    (.store (v 4 +' v 1 +' v 6) (v 7) ;; .set 6 (v 6 +' k 1))

def body : Stmt := .set 5 (k 0) ;; .set 6 (k 0) ;; .for 7 (v 1) roundBody ;; .set 0 (v 6)
def time (n : ℕ) : ℕ := 200*n+100

def Inv (μ : ℕ → ℤ) (keyBase n hist q out : ℕ) (keys counts : ℕ → ℕ) (i : ℕ) (σ : State) : Prop :=
  ∃ key count : ℤ, ∃ ν : ℕ → ℤ,
    σ=⟨frame [keyBase,n,hist,q,out,(good keys counts i).length,(bad keys counts i).length,i,key,count],ν⟩ ∧
    Seg ν out (cells (good keys counts i)) ∧ Seg ν (out+n) (cells (bad keys counts i)) ∧
    SameOutside μ ν out (2*n)

variable {lim : Limits} {P : Program}

theorem meets {pMain keyBase n hist q out d : ℕ} (hmain : P[pMain]?=some body)
    (μ : ℕ → ℤ) (keys counts : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word)
    (hkeysSpace : keyBase+n≤out) (hhistSpace : hist+q≤out) (hout : out+2*n≤lim.space)
    (hkeys : ∀ i<n, keys i<q)
    (hread : ∀ i<n, μ (keyBase+i)=(keys i : ℤ))
    (hcounts : ∀ k<q, μ (hist+k)=(counts k : ℤ))
    (hcountWord : ∀ k<q, (counts k : ℤ)≤lim.word)
    (hone : (1 : ℤ)≤lim.word) :
    Meets lim P pMain d [keyBase,n,hist,q,out] μ (time n)
      (fun r ν => r=((bad keys counts n).length : ℤ) ∧
        Seg ν out (cells (good keys counts n)) ∧ Seg ν (out+n) (cells (bad keys counts n)) ∧
        SameOutside μ ν out (2*n)) := by
  apply Meets.of_body hmain
  unfold body time
  light_set 0
  light_set 0
  refine Ends.pieceThen (Ends.for (T := 200*n+30)
    (Q := Inv μ keyBase n hist q out keys counts n)
    (Inv μ keyBase n hist q out keys counts) n 150
    ?start ?round ?done ?bound (hT := by light_time)) ?after (hT := by light_time)
  case start =>
    refine ⟨0,0,μ,?_,Seg.nil,Seg.nil,SameOn.refl⟩
    simp [update_frame_setLocal]
    change frame [(keyBase : ℤ),n,hist,q,out,0,0,0]=
      frame ([(keyBase : ℤ),n,hist,q,out,0,0,0]++[0,0])
    exact (frame_append_zeros _ 2).symm
  case round =>
    rintro i _ hi _ ⟨key,count,ν,rfl,hGood,hBad,H⟩
    have hg := (lengths keys counts i).1
    have hb := (lengths keys counts i).2
    have hk := hkeys i hi
    have hKeyRead : ν (keyBase+i)=(keys i : ℤ) := by rw [H _ (Or.inl (by omega)),hread i hi]
    have hCountRead : ν (hist+keys i)=(counts (keys i) : ℤ) := by rw [H _ (Or.inl (by omega)),hcounts _ hk]
    have hCountWord := hcountWord _ hk
    unfold roundBody
    light_set (keys i : ℕ) using hKeyRead
    light_set (counts (keys i) : ℕ) using hCountRead
    light_if hc hnc : counts (keys i)=1
    · have hGoodNext : good keys counts (i+1)=good keys counts i++[i] := by simp [good_succ,hc]
      have hBadNext : bad keys counts (i+1)=bad keys counts i := by simp [bad_succ,hc]
      light_store (out+(good keys counts i).length) (i : ℕ)
      light_set ((good keys counts i).length+1 : ℕ)
      refine ⟨by simp,(keys i : ℤ),(counts (keys i) : ℤ),
        Function.update ν (out+(good keys counts i).length) (i : ℤ),?_,?_,?_,?_⟩
      · simp [update_frame_setLocal,hGoodNext,hBadNext]
      · simpa [hGoodNext,cells,List.map_append] using hGood.snoc (i : ℤ)
      · rw [hBadNext]
        exact hBad.update_out (Or.inl (by omega)) _
      · exact H.update ⟨by omega,by omega⟩ _
    · have hGoodNext : good keys counts (i+1)=good keys counts i := by simp [good_succ,hnc]
      have hBadNext : bad keys counts (i+1)=bad keys counts i++[i] := by simp [bad_succ,hnc]
      light_store (out+n+(bad keys counts i).length) (i : ℕ)
      light_set ((bad keys counts i).length+1 : ℕ)
      refine ⟨by simp,(keys i : ℤ),(counts (keys i) : ℤ),
        Function.update ν (out+n+(bad keys counts i).length) (i : ℤ),?_,?_,?_,?_⟩
      · simp [update_frame_setLocal,hGoodNext,hBadNext]
      · rw [hGoodNext]
        exact hGood.update_out (Or.inr (by simp [cells]; omega)) _
      · simpa [hBadNext,cells,List.map_append] using hBad.snoc (i : ℤ)
      · exact H.update ⟨by omega,by omega⟩ _
  case done => intro σ _ H; exact H
  case bound =>
    rintro i _ hi _ ⟨key,count,ν,rfl,hGood,hBad,H⟩
    light_side
  case after =>
    rintro _ ⟨key,count,ν,rfl,hGood,hBad,H⟩
    have hb := (lengths keys counts n).2
    light_set ((bad keys counts n).length : ℕ)
    exact ⟨by simp,hGood,hBad,H⟩

end ThreeSum.LightOriginalBucketFilter
