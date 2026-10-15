import Submission.ThreeSum.LightBandLookup

/-! Actual scan plus logarithmic exact membership lookup for colored two-sum. -/
noncomputable section
namespace ThreeSum.LightColoredTwoSum
open Light ThreeSum.LightSubsetAddress
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 4000000
set_option maxRecDepth 12000

theorem lookup_positive_iff (target : ℕ → ℤ) (m : ℕ) (x : ℤ)
    (hs : ∀ i j, i<j → j<m → target i<target j) :
    0<LightBandLookup.result target target m x ↔ ∃ j<m, target j=x := by
  have hle : ∀ i j, i≤j → j<m → target i≤target j := by
    intro i j hij hj
    rcases eq_or_lt_of_le hij with rfl | hlt
    · rfl
    · exact (hs i j hlt hj).le
  constructor
  · intro hp
    cases he : BinarySearch.locate target target m x with
    | none => simp [LightBandLookup.result,he] at hp
    | some j =>
      have hh := BinarySearch.locate_sound target target m x hle he
      exact ⟨j,hh.1,le_antisymm hh.2.1 hh.2.2⟩
  · rintro ⟨j,hj,he⟩
    have hh := BinarySearch.locate_complete target target m x hle hs hj (by omega) (by omega)
    simp [LightBandLookup.result,hh]

def Hit (scan target : ℕ → ℤ) (m j : ℕ) (bad sign : ℤ) : Prop :=
  ∃ i<j, ∃ k<m, target k=sign*scan i+bad

def flag (scan target : ℕ → ℤ) (m j : ℕ) (bad sign : ℤ) : ℕ :=
  if Hit scan target m j bad sign then 1 else 0

@[simp] theorem flag_zero (scan target : ℕ → ℤ) (m : ℕ) (bad sign : ℤ) :
    flag scan target m 0 bad sign=0 := by simp [flag,Hit]

theorem flag_le_one (scan target : ℕ → ℤ) (m j : ℕ) (bad sign : ℤ) :
    flag scan target m j bad sign≤1 := by unfold flag; split <;> omega

theorem hit_succ (scan target : ℕ → ℤ) (m j : ℕ) (bad sign : ℤ) :
    Hit scan target m (j+1) bad sign ↔ Hit scan target m j bad sign ∨ ∃ k<m, target k=sign*scan j+bad := by
  unfold Hit
  constructor
  · rintro ⟨i,hi,k,hk,he⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact Or.inl ⟨i,hi,k,hk,he⟩
    · exact Or.inr ⟨k,hk,he⟩
  · rintro (⟨i,hi,k,hk,he⟩ | ⟨k,hk,he⟩)
    · exact ⟨i,by omega,k,hk,he⟩
    · exact ⟨j,by omega,k,hk,he⟩

def roundBody (pLookup : ℕ) : Stmt :=
  .set 10 (v 7 *' M (v 0 +' v 9) +' v 6) ;;
  .call pLookup [v 2,v 2,v 3,v 10,v 4,v 5] 11 ;;
  .ite (k 0 <' v 11) (.set 8 (k 1)) .skip

def body (pLookup : ℕ) : Stmt := .set 8 (k 0) ;; .for 9 (v 1) (roundBody pLookup) ;; .set 0 (v 8)
def time (n L : ℕ) : ℕ := n*(LightBandLookup.time L+200)+100

def Inv (μ : ℕ → ℤ) (a n b m powers L : ℕ) (bad sign : ℤ) (scan target : ℕ → ℤ)
    (j : ℕ) (σ : State) : Prop := ∃ q r : ℤ,
    σ=⟨frame [a,n,b,m,powers,L,bad,sign,flag scan target m j bad sign,j,q,r],μ⟩

variable {lim : Limits} {P : Program}

theorem meets {pMain pLookup pSearch a n b m powers W L U d : ℕ} (bad sign : ℤ)
    (hmain : P[pMain]?=some (body pLookup))
    (hlookup : P[pLookup]?=some (LightBandLookup.body pSearch))
    (hsearch : P[pSearch]?=some (LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (scan target : ℕ → ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (ha : a+n≤lim.space) (hb : b+m≤lim.space)
    (hspace : powers+(W+1)≤lim.space)
    (hword : ((m+2^(W+1)+16 : ℕ) : ℤ)≤lim.word)
    (hvalues : ∀ i<n, |scan i|≤U) (hbad : |bad|≤U) (hsign : |sign|≤1)
    (hvalueWord : 2*(U : ℤ)+3≤lim.word)
    (hread : ∀ i<n, μ (a+i)=scan i) (htarget : ∀ j<m, μ (b+j)=target j)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i j, i<j → j<m → target i<target j)
    (hL : L≤W) (hm : m<2^L) (hd : d+L+2≤lim.depth) :
    Meets lim P pMain d [a,n,b,m,powers,L,bad,sign] μ (time n L)
      (fun r ν => r=(flag scan target m n bad sign : ℤ) ∧ ν=μ) := by
  have htargetSorted : ∀ i j, i≤j → j<m → target i≤target j := by
    intro i j hij hj
    rcases eq_or_lt_of_le hij with rfl | hlt
    · rfl
    · exact (hsorted i j hlt hj).le
  apply Meets.of_body hmain
  unfold body time
  light_set 0 using LightBandLookup.time
  refine Ends.pieceThen (Ends.for (T := n*(LightBandLookup.time L+200)+20)
    (Q := Inv μ a n b m powers L bad sign scan target n)
    (Inv μ a n b m powers L bad sign scan target) n (LightBandLookup.time L+150)
    ?start ?round ?done ?bound (hT := by light_time)) ?after (hT := by light_time)
  case start =>
    refine ⟨0,0,?_⟩
    simp [update_frame_setLocal]
    change frame [(a : ℤ),n,b,m,powers,L,bad,sign,0,0]=
      frame ([(a : ℤ),n,b,m,powers,L,bad,sign,0,0]++[0,0])
    exact (frame_append_zeros _ 2).symm
  case round =>
    rintro j _ hj _ ⟨q,r,rfl⟩
    have hRead := hread j hj
    have hprod : |sign*scan j|≤U := by
      rw [abs_mul]
      exact (mul_le_mul hsign (hvalues j hj) (abs_nonneg _) (by omega)).trans_eq (one_mul _)
    have hquery : |sign*scan j+bad|≤2*(U : ℤ) :=
      (abs_add_le _ _).trans (by linarith [hprod,hbad])
    have hQueryBounds := abs_le.mp hquery
    have hProdBounds := abs_le.mp hprod
    have hSignBounds := abs_le.mp hsign
    have hBadBounds := abs_le.mp hbad
    have hc := LightBandLookup.meets (d := d+1) (x := sign*scan j+bad) hlookup hsearch μ target target hw hb hb hspace hword
      htarget htarget hpowers htargetSorted hL hm (by omega)
    have hflag := flag_le_one scan target m j bad sign
    unfold roundBody
    light_set (sign*scan j+bad) using hRead,LightBandLookup.time
    light_call hc using LightBandLookup.time
      with out ν ⟨hout,hmem⟩
    subst ν
    have hresult := LightBandLookup.result_le target target m (sign*scan j+bad) htargetSorted
    have hpos := lookup_positive_iff target m (sign*scan j+bad) hsorted
    light_if hp hn : (0 : ℤ)<(LightBandLookup.result target target m (sign*scan j+bad) : ℤ)
      using hout,LightBandLookup.time
    · have hcurrent : ∃ k<m, target k=sign*scan j+bad := hpos.mp (by exact_mod_cast hp)
      have hnext : flag scan target m (j+1) bad sign=1 := by
        unfold flag
        rw [if_pos ((hit_succ scan target m j bad sign).mpr (Or.inr hcurrent))]
      light_set 1 using LightBandLookup.time
      refine ⟨by simp,sign*scan j+bad,out,?_⟩
      simp [update_frame_setLocal,hnext]
    · have hcurrent : ¬∃ k<m, target k=sign*scan j+bad := fun hh => hn (by exact_mod_cast hpos.mpr hh)
      have hnext : flag scan target m (j+1) bad sign=flag scan target m j bad sign := by
        simp only [flag,hit_succ,or_false,hcurrent]
      refine Ends.skip ⟨by simp,sign*scan j+bad,out,?_⟩
      simp [update_frame_setLocal,hnext]
  case done => intro σ _ hshape; exact hshape
  case bound =>
    rintro j _ hj _ ⟨q,r,rfl⟩
    light_side
  case after =>
    rintro _ ⟨q,r,rfl⟩
    have hf := flag_le_one scan target m n bad sign
    light_set (flag scan target m n bad sign : ℕ)
    exact ⟨by simp,rfl⟩

def program : Program := [body 1,LightBandLookup.body 2,LightBandLookup.searchBody 2]

end ThreeSum.LightColoredTwoSum
