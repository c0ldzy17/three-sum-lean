import Submission.ThreeSum.LightColoredTwoSum
import Submission.ThreeSum.LightOriginalBucketFilter

/-! Exact two-sum cleanup over a physically stored list of deleted ORIGINAL record indices. -/
noncomputable section
namespace ThreeSum.LightDeletedTwoSum
open Light ThreeSum.LightSubsetAddress
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000

def Hit (ids : ℕ → ℕ) (values scan target : ℕ → ℤ) (targetN scanN j : ℕ) (sign : ℤ) : Prop :=
  ∃ i<j, LightColoredTwoSum.Hit scan target targetN scanN (values (ids i)) sign

def flag (ids : ℕ → ℕ) (values scan target : ℕ → ℤ) (targetN scanN j : ℕ) (sign : ℤ) : ℕ :=
  if Hit ids values scan target targetN scanN j sign then 1 else 0

@[simp] theorem flag_zero (ids : ℕ → ℕ) (values scan target : ℕ → ℤ) (targetN scanN : ℕ) (sign : ℤ) :
    flag ids values scan target targetN scanN 0 sign=0 := by simp [flag,Hit]

theorem flag_le_one (ids : ℕ → ℕ) (values scan target : ℕ → ℤ) (targetN scanN j : ℕ) (sign : ℤ) :
    flag ids values scan target targetN scanN j sign≤1 := by unfold flag; split <;> omega

theorem hit_succ (ids : ℕ → ℕ) (values scan target : ℕ → ℤ) (targetN scanN j : ℕ) (sign : ℤ) :
    Hit ids values scan target targetN scanN (j+1) sign ↔
      Hit ids values scan target targetN scanN j sign ∨
        LightColoredTwoSum.Hit scan target targetN scanN (values (ids j)) sign := by
  unfold Hit
  constructor
  · rintro ⟨i,hi,hh⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact Or.inl ⟨i,hi,hh⟩
    · exact Or.inr hh
  · rintro (⟨i,hi,hh⟩ | hh)
    · exact ⟨i,by omega,hh⟩
    · exact ⟨j,by omega,hh⟩

def roundBody (pTwoSum : ℕ) : Stmt :=
  .set 13 (M (v 0 +' v 12)) ;;
  .set 14 (M (v 2 +' v 13)) ;;
  .call pTwoSum [v 4,v 5,v 6,v 7,v 8,v 9,v 14,v 10] 15 ;;
  .ite (k 0 <' v 15) (.set 11 (k 1)) .skip

def body (pTwoSum : ℕ) : Stmt := .set 11 (k 0) ;; .for 12 (v 1) (roundBody pTwoSum) ;; .set 0 (v 11)
def time (badN scanN L : ℕ) : ℕ := badN*(LightColoredTwoSum.time scanN L+200)+100

def Inv (μ : ℕ → ℤ) (badBase badN valuesBase originalN scanBase scanN targetBase targetN powers L : ℕ)
    (sign : ℤ) (ids : ℕ → ℕ) (values scan target : ℕ → ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ index bad result : ℤ,
    σ=⟨frame [badBase,badN,valuesBase,originalN,scanBase,scanN,targetBase,targetN,powers,L,sign,
      flag ids values scan target targetN scanN j sign,j,index,bad,result],μ⟩

variable {lim : Limits} {P : Program}

theorem meets {pMain pTwoSum pLookup pSearch badBase badN valuesBase originalN scanBase scanN targetBase targetN
    powers W L U d : ℕ} (sign : ℤ)
    (hmain : P[pMain]?=some (body pTwoSum))
    (htwo : P[pTwoSum]?=some (LightColoredTwoSum.body pLookup))
    (hlookup : P[pLookup]?=some (LightBandLookup.body pSearch))
    (hsearch : P[pSearch]?=some (LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (ids : ℕ → ℕ) (values scan target : ℕ → ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (hbadSpace : badBase+badN≤lim.space) (hvaluesSpace : valuesBase+originalN≤lim.space)
    (hscanSpace : scanBase+scanN≤lim.space) (htargetSpace : targetBase+targetN≤lim.space)
    (hspace : powers+(W+1)≤lim.space)
    (hword : ((targetN+2^(W+1)+16 : ℕ) : ℤ)≤lim.word)
    (hids : ∀ i<badN, ids i<originalN) (hreadIds : ∀ i<badN, μ (badBase+i)=(ids i : ℤ))
    (hvalues : ∀ i<originalN, |values i|≤U) (hreadValues : ∀ i<originalN, μ (valuesBase+i)=values i)
    (hscan : ∀ i<scanN, |scan i|≤U) (hreadScan : ∀ i<scanN, μ (scanBase+i)=scan i)
    (hreadTarget : ∀ i<targetN, μ (targetBase+i)=target i)
    (hsign : |sign|≤1) (hvalueWord : 2*(U : ℤ)+3≤lim.word)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i j, i<j → j<targetN → target i<target j)
    (hL : L≤W) (htargetN : targetN<2^L) (hd : d+L+3≤lim.depth) :
    Meets lim P pMain d [badBase,badN,valuesBase,originalN,scanBase,scanN,targetBase,targetN,powers,L,sign] μ
      (time badN scanN L)
      (fun r ν => r=(flag ids values scan target targetN scanN badN sign : ℤ) ∧ ν=μ) := by
  apply Meets.of_body hmain
  unfold body time
  light_set 0 using LightColoredTwoSum.time
  refine Ends.pieceThen (Ends.for (T := badN*(LightColoredTwoSum.time scanN L+200)+20)
    (Q := Inv μ badBase badN valuesBase originalN scanBase scanN targetBase targetN powers L sign ids values scan target badN)
    (Inv μ badBase badN valuesBase originalN scanBase scanN targetBase targetN powers L sign ids values scan target)
    badN (LightColoredTwoSum.time scanN L+150)
    ?start ?round ?done ?bound (hT := by light_time)) ?after (hT := by light_time)
  case start =>
    refine ⟨0,0,0,?_⟩
    simp [update_frame_setLocal]
    change frame [(badBase : ℤ),badN,valuesBase,originalN,scanBase,scanN,targetBase,targetN,powers,L,sign,0,0]=
      frame ([(badBase : ℤ),badN,valuesBase,originalN,scanBase,scanN,targetBase,targetN,powers,L,sign,0,0]++[0,0,0])
    exact (frame_append_zeros _ 3).symm
  case round =>
    rintro j _ hj _ ⟨index,bad,result,rfl⟩
    have hid := hids j hj
    have hIdRead := hreadIds j hj
    have hValueRead := hreadValues _ hid
    have hValueBounds := abs_le.mp (hvalues _ hid)
    have hf := flag_le_one ids values scan target targetN scanN j sign
    have hc := LightColoredTwoSum.meets (d := d+1) (values (ids j)) sign htwo hlookup hsearch μ scan target
      hw hscanSpace htargetSpace hspace hword hscan (hvalues _ hid) hsign hvalueWord
      hreadScan hreadTarget hpowers hsorted hL htargetN (by omega)
    unfold roundBody
    light_set (ids j : ℕ) using hIdRead,LightColoredTwoSum.time
    light_set (values (ids j)) using hValueRead,LightColoredTwoSum.time
    light_call hc using LightColoredTwoSum.time
      with out ν ⟨hout,hmem⟩
    subst ν
    have hfound := LightColoredTwoSum.flag_le_one scan target targetN scanN (values (ids j)) sign
    light_if hp hn : (0 : ℤ)<(LightColoredTwoSum.flag scan target targetN scanN (values (ids j)) sign : ℤ)
      using hout,LightColoredTwoSum.time
    · have hcurrent : LightColoredTwoSum.Hit scan target targetN scanN (values (ids j)) sign := by
        by_contra hh
        simp [LightColoredTwoSum.flag,hh] at hp
      have hnext : flag ids values scan target targetN scanN (j+1) sign=1 := by
        unfold flag
        rw [if_pos ((hit_succ ids values scan target targetN scanN j sign).mpr (Or.inr hcurrent))]
      light_set 1 using LightColoredTwoSum.time
      refine ⟨by simp,(ids j : ℤ),values (ids j),out,?_⟩
      simp [update_frame_setLocal,hnext]
    · have hcurrent : ¬LightColoredTwoSum.Hit scan target targetN scanN (values (ids j)) sign := by
        intro hh
        simp [LightColoredTwoSum.flag,hh] at hn
      have hnext : flag ids values scan target targetN scanN (j+1) sign=flag ids values scan target targetN scanN j sign := by
        simp only [flag,hit_succ,or_false,hcurrent]
      refine Ends.skip ⟨by simp,(ids j : ℤ),values (ids j),out,?_⟩
      simp [update_frame_setLocal,hnext]
  case done => intro σ _ hshape; exact hshape
  case bound =>
    rintro j _ hj _ ⟨index,bad,result,rfl⟩
    light_side
  case after =>
    rintro _ ⟨index,bad,result,rfl⟩
    have hf := flag_le_one ids values scan target targetN scanN badN sign
    light_set (flag ids values scan target targetN scanN badN sign : ℕ)
    exact ⟨by simp,rfl⟩

def program : Program := [body 1,LightColoredTwoSum.body 2,LightBandLookup.body 3,LightBandLookup.searchBody 3]

end ThreeSum.LightDeletedTwoSum
