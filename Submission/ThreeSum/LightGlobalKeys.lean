import Submission.ThreeSum.LocalKeyArraySemantics
import Submission.ThreeSum.LightRadixKeys
import Submission.ThreeSum.LightSubsetEnumerationSetup

/-!
# From selected coefficient rows to every original global output key

The fixed program constructs the output-mask layer, all signed local keys,
and the full positional product. Its output is the literal occurrence-aware
`GlobalKeyEnumeration.globalKeys` array. No input key or mask table is assumed.
-/

namespace ThreeSum.LightGlobalKeys

open Light GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open LightSubsetAddress SubsetAddress

set_option maxHeartbeats 600000
set_option maxRecDepth 10000

/-- L, layer cardinality, schedule length, radix, block count, coefficient rows,
layer size, and first free address. Sizes are read from the parameter initializer. -/
def body (pEnum pLocal pGlobal : ℕ) : Stmt :=
  .set 8 (v 2 *' v 6) ;;
  .set 9 (v 7 +' v 6) ;;
  .set 10 (v 9 +' v 8) ;;
  .call pEnum [v 0,v 1,v 7,v 10] 11 ;;
  .call pLocal [v 0,v 7,v 11,v 5,v 2,v 9,v 10] 12 ;;
  .call pGlobal [v 9,v 8,v 4,v 3,v 10] 0

def localCount (h : ℕ) : ℕ := scheduleSize h*outputCount (512*h) h
def scratch (free h : ℕ) : ℕ := free+outputCount (512*h) h+localCount h

def space (free h J : ℕ) : ℕ :=
  max (LightLocalKeyRow.space (scratch free h) (512*h) (outputCount (512*h) h))
    (LightRadixKeys.space (scratch free h) (localCount h) J)

def word (h J : ℕ) : ℕ := 2^(512*h+1)+
  LightLocalKeys.word (512*h) (localPrime h) (scheduleSize h)+
  LightRadixKeys.word (localPrime h) (512*h*localPrime h) J+J+512

def time (h J : ℕ) : ℕ := LightSubsetEnumerationSetup.time (512*h) (2*h)+
  LightLocalKeys.time (512*h) (outputCount (512*h) h) (scheduleSize h)+
  LightRadixKeys.time (localCount h) J+200

private theorem sum_parts (a b c j : ℕ) :
    a ≤ a+b+c+j+512 ∧ b ≤ a+b+c+j+512 ∧
    c ≤ a+b+c+j+512 ∧ j ≤ a+b+c+j+512 := by omega

private theorem word_parts (h J : ℕ) :
    2^(512*h+1) ≤ word h J ∧
    LightLocalKeys.word (512*h) (localPrime h) (scheduleSize h) ≤ word h J ∧
    LightRadixKeys.word (localPrime h) (512*h*localPrime h) J ≤ word h J ∧
    J ≤ word h J :=
  sum_parts _ _ _ _

private theorem int_mul_le_word {a b c : ℕ} {w : ℤ}
    (hab : a*b ≤ c) (hc : (c : ℤ) ≤ w) : (a : ℤ)*(b : ℤ) ≤ w := by
  exact (show (a : ℤ)*(b : ℤ) ≤ (c : ℤ) by
    simpa only [Nat.cast_mul] using Int.ofNat_le.mpr hab).trans hc

theorem localCount_pos (h : ℕ) : 0 < localCount h := by
  apply Nat.mul_pos
  · unfold scheduleSize scheduleLength
    positivity
  · exact Nat.choose_pos (by omega)

theorem localKeys_length (h : ℕ) : (localKeys h).length=localCount h := by
  simp [localKeys,localRecords_length,localCount]

structure Procs (P : Program) (pMain : ℕ) where
  pEnum : ℕ
  pPowers : ℕ
  pLayer : ℕ
  pLocal : ℕ
  pGlobal : ℕ
  pRows : ℕ
  pAffine : ℕ
  main : P[pMain]? = some (body pEnum pLocal pGlobal)
  enum : P[pEnum]? = some (LightSubsetEnumerationSetup.body pPowers pLayer)
  powers : P[pPowers]? = some powTableBody
  layer : P[pLayer]? = some (LightSubsetEnumeration.body pLayer)
  locals : LightLocalKeys.Procs P pLocal
  globalProc : P[pGlobal]? = some (LightRadixKeys.body pGlobal pRows)
  rows : P[pRows]? = some (LightRadixRows.body pAffine)
  affine : P[pAffine]? = some LightReportingAffine.body

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets_with_masks {pMain h J maps free : ℕ} {μ : ℕ → ℤ} (S : Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+J+5 ≤ lim.depth)
    (hspace : space free h J ≤ lim.space) (hword : (word h J : ℤ) ≤ lim.word)
    (hmaps : maps+scheduleSize h*(2*(512*h)) ≤ free)
    (hreadFalse : ∀ j < scheduleSize h, ∀ i < 512*h,
      μ (maps+j*(2*(512*h))+i)=(BlockCoefficientRows.mapRow h false j i : ℤ))
    (hreadTrue : ∀ j < scheduleSize h, ∀ i < 512*h,
      μ (maps+j*(2*(512*h))+512*h+i)=(BlockCoefficientRows.mapRow h true j i : ℤ)) :
    Meets lim P pMain d [512*h,2*h,scheduleSize h,localPrime h,J,maps,
      outputCount (512*h) h,free] μ (time h J)
      (fun r ν => r=((scratch free h+LightRadixKeys.offset (localCount h) J : ℕ) : ℤ) ∧
        ν (scratch free h+LightRadixKeys.offset (localCount h) J)=((localCount h^J : ℕ) : ℤ) ∧
        Seg ν (scratch free h+LightRadixKeys.offset (localCount h) J+1) (globalKeys h J) ∧
        (∀ i < outputCount (512*h) h,
          ν (free+i)=(LocalMaskGraph.maskAt (512*h) (2*h) i : ℤ)) ∧
        Kept μ ν free) := by
  let n := outputCount (512*h) h
  let m := localCount h
  let dst := free+n
  let work := scratch free h
  have hwork : work=dst+m := rfl
  have hlspace : LightLocalKeyRow.space work (512*h) n ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hgspace : LightRadixKeys.space work m J ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hs : work+512*h+2*n+(512*h+1) ≤ lim.space := hlspace
  have hbudget (x : ℕ) (hx : x ≤ word h J) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hpword := hbudget (2^(512*h+1)) (word_parts h J).1
  have hlword := hbudget (LightLocalKeys.word (512*h) (localPrime h) (scheduleSize h)) (word_parts h J).2.1
  have hgword := hbudget (LightRadixKeys.word (localPrime h) (512*h*localPrime h) J) (word_parts h J).2.2.1
  have hJword := hbudget J (word_parts h J).2.2.2
  have hcount := localCount_pos h
  have hlen : (localKeys h).length=m := localKeys_length h
  have hprodWord : (scheduleSize h : ℤ)*(n : ℤ) ≤ lim.word := by
    have hh : scheduleSize h*n ≤ lim.space := by change m ≤ lim.space; omega
    exact int_mul_le_word hh hw
  have hprodNonneg : (0 : ℤ) ≤ (scheduleSize h : ℤ)*(n : ℤ) :=
    mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hprodWord' : (scheduleSize h : ℤ)*(outputCount (512*h) h : ℤ) ≤ lim.word := hprodWord
  have hprodNonneg' : (0 : ℤ) ≤ (scheduleSize h : ℤ)*(outputCount (512*h) h : ℤ) :=
    mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hproduct : (scheduleSize h : ℤ)*(outputCount (512*h) h : ℤ)=(m : ℤ) := by
    simp only [m,localCount,Nat.cast_mul]
  apply Meets.of_body S.main
  unfold body time
  light_set (scheduleSize h*outputCount (512*h) h : ℕ)
  light_set (dst : ℕ) using dst,n
  light_set (work : ℕ) using hwork,hproduct
  have he := LightSubsetEnumerationSetup.meets (d := d+1) (μ := μ)
    (L := 512*h) (k := 2*h) (dst := free) (work := work)
    S.enum S.powers S.layer hw (by omega) hpword (by omega)
    (by change free+n ≤ work; dsimp [dst] at hwork; omega) (by omega)
  light_call he with count μ₁ ⟨hcountVal,hmasks,hpowers,hkeep₁⟩
  have hc : count=(n : ℤ) := hcountVal
  have hmRead (i : ℕ) (hi : i < n) : μ₁ (free+i)=(LocalMaskGraph.maskAt (512*h) (2*h) i : ℤ) := by
    have hi' : i < (enumerateLayer (512*h) (2*h)).length := by
      rw [enumerateLayer_length]
      exact hi
    have he := hmasks i (by simpa only [List.length_map] using hi')
    simpa only [LocalMaskGraph.maskAt,List.getD_eq_getElem _ _ hi',List.getElem_map] using he
  have hfi (j : ℕ) (hj : j < scheduleSize h) (i : ℕ) (hi : i < 512*h) :
      μ₁ (maps+j*(2*(512*h))+i)=(BlockCoefficientRows.mapRow h false j i : ℤ) := by
    have hh := Nat.mul_le_mul_right (2*(512*h)) (show j+1 ≤ scheduleSize h by omega)
    simp only [Nat.add_mul,one_mul] at hh
    rw [hkeep₁ _ ⟨by omega,Or.inl (by omega)⟩]
    exact hreadFalse j hj i hi
  have hti (j : ℕ) (hj : j < scheduleSize h) (i : ℕ) (hi : i < 512*h) :
      μ₁ (maps+j*(2*(512*h))+512*h+i)=(BlockCoefficientRows.mapRow h true j i : ℤ) := by
    have hh := Nat.mul_le_mul_right (2*(512*h)) (show j+1 ≤ scheduleSize h by omega)
    simp only [Nat.add_mul,one_mul] at hh
    rw [hkeep₁ _ ⟨by omega,Or.inl (by omega)⟩]
    exact hreadTrue j hj i hi
  have hl := LocalKeyArraySemantics.meets_original (d := d+1) (μ := μ₁)
    (h := h) (masks := free) (maps := maps) (dst := dst) (free := work) S.locals
    hw (by omega) hlspace le_rfl (by dsimp [dst]; omega) (by dsimp [localCount,m] at *; omega)
    hlword hmRead hfi hti
  light_call hl using hc with result μ₂ ⟨hkeys,hkeep₂⟩
  have hg := LightRadixKeys.meets (src := dst) (dst := work) (p := localPrime h)
    (U := 512*h*localPrime h) S.globalProc S.rows S.affine (localKeys h) hw
    (by rw [hlen]; omega) (by rw [hlen]; exact hcount) (localKeys_bounded h)
    J (d+1) μ₂ (by simpa only [hlen] using hgspace) hgword (by omega) hkeys
  simp only [hlen] at hg
  light_call hg using m with final μ₃ ⟨hresult,hheader,hglobal,hkeep₃⟩
  refine ⟨hresult,hheader,hglobal,?_,?_⟩
  · intro i hi
    change μ₃ (free+i)=(LocalMaskGraph.maskAt (512*h) (2*h) i : ℤ)
    rw [hkeep₃ _ (by dsimp [dst] at hwork; change i < n at hi; omega),
      hkeep₂ _ (by dsimp [dst]; change i < n at hi; omega)]
    exact hmRead i hi
  · intro a ha
    change μ₃ a=μ a
    rw [hkeep₃ _ (by omega),hkeep₂ _ (by dsimp [dst]; omega),
      hkeep₁ _ ⟨by omega,Or.inl ha⟩]

/-- The original key-only API remains unchanged. -/
theorem Procs.meets {pMain h J maps free : ℕ} {μ : ℕ → ℤ} (S : Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+J+5 ≤ lim.depth)
    (hspace : space free h J ≤ lim.space) (hword : (word h J : ℤ) ≤ lim.word)
    (hmaps : maps+scheduleSize h*(2*(512*h)) ≤ free)
    (hreadFalse : ∀ j < scheduleSize h, ∀ i < 512*h,
      μ (maps+j*(2*(512*h))+i)=(BlockCoefficientRows.mapRow h false j i : ℤ))
    (hreadTrue : ∀ j < scheduleSize h, ∀ i < 512*h,
      μ (maps+j*(2*(512*h))+512*h+i)=(BlockCoefficientRows.mapRow h true j i : ℤ)) :
    Meets lim P pMain d [512*h,2*h,scheduleSize h,localPrime h,J,maps,
      outputCount (512*h) h,free] μ (time h J)
      (fun r ν => r=((scratch free h+LightRadixKeys.offset (localCount h) J : ℕ) : ℤ) ∧
        ν (scratch free h+LightRadixKeys.offset (localCount h) J)=((localCount h^J : ℕ) : ℤ) ∧
        Seg ν (scratch free h+LightRadixKeys.offset (localCount h) J+1) (globalKeys h J) ∧
        Kept μ ν free) := by
  exact (S.meets_with_masks hw hd hspace hword hmaps hreadFalse hreadTrue).mono le_rfl
    (fun _ _ ⟨hr,hc,hg,_,hk⟩ => ⟨hr,hc,hg,hk⟩)

def program : Program := [body 1 4 11,LightSubsetEnumerationSetup.body 2 3,powTableBody,
  LightSubsetEnumeration.body 3,LightLocalKeys.body 5 10,LightLocalKeyRow.body 6 7 9,
  fillBody,LightMaskHashes.body 2 8,LightOneHot.body 8,LightArray.linearBody,copyBody,
  LightRadixKeys.body 11 12,LightRadixRows.body 13,LightReportingAffine.body]

def programProcs : Procs program 0 :=
  ⟨1,2,3,4,11,12,13,rfl,rfl,rfl,rfl,⟨5,10,rfl,⟨6,7,2,8,9,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,
    rfl,rfl,rfl⟩

theorem program_length : program.length=14 := rfl

theorem time_bound (h J : ℕ) :
    time h J ≤ 2000*(512*h+1)*(outputCount (512*h) h+1)*(scheduleSize h+1)+
      300*(J+1)*(localCount h^J+1)+200 := by
  have he := LightSubsetEnumerationSetup.time_bound (512*h) (2*h)
  have hl := LightLocalKeys.time_bound (512*h) (outputCount (512*h) h) (scheduleSize h)
  have hg := LightRadixKeys.time_bound (localCount h) J (localCount_pos h)
  have hc : 800*(512*h+1)*(outputCount (512*h) h+1) ≤
      800*(512*h+1)*(outputCount (512*h) h+1)*(scheduleSize h+1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  change LightSubsetEnumerationSetup.time (512*h) (2*h) ≤
    800*(512*h+1)*(outputCount (512*h) h+1) at he
  unfold time
  nlinarith

end ThreeSum.LightGlobalKeys
