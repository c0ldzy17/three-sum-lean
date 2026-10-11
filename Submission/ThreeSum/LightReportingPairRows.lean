import Submission.ThreeSum.ReportingHostPairEnumeration
import Submission.ThreeSum.LightQueryEnumeration
import Submission.ThreeSum.LightSubsetEnumerationSetup
import Submission.ThreeSum.LightReportingAffine

/-!
# Actual direct construction of all local balanced row pairs

An own-power layer enumerator constructs the left subsets. For each left
subset, an actual output-sensitive query enumerator constructs its disjoint
right subsets, and an affine pass writes the matching repeated left mask.
-/

namespace ThreeSum.LightReportingPairRows

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPairEnumeration

set_option maxHeartbeats 1800000

variable {lim : Limits}

def roundBody (pQuery pAffine : ℕ) : Stmt :=
  .set 10 (M (v 2 +' v 9)) ;;
  .set 11 (v 7 -' v 10) ;;
  .call pQuery [v 0,v 11,v 1,v 4 +' v 8,v 5] 12 ;;
  .call pAffine [v 4 +' v 8,v 3 +' v 8,v 12,v 10,k 0] 13 ;;
  .set 8 (v 8 +' v 12)

def body (pLayer pQuery pAffine : ℕ) : Stmt :=
  .call pLayer [v 0,v 1,v 2,v 5] 6 ;;
  .set 7 (M (v 5 +' v 0) -' k 1) ;;
  .set 8 (k 0) ;;
  .for 9 (v 6) (roundBody pQuery pAffine) ;;
  .set 0 (v 8)

def program : Program := LightQueryEnumeration.program ++
  [LightSubsetEnumerationSetup.body 2 4,LightReportingAffine.body,body 5 0 6]

def roundTime (L h : ℕ) : ℕ :=
  LightQueryEnumeration.time L (L-h) h+LightReportingAffine.time ((L-h).choose h)+220

def time (L h : ℕ) : ℕ :=
  LightSubsetEnumerationSetup.time L h+L.choose h*(roundTime L h+20)+130

def Inv (μ : ℕ → ℤ) (L h srcS dstL dstR work j : ℕ) (σ : State) : Prop :=
  ∃ (a b nr r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [L,h,srcS,dstL,dstR,work,L.choose h,subsetMask (Finset.univ : Finset (Fin L)),
      j*(L-h).choose h,j,a,b,nr,r],μ'⟩ ∧
    SegN μ' srcS (enumerateLayer L h) ∧
    (∀ i < j, ∀ l < (L-h).choose h,
      μ' (dstL+i*(L-h).choose h+l) = (subsetMask (leftAt L h i) : ℤ) ∧
      μ' (dstR+i*(L-h).choose h+l) = (subsetMask (rightAt L h i l) : ℤ)) ∧
    Kept μ μ' srcS

theorem program_meets {μ : ℕ → ℤ} {L h srcS dstL dstR work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hh : 2*h ≤ L)
    (hS : srcS+L.choose h ≤ dstL)
    (hL : dstL+L.choose h*(L-h).choose h ≤ dstR)
    (hR : dstR+L.choose h*(L-h).choose h ≤ work)
    (hspace : work+2*L+2 ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+L+3 ≤ lim.depth) :
    Meets lim program 7 d [L,h,srcS,dstL,dstR,work] μ (time L h)
      (fun r μ' => r = (L.choose (2*h)*(2*h).choose h : ℤ) ∧
        SegN μ' srcS (enumerateLayer L h) ∧
        (∀ i < L.choose h, ∀ j < (L-h).choose h,
          μ' (dstL+i*(L-h).choose h+j) = (subsetMask (leftAt L h i) : ℤ) ∧
          μ' (dstR+i*(L-h).choose h+j) = (subsetMask (rightAt L h i j) : ℤ)) ∧
        Kept μ μ' srcS) := by
  have hdeg : 0 < (L-h).choose h := Nat.choose_pos (by omega)
  have hverts : 0 < L.choose h := Nat.choose_pos (by omega)
  have hmask (S : Finset (Fin L)) : (subsetMask S : ℤ) ≤ lim.word := by
    have hb : subsetMask S ≤ 2^(L+1) := (Nat.le_of_lt (subsetMask_isMask S).1).trans
      (Nat.pow_le_pow_right (by decide) (by omega))
    exact (Int.ofNat_le.mpr hb).trans hword
  have hfullWord := hmask (Finset.univ : Finset (Fin L))
  apply Meets.of_body (p := 7) (by rfl : program[7]? = some (body 5 0 6))
  unfold body time
  have hs := LightSubsetEnumerationSetup.meets (P := program) (pMain := 5) (pPowers := 2)
    (pEnum := 4) (d := d+1) (μ := μ) (L := L) (k := h) (dst := srcS) (work := work)
    rfl rfl rfl hw (by omega) hword (by omega) (by omega) (by omega)
  light_call hs using LightSubsetEnumerationSetup.time,roundTime
    with len μ₁ ⟨hlen,hlefts,hpowers,hkeepLayer⟩
  subst len
  have hpow := hpowers L le_rfl
  have hpowNat : μ₁ (work+L) = ((2^L : ℕ) : ℤ) := by simpa using hpow
  have hfull : ((2^L : ℕ) : ℤ)-1 = (subsetMask (Finset.univ : Finset (Fin L)) : ℤ) := by
    have he : (subsetMask (Finset.univ : Finset (Fin L)) : ℤ)+1 = ((2^L : ℕ) : ℤ) := by
      exact_mod_cast subsetMask_univ_succ L
    omega
  have hfullInt : (2 : ℤ)^L-1 = (subsetMask (Finset.univ : Finset (Fin L)) : ℤ) := by simpa using hfull
  light_set (subsetMask (Finset.univ : Finset (Fin L)) : ℕ)
    using hpow,hpowNat,hfull,hfullInt,LightSubsetEnumerationSetup.time,roundTime
  light_set (0 : ℕ) using LightSubsetEnumerationSetup.time,roundTime
  refine Ends.pieceThen (Ends.for (lim := lim) (P := program) (d := d) (i := 9) (hi := v 6)
    (body := roundBody 0 6) (T := L.choose h*(roundTime L h+20)+70)
    (Q := Inv μ L h srcS dstL dstR work (L.choose h))
    (Inv μ L h srcS dstL dstR work) (L.choose h) (roundTime L h)
    ?start ?round ?done ?bound (hT := by light_time [roundTime])) ?after
  case start =>
    refine ⟨0,0,0,0,μ₁,?_,hlefts,?_,?_⟩
    · simp [update_frame_setLocal]
      change frame [(L : ℤ),h,srcS,dstL,dstR,work,L.choose h,
        subsetMask (Finset.univ : Finset (Fin L)),0,0] =
        frame ([(L : ℤ),h,srcS,dstL,dstR,work,L.choose h,
          subsetMask (Finset.univ : Finset (Fin L)),0,0] ++ [0,0,0,0])
      exact (frame_append_zeros _ 4).symm
    · intro i hi; omega
    · intro i hi
      exact hkeepLayer i ⟨by omega,Or.inl hi⟩
  case round =>
    rintro j _ hj _ ⟨a,b,nr,r,μ',rfl,hlefts,hout,hkeep⟩
    have hjD : j*(L-h).choose h+(L-h).choose h ≤ L.choose h*(L-h).choose h := by
      have hm := Nat.mul_le_mul_right ((L-h).choose h) (show j+1 ≤ L.choose h by omega)
      nlinarith
    have hleftCard := leftAt_card hj
    have hcomp : (Finset.univ \ leftAt L h j).card = L-h := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin,hleftCard]
    have hread : μ' (srcS+j) = (subsetMask (leftAt L h j) : ℤ) := by
      have hget := hlefts j (by simpa only [List.length_map,enumerateLayer_length] using hj)
      simpa only [List.getElem_map,leftAt_mask hj] using hget
    have hlword := hmask (leftAt L h j)
    have hcword := hmask (Finset.univ \ leftAt L h j)
    have hdiff := MaskDifference.subsetMask_sdiff_int Finset.univ (leftAt L h j) (Finset.subset_univ _)
    unfold roundBody
    light_set (subsetMask (leftAt L h j) : ℕ) using hread,roundTime
    light_set (subsetMask (Finset.univ \ leftAt L h j) : ℕ) using hdiff,roundTime
    have hq := LightQueryEnumeration.meets (P := program) (pMain := 0) (pWeights := 1)
      (pPowers := 2) (pErase := 3) (pEnum := 4) (d := d+1) (μ := μ')
      (dst := dstR+j*(L-h).choose h) (work := work) (t := h)
      rfl rfl rfl rfl rfl (Finset.univ \ leftAt L h j) hw (by omega) hword
      (by rw [hcomp]; omega) (by rw [hcomp]; omega) (by omega)
    rw [hcomp] at hq
    light_call hq using roundTime with count ν ⟨hcount,hnewR,hweights,hkeepQuery⟩
    have ha := LightReportingAffine.meets (P := program) (p := 6) (d := d+1)
      (μ := ν) (src := dstR+j*(L-h).choose h) (dst := dstL+j*(L-h).choose h)
      (n := (L-h).choose h) (b := (subsetMask (leftAt L h j) : ℤ)) (c := 0)
      rfl hw (by omega) (by omega) (Or.inr (by omega))
      (by intro i hi; simp only [zero_mul,abs_zero]; omega)
      (by intro i hi; simpa only [zero_mul,add_zero,Int.abs_natCast] using hlword)
    light_call ha using hcount,roundTime with affineRet ξ ⟨hnewL,hkeepAffine⟩
    light_set ((j+1)*(L-h).choose h : ℕ) using hcount,Nat.add_mul,roundTime
    refine ⟨by simp,(subsetMask (leftAt L h j) : ℤ),
      (subsetMask (Finset.univ \ leftAt L h j) : ℤ),count,affineRet,ξ,?_,?_,?_,?_⟩
    · simp [update_frame_setLocal]
    · intro i hi
      rw [hkeepAffine (srcS+i) (Or.inl (by simp only [List.length_map,enumerateLayer_length] at hi; omega)),
        hkeepQuery (srcS+i) ⟨by simp only [List.length_map,enumerateLayer_length] at hi; omega,
          Or.inl (by simp only [List.length_map,enumerateLayer_length] at hi; omega)⟩]
      exact hlefts i hi
    · intro i hi l hl
      by_cases he : i = j
      · subst i
        constructor
        · simpa only [zero_mul,add_zero,Nat.add_assoc] using hnewL l hl
        · rw [hkeepAffine _ (Or.inr (by omega))]
          have hlen : l < (rights (leftAt L h j) h).length := by rw [rights_length _ hleftCard]; exact hl
          have hr := hnewR l (by simpa only [List.length_map,rights] using hlen)
          simpa only [List.getElem_map,Nat.add_assoc,rights,rightAt_eq_get hj hl] using hr
      · have hij : i < j := by omega
        have hm := Nat.mul_le_mul_right ((L-h).choose h) (show i+1 ≤ j by omega)
        obtain ⟨hprevL,hprevR⟩ := hout i hij l hl
        constructor
        · rw [hkeepAffine _ (Or.inl (by nlinarith)),hkeepQuery _ ⟨by nlinarith,Or.inl (by nlinarith)⟩]
          exact hprevL
        · rw [hkeepAffine _ (Or.inr (by omega)),hkeepQuery _ ⟨by nlinarith,Or.inl (by nlinarith)⟩]
          exact hprevR
    · intro i hi
      exact (hkeepAffine i (Or.inl (by omega))).trans
        ((hkeepQuery i ⟨by omega,Or.inl (by omega)⟩).trans (hkeep i hi))
  case done =>
    intro σ _ hσ
    exact hσ
  case bound =>
    rintro j _ hj _ ⟨a,b,nr,r,μ',rfl,_,_,_⟩
    light_side
  case after =>
    rintro _ ⟨a,b,nr,r,μ',rfl,hlefts,hout,hkeep⟩
    light_set (L.choose h*(L-h).choose h : ℕ) using roundTime
    refine ⟨?_,hlefts,hout,hkeep⟩
    simp only [LayerCounts.vertex_degree_identity]
    rfl

theorem time_bound {L h : ℕ} (hh : 2*h ≤ L) :
    time L h ≤ 4000*(L+1)^2*(L.choose (2*h)*(2*h).choose h+1) := by
  have hdeg : 0 < (L-h).choose h := Nat.choose_pos (by omega)
  have hs := LightSubsetEnumerationSetup.time_bound L h
  have hq := LightQueryEnumeration.time_bound (t := h) (Nat.sub_le L h)
  have hlinear : L+1 ≤ (L+1)^2 := by nlinarith
  have hv : L.choose h ≤ L.choose h*(L-h).choose h := Nat.le_mul_of_pos_right _ hdeg
  have hm := Nat.mul_le_mul_left (L.choose h) hq
  rw [← LayerCounts.vertex_degree_identity]
  unfold time roundTime LightReportingAffine.time
  nlinarith

end ThreeSum.LightReportingPairRows
