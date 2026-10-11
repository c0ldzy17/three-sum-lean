import Submission.ThreeSum.LightMaskErase
import Submission.ThreeSum.LightSubsetSetup
import Submission.ThreeSum.LightSubsetOffset
import Submission.ThreeSum.Subset

/-!
# An actual compact-table zeta-cell update

The fixed procedure builds its own Pascal and power tables, ranks the input
mask, deletes the requested coordinate, ranks the smaller mask if necessary,
and writes the zeta addition at the compact downset address. The scratch area
is polynomial in the width. Neither addresses nor table values are supplied
by an oracle.
-/

namespace ThreeSum.LightZetaCell

open Light ThreeSum.SubsetAddress ThreeSum.MaskErase
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

/-- Correct contents at all compact addresses within the stored downset. -/
def TableAt {L : ℕ} (μ : ℕ → ℤ) (src cut : ℕ) (f : Finset (Fin L) → ℤ) : Prop :=
  ∀ S, S.card ≤ cut → μ (src+subsetRank S) = f S

def KeptExcept (μ μ' : ℕ → ℤ) (work changed : ℕ) : Prop :=
  ∀ i < work, i ≠ changed → μ' i = μ i

/-- Arguments: width, cardinality, mask, coordinate, source, destination,
and scratch. The destination contains only `downsetCap` data cells. -/
def body (pSetup pOffset pErase pRank : ℕ) : Stmt :=
  .set 10 (v 6 +' (v 0 +' k 1) *' (v 0 +' k 1)) ;;
  .call pSetup [v 0,v 1,v 2,v 6] 7 ;;
  .call pOffset [v 6,v 0,v 1,v 0] 8 ;;
  .set 9 (v 7 +' v 8) ;;
  .call pErase [v 0,v 3,v 2,v 0,v 10] 11 ;;
  .ite (v 11 <' v 2)
    (.call pRank [v 0,v 1 -' k 1,v 11,v 0,v 6,v 10] 12 ;;
      .call pOffset [v 6,v 0,v 1 -' k 1,v 0] 13 ;;
      .set 14 (v 12 +' v 13) ;;
      .store (v 5 +' v 9) (M (v 4 +' v 9) +' M (v 4 +' v 14)))
    (.store (v 5 +' v 9) (M (v 4 +' v 9)))

def time (L : ℕ) : ℕ := LightSubsetSetup.time L +
  LightMaskErase.time L + rankTime L + 2*LightSubsetOffset.time L + 200

private theorem rank_offset {L : ℕ} (S : Finset (Fin L)) :
    layerRank L S.card (subsetMask S) + layerOffset L S.card = subsetRank S := by
  simp only [subsetRank, downsetRank, (subsetMask_isMask S).2, Nat.add_comm]

theorem meets {pThis pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hThis : P[pThis]? = some (body pSetup pOffset pErase pRank))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body)
    (hErase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L cut src dst work U d : ℕ}
    (S : Finset (Fin L)) (a : Fin L) (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+downsetCap L cut ≤ work) (hdst : dst+downsetCap L cut ≤ work)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : 2*(U : ℤ) ≤ lim.word)
    (hread : TableAt μ src cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U)
    (hS : S.card ≤ cut) (hd : d+L+4 ≤ lim.depth) :
    Meets lim P pThis d [L,S.card,subsetMask S,a.val,src,dst,work] μ (time L)
      (fun _ μ' => μ' (dst+subsetRank S) = Subset.zetaStep a f S ∧
        KeptExcept μ μ' work (dst+subsetRank S)) := by
  have hm := subsetMask_isMask S
  have hk := hm.le_width
  have hrS := subsetRank_lt hS
  have hword₀ : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : (2^(L+1) : ℕ) ≤ (L+1)*2^(L+1) := Nat.le_mul_of_pos_left _ (by omega)
    exact (by exact_mod_cast hh : ((2^(L+1) : ℕ) : ℤ) ≤
      (((L+1)*2^(L+1) : ℕ) : ℤ)).trans hword
  have hfS := abs_le.mp (hvalues S hS)
  have hRankSum : (layerRank L S.card (subsetMask S) : ℤ) +
      (layerOffset L S.card : ℤ) = (subsetRank S : ℤ) := by
    exact_mod_cast rank_offset S
  have hRankNonneg : (0 : ℤ) ≤ layerRank L S.card (subsetMask S) := Int.natCast_nonneg _
  have hOffsetNonneg : (0 : ℤ) ≤ layerOffset L S.card := Int.natCast_nonneg _
  have hcastSize : ((L : ℤ)+1)*((L : ℤ)+1) = (tableSize L : ℤ) := by
    simp [tableSize,pow_two]
  apply Meets.of_body hThis
  unfold body time
  light_set (work+tableSize L : ℕ) using hcastSize
  have hSetup := LightSubsetSetup.meets (d := d+1) (μ := μ) C hw hspace hword₀ hm (by omega)
  light_call hSetup using LightSubsetSetup.time, LightMaskErase.time, rankTime,
    LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime, powTableTime
    with fullRank μ₁ ⟨hFullRank,hTable,hPowers,hKept⟩
  have hSread : μ₁ (src+subsetRank S) = f S :=
    (hKept _ (by omega)).trans (hread S hS)
  have hOff := LightSubsetOffset.meets (d := d+1) hOffset μ₁ hw (by omega) hword hTable le_rfl hk
  light_call hOff using LightSubsetSetup.time, LightMaskErase.time, rankTime,
    LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime, powTableTime
    with fullOffset μ₂ ⟨hFullOffset,hmem⟩
  subst μ₂
  light_set (subsetRank S : ℕ) using hFullRank,hFullOffset,hRankSum,
    LightSubsetSetup.time, LightMaskErase.time, rankTime, LightSubsetOffset.time,
    buildTime, rowTime, LightArray.linearTime, powTableTime
  have hDel := LightMaskErase.meets hErase μ₁ hw hspace hword₀ hPowers
    L a.val (subsetMask S) le_rfl (Nat.le_of_lt a.isLt) hm.1 (d+1) (by omega)
  light_call hDel using LightSubsetSetup.time, LightMaskErase.time, rankTime,
    LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime, powTableTime
    with erased μ₂ ⟨hErased,hmem⟩
  subst μ₂
  light_if hbitZ hnotZ : (eraseMask L a.val (subsetMask S) : ℤ) < (subsetMask S : ℤ)
    using hErased, LightSubsetSetup.time, LightMaskErase.time, rankTime, LightSubsetOffset.time,
      buildTime, rowTime, LightArray.linearTime, powTableTime
  · have ha : a ∈ S := (eraseMask_lt_iff S a).mp (by exact_mod_cast hbitZ)
    have hkpos : 0 < S.card := Finset.card_pos.mpr ⟨a,ha⟩
    have hsubCard : (S.card : ℤ)-1 = ((S.card-1 : ℕ) : ℤ) := by omega
    have hE : (S.erase a).card ≤ cut := (Finset.card_le_card (Finset.erase_subset _ _)).trans hS
    have hrE := subsetRank_lt hE
    have hfE := abs_le.mp (hvalues (S.erase a) hE)
    have hEread : μ₁ (src+subsetRank (S.erase a)) = f (S.erase a) :=
      (hKept _ (by omega)).trans (hread _ hE)
    have hMask := eraseMask_isMask S a ha
    have hkE : S.card-1 ≤ L := by omega
    have hRankE : (layerRank L (S.card-1) (eraseMask L a.val (subsetMask S)) : ℤ) +
        (layerOffset L (S.card-1) : ℤ) = (subsetRank (S.erase a) : ℤ) := by
      rw [eraseMask_subsetMask, ← Finset.card_erase_of_mem ha]
      exact_mod_cast rank_offset (S.erase a)
    have hRankENonneg : (0 : ℤ) ≤ layerRank L (S.card-1) (eraseMask L a.val (subsetMask S)) :=
      Int.natCast_nonneg _
    have hOffsetENonneg : (0 : ℤ) ≤ layerOffset L (S.card-1) := Int.natCast_nonneg _
    have hRankCall := rank_meets C.rank μ₁ hw (by omega) hspace hword₀ hTable hPowers
      L (S.card-1) (eraseMask L a.val (subsetMask S)) le_rfl hMask (d+1) (by omega)
    light_call hRankCall using hErased, hsubCard, LightSubsetSetup.time, LightMaskErase.time, rankTime,
      LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime, powTableTime
      with erasedRank μ₂ ⟨hErasedRank,hmem⟩
    subst μ₂
    have hOffCall := LightSubsetOffset.meets (d := d+1) hOffset μ₁ hw (by omega)
      hword hTable le_rfl hkE
    light_call hOffCall using hsubCard, LightSubsetSetup.time, LightMaskErase.time, rankTime,
      LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime, powTableTime
      with erasedOffset μ₂ ⟨hErasedOffset,hmem⟩
    subst μ₂
    light_set (subsetRank (S.erase a) : ℕ) using hErasedRank,hErasedOffset,hRankE,
      LightSubsetSetup.time, LightMaskErase.time, rankTime, LightSubsetOffset.time,
      buildTime, rowTime, LightArray.linearTime, powTableTime
    light_store (dst+subsetRank S) (f S + f (S.erase a)) using hSread,hEread,
      LightSubsetSetup.time, LightMaskErase.time, rankTime, LightSubsetOffset.time,
      buildTime, rowTime, LightArray.linearTime, powTableTime
    constructor
    · simp only [Function.update_self, Subset.zetaStep, ha, ite_true]
    · intro i hi hne
      change Function.update μ₁ (dst+subsetRank S) (f S + f (S.erase a)) i = μ i
      rw [Function.update_of_ne hne]
      exact hKept i hi
  · have ha : a ∉ S := by
      intro ha
      exact hnotZ (by exact_mod_cast (eraseMask_lt_iff S a).mpr ha)
    light_store (dst+subsetRank S) (f S) using hSread,
      LightSubsetSetup.time, LightMaskErase.time, rankTime, LightSubsetOffset.time,
      buildTime, rowTime, LightArray.linearTime, powTableTime
    constructor
    · simp only [Function.update_self, Subset.zetaStep, ha, ite_false]
    · intro i hi hne
      change Function.update μ₁ (dst+subsetRank S) (f S) i = μ i
      rw [Function.update_of_ne hne]
      exact hKept i hi

def program : Program :=
  [body 1 8 9 7, LightSubsetSetup.body 2 6 7, buildBody 3 4, fillBody, rowBody 5,
    LightArray.linearBody, powTableBody, rankBody 7, LightSubsetOffset.body, LightMaskErase.body 9]

theorem program_procs : LightSubsetSetup.Procs program 1 2 3 4 5 6 7 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem program_meets {μ : ℕ → ℤ} {L cut src dst work U d : ℕ}
    (S : Finset (Fin L)) (a : Fin L) (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+downsetCap L cut ≤ work) (hdst : dst+downsetCap L cut ≤ work)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : 2*(U : ℤ) ≤ lim.word)
    (hread : TableAt μ src cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U)
    (hS : S.card ≤ cut) (hd : d+L+4 ≤ lim.depth) :
    Meets lim program 0 d [L,S.card,subsetMask S,a.val,src,dst,work] μ (time L)
      (fun _ μ' => μ' (dst+subsetRank S) = Subset.zetaStep a f S ∧
        KeptExcept μ μ' work (dst+subsetRank S)) :=
  meets rfl program_procs rfl rfl S a f hw hsrc hdst hspace hword hvalueWord hread hvalues hS hd

theorem time_bound (L : ℕ) : time L ≤ 2000*(L+1)^2 := by
  have h := LightSubsetSetup.time_bound L
  unfold time LightMaskErase.time LightSubsetOffset.time rankTime
  nlinarith

end ThreeSum.LightZetaCell
