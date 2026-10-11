import Submission.ThreeSum.LightSubsetAddress

/-!
# A complete subset-rank program, including table construction

This fixed program constructs both lookup tables in scratch and then ranks
one valid mask. Its cost is quadratic in the bit width. The faster cached
rank contract remains available separately, but no supplied table correctness
assumption appears in the fixed-program result below.
-/

namespace ThreeSum.LightSubsetSetup

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

/-- Arguments: bit width, cardinality, mask, scratch base. -/
def body (pBuild pPowers pRank : ℕ) : Stmt :=
  .set 4 (v 3 +' (v 0 +' k 1) *' (v 0 +' k 1)) ;;
  .call pBuild [v 3,v 0] 5 ;;
  .call pPowers [v 4,v 0 +' k 1,k 2] 5 ;;
  .call pRank [v 0,v 1,v 2,v 0,v 3,v 4] 0

def time (L : ℕ) : ℕ := buildTime L + powTableTime (L+1) + rankTime L + 60

structure Procs (P : Program) (pMain pBuild pFill pRow pLinear pPowers pRank : ℕ) : Prop where
  main : P[pMain]? = some (body pBuild pPowers pRank)
  build : P[pBuild]? = some (buildBody pFill pRow)
  fill : P[pFill]? = some fillBody
  row : P[pRow]? = some (rowBody pLinear)
  linear : P[pLinear]? = some LightArray.linearBody
  powers : P[pPowers]? = some powTableBody
  rank : P[pRank]? = some (rankBody pRank)

theorem meets {pMain pBuild pFill pRow pLinear pPowers pRank : ℕ}
    (C : Procs P pMain pBuild pFill pRow pLinear pPowers pRank)
    {μ : ℕ → ℤ} {L k m work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hm : IsMask L k m) (hd : d+L+3 ≤ lim.depth) :
    Meets lim P pMain d [L,k,m,work] μ (time L)
      (fun r μ' => r = (layerRank L k m : ℤ) ∧ Table μ' work L ∧
        Powers μ' (work+tableSize L) L ∧ Kept μ μ' work) := by
  have hsize : L+1 ≤ tableSize L := by unfold tableSize; nlinarith
  have hcastSize : ((L : ℤ)+1)*((L : ℤ)+1) = (tableSize L : ℤ) := by
    simp [tableSize, pow_two]
  apply Meets.of_body C.main
  unfold body time
  light_set (work+tableSize L : ℕ) using buildTime, rowTime, LightArray.linearTime,
    powTableTime, rankTime
  have hbuild := build_meets (d := d+1) (μ := μ) (dst := work) (L := L)
    C.build C.fill C.row C.linear hw (by omega) (by omega) hword
  light_call hbuild using buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime
    with _ μ₁ ⟨htable,hkept₁⟩
  have hpowers := powTable_meets (d := d+1) (μ := μ₁) (dst := work+tableSize L)
    (L := L+1) (b := 2) C.powers hw hspace (by
      intro j hj
      have hb : (2^j : ℕ) ≤ 2^(L+1) := Nat.pow_le_pow_right (by decide) hj
      have hbZ : ((2^j : ℕ) : ℤ) ≤ ((2^(L+1) : ℕ) : ℤ) := by exact_mod_cast hb
      exact hbZ.trans hword)
  light_call hpowers using buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime
    with _ μ₂ ⟨hpSeg,hkept₂⟩
  have htable₂ : Table μ₂ work L := by
    intro i hi j hj
    have hb := cell_offset_lt hi hj
    rw [hkept₂ _ (by omega)]
    exact htable i hi j hj
  have hpowSpec := powers_of_segment hpSeg
  have hrank := rank_meets C.rank μ₂ hw (by omega) hspace hword htable₂ hpowSpec
    L k m le_rfl hm (d+1) (by omega)
  light_call hrank using buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime
    with res μ₃ ⟨hres,hmem⟩
  subst μ₃
  refine ⟨by simpa using hres, htable₂, hpowSpec, ?_⟩
  intro a ha
  exact (hkept₂ a (by omega)).trans (hkept₁ a (by omega))

def program : Program :=
  [body 1 5 6, buildBody 2 3, fillBody, rowBody 4,
    LightArray.linearBody, powTableBody, rankBody 6]

theorem program_procs : Procs program 0 1 2 3 4 5 6 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem program_meets {μ : ℕ → ℤ} {L k m work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hm : IsMask L k m) (hd : d+L+3 ≤ lim.depth) :
    Meets lim program 0 d [L,k,m,work] μ (time L)
      (fun r μ' => r = (layerRank L k m : ℤ) ∧ Table μ' work L ∧
        Powers μ' (work+tableSize L) L ∧ Kept μ μ' work) :=
  meets program_procs hw hspace hword hm hd

theorem time_bound (L : ℕ) : time L ≤ 1200*(L+1)^2 := by
  have hb := buildTime_bound L
  unfold time powTableTime rankTime
  nlinarith

end ThreeSum.LightSubsetSetup
