import Submission.ThreeSum.LightSubsetSetup
import Submission.ThreeSum.LightSubsetOffset

/-!
# A fixed program for the complete compact downset address

The input gives a mask and its known cardinality. The program constructs
its own Pascal and power tables, computes the layer rank, scans the layer
offset, and returns their sum. No table-correctness or algorithmic runtime
premise is supplied by the caller.
-/

namespace ThreeSum.LightDownsetAddress

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def body (pFresh pOffset : ℕ) : Stmt :=
  .call pFresh [v 0,v 1,v 2,v 3] 4 ;;
  .call pOffset [v 3,v 0,v 1,v 0] 5 ;;
  .set 0 (v 4 +' v 5)

def time (L : ℕ) : ℕ := LightSubsetSetup.time L + LightSubsetOffset.time L + 30

theorem meets {pMain pFresh pBuild pFill pRow pLinear pPowers pRank pOffset : ℕ}
    (hmain : P[pMain]? = some (body pFresh pOffset))
    (C : LightSubsetSetup.Procs P pFresh pBuild pFill pRow pLinear pPowers pRank)
    (hoff : P[pOffset]? = some LightSubsetOffset.body)
    {μ : ℕ → ℤ} {L k m work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hm : IsMask L k m) (hd : d+L+4 ≤ lim.depth) :
    Meets lim P pMain d [L,k,m,work] μ (time L)
      (fun r μ' => r = (downsetRank L m : ℤ) ∧ Kept μ μ' work) := by
  have hk := hm.le_width
  have hword₀ : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word := by
    have hb : (2^(L+1) : ℕ) ≤ (L+1)*2^(L+1) := Nat.le_mul_of_pos_left _ (by omega)
    have hbZ : ((2^(L+1) : ℕ) : ℤ) ≤ (((L+1)*2^(L+1) : ℕ) : ℤ) := by
      exact_mod_cast hb
    exact hbZ.trans hword
  have hrank := (layerRank_lt hm).trans_le (Nat.choose_le_two_pow L k)
  have hoffset := LightSubsetOffset.layerOffset_bound L k
  have hscale := Nat.mul_le_mul_right (2^L) hk
  have hdouble := Nat.mul_le_mul_left (L+1)
    (show (2^L : ℕ) ≤ 2^(L+1) from Nat.pow_le_pow_right (by decide) (by omega))
  have hsumNat : layerRank L k m + layerOffset L k ≤ (L+1)*2^(L+1) := by
    nlinarith
  have hsum : (layerRank L k m : ℤ)+(layerOffset L k : ℤ) ≤ lim.word := by
    have hbZ : (layerRank L k m : ℤ)+(layerOffset L k : ℤ) ≤
        (((L+1)*2^(L+1) : ℕ) : ℤ) := by exact_mod_cast hsumNat
    exact hbZ.trans hword
  have hrNonneg : (0 : ℤ) ≤ (layerRank L k m : ℤ) := Int.natCast_nonneg _
  have hoNonneg : (0 : ℤ) ≤ (layerOffset L k : ℤ) := Int.natCast_nonneg _
  apply Meets.of_body hmain
  unfold body time
  have hsetup := LightSubsetSetup.meets (d := d+1) (μ := μ) C hw hspace hword₀ hm (by omega)
  light_call hsetup using LightSubsetSetup.time, LightSubsetOffset.time,
    buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime
    with rank μ₁ ⟨hr,hT,hPow,hKept⟩
  have hscan := LightSubsetOffset.meets (d := d+1) hoff μ₁ hw (by omega) hword hT le_rfl hk
  light_call hscan using LightSubsetSetup.time, LightSubsetOffset.time,
    buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime
    with offset μ₂ ⟨ho,hmem⟩
  subst μ₂
  light_set ((layerRank L k m + layerOffset L k : ℕ)) using hr,ho,
    LightSubsetSetup.time, LightSubsetOffset.time,
    buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime
  refine ⟨?_,hKept⟩
  simp [downsetRank,hm.2,Nat.add_comm]

def program : Program :=
  [body 1 8, LightSubsetSetup.body 2 6 7, buildBody 3 4, fillBody, rowBody 5,
    LightArray.linearBody, powTableBody, rankBody 7, LightSubsetOffset.body]

theorem program_procs : LightSubsetSetup.Procs program 1 2 3 4 5 6 7 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem program_meets {μ : ℕ → ℤ} {L k m work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hm : IsMask L k m) (hd : d+L+4 ≤ lim.depth) :
    Meets lim program 0 d [L,k,m,work] μ (time L)
      (fun r μ' => r = (downsetRank L m : ℤ) ∧ Kept μ μ' work) :=
  meets rfl program_procs rfl hw hspace hword hm hd

theorem time_bound (L : ℕ) : time L ≤ 1300*(L+1)^2 := by
  have h := LightSubsetSetup.time_bound L
  unfold time LightSubsetOffset.time
  nlinarith

end ThreeSum.LightDownsetAddress
