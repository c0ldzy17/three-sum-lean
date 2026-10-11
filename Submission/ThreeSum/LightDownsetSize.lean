import Submission.ThreeSum.LightSubsetSetup
import Submission.ThreeSum.LightSubsetOffset

/-!
# Computing the compact downset size

The program builds a Pascal table, scans all preceding layers, and adds
the final binomial coefficient. The table stride used by the transform
is therefore computed by an actual fixed program.
-/

namespace ThreeSum.LightDownsetSize

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

/-- Arguments: width, cutoff, polynomial scratch base. -/
def body (pSetup pOffset : ℕ) : Stmt :=
  .call pSetup [v 0,k 0,k 0,v 2] 3 ;;
  .call pOffset [v 2,v 0,v 1,v 0] 4 ;;
  .set 0 (v 4 +' M (v 2 +' v 0 *' (v 0 +' k 1) +' v 1))

def time (L : ℕ) : ℕ := LightSubsetSetup.time L+LightSubsetOffset.time L+60

theorem cap_eq {L cut : ℕ} (hcut : cut ≤ L) :
    downsetCap L cut = layerOffset L cut+L.choose cut := by
  simp only [downsetCap,Nat.min_eq_left hcut,layerOffset_succ]

theorem meets {pMain pSetup pBuild pFill pRow pLinear pPowers pRank pOffset : ℕ}
    (hmain : P[pMain]? = some (body pSetup pOffset))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body)
    {μ : ℕ → ℤ} {L cut work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hcut : cut ≤ L) (hd : d+L+4 ≤ lim.depth) :
    Meets lim P pMain d [L,cut,work] μ (time L)
      (fun r μ' => r = (downsetCap L cut : ℤ) ∧ Kept μ μ' work) := by
  have hword₀ : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : (2^(L+1) : ℕ) ≤ (L+1)*2^(L+1) := Nat.le_mul_of_pos_left _ (by omega)
    exact (by exact_mod_cast hh : ((2^(L+1) : ℕ) : ℤ) ≤
      (((L+1)*2^(L+1) : ℕ) : ℤ)).trans hword
  have hpow : (2^L : ℕ) ≤ 2^(L+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hsmall := LightSubsetOffset.layerOffset_bound L cut
  have hchoose := Nat.choose_le_two_pow L cut
  have hprod := Nat.mul_le_mul hcut hpow
  have hbound : downsetCap L cut ≤ (L+1)*2^(L+1) := by
    rw [cap_eq hcut]
    nlinarith
  have hboundZ : (downsetCap L cut : ℤ) ≤ lim.word :=
    (by exact_mod_cast hbound : (downsetCap L cut : ℤ) ≤
      (((L+1)*2^(L+1) : ℕ) : ℤ)).trans hword
  have hcast : (L : ℤ)*((L : ℤ)+1) = ((L*(L+1) : ℕ) : ℤ) := by push_cast; rfl
  apply Meets.of_body hmain
  unfold body time
  have hs := LightSubsetSetup.meets (d := d+1) (μ := μ) (L := L) (k := 0) (m := 0)
    C hw hspace hword₀ (by simp) (by omega)
  light_call hs using LightSubsetSetup.time,LightSubsetOffset.time,buildTime,rowTime,
    LightArray.linearTime,powTableTime,rankTime with _ μ₁ ⟨_,hTable,_,hKept⟩
  have ho := LightSubsetOffset.meets (d := d+1) hOffset μ₁ hw (by omega) hword hTable le_rfl hcut
  light_call ho using LightSubsetSetup.time,LightSubsetOffset.time,buildTime,rowTime,
    LightArray.linearTime,powTableTime,rankTime with off μ₂ ⟨hoff,hmem⟩
  subst μ₂
  have hread := hTable L le_rfl cut hcut
  have hcell := cell_offset_lt (show L ≤ L from le_rfl) hcut
  have haddr : ((work : ℤ)+(L : ℤ)*((L : ℤ)+1)+(cut : ℤ)).toNat = work+L*(L+1)+cut := by
    have hh : (work : ℤ)+(L : ℤ)*((L : ℤ)+1)+(cut : ℤ) = ((work+L*(L+1)+cut : ℕ) : ℤ) := by
      push_cast
      rfl
    rw [hh,Int.toNat_natCast]
  have hreadZ : μ₁ (((work : ℤ)+(L : ℤ)*((L : ℤ)+1)+(cut : ℤ)).toNat) = (L.choose cut : ℤ) := by
    rw [haddr,hread]
  have hsum : (layerOffset L cut : ℤ)+(L.choose cut : ℤ) = (downsetCap L cut : ℤ) := by
    rw [cap_eq hcut,Nat.cast_add]
  have hn₁ : (0 : ℤ) ≤ layerOffset L cut := Int.natCast_nonneg _
  have hn₂ : (0 : ℤ) ≤ L.choose cut := Int.natCast_nonneg _
  light_set (downsetCap L cut : ℕ) using hoff,hreadZ,hsum,
    LightSubsetSetup.time,LightSubsetOffset.time,buildTime,rowTime,
    LightArray.linearTime,powTableTime,rankTime
  exact ⟨by simp,hKept⟩

def program : Program :=
  [body 1 8,LightSubsetSetup.body 2 6 7,buildBody 3 4,fillBody,rowBody 5,
    LightArray.linearBody,powTableBody,rankBody 7,LightSubsetOffset.body]

theorem program_procs : LightSubsetSetup.Procs program 1 2 3 4 5 6 7 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem program_meets {μ : ℕ → ℤ} {L cut work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hcut : cut ≤ L) (hd : d+L+4 ≤ lim.depth) :
    Meets lim program 0 d [L,cut,work] μ (time L)
      (fun r μ' => r = (downsetCap L cut : ℤ) ∧ Kept μ μ' work) :=
  meets rfl program_procs rfl hw hspace hword hcut hd

theorem time_bound (L : ℕ) : time L ≤ 1400*(L+1)^2 := by
  have hh := LightSubsetSetup.time_bound L
  have hp : 1 ≤ (L+1)^2 := Nat.one_le_pow' 2 L
  unfold time LightSubsetOffset.time
  nlinarith

end ThreeSum.LightDownsetSize
