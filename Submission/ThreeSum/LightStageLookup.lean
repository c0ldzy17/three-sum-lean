import Submission.ThreeSum.LightZetaStages
import Submission.ThreeSum.LightBoxStages
import Submission.ThreeSum.LightDownsetAddress

/-!
# Executing a stored partial-zeta or box lookup

This fixed program computes the compact downset stride and the queried
subset rank from freshly built tables. It then reads exactly one stored
stage cell. The specialized contracts connect that machine read to the
forced-prefix sum and to the canonical sparse-box sum.
-/

namespace ThreeSum.LightStageLookup

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def readAddr {L : ℕ} (cut base j : ℕ) (S : Finset (Fin L)) : ℕ :=
  base+j*downsetCap L cut+subsetRank S

/-- Arguments: width, cutoff, cardinality, mask, stage, table base,
polynomial scratch base. -/
def body (pSize pAddress : ℕ) : Stmt :=
  .call pSize [v 0,v 1,v 6] 7 ;;
  .call pAddress [v 0,v 2,v 3,v 6] 8 ;;
  .set 0 (M (v 5 +' v 4 *' v 7 +' v 8))

def time (L : ℕ) : ℕ := LightDownsetSize.time L+LightDownsetAddress.time L+50

theorem meets {pMain pSize pAddress pSetup pBuild pFill pRow pLinear pPowers pRank pOffset : ℕ}
    (hmain : P[pMain]? = some (body pSize pAddress))
    (hSize : P[pSize]? = some (LightDownsetSize.body pSetup pOffset))
    (hAddress : P[pAddress]? = some (LightDownsetAddress.body pSetup pOffset))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body)
    {μ : ℕ → ℤ} {L cut base j work d : ℕ} (S : Finset (Fin L)) (value : ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdata : base+(L+1)*downsetCap L cut ≤ work)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hS : S.card ≤ cut) (hj : j ≤ L)
    (hread : μ (readAddr cut base j S) = value) (hd : d+L+5 ≤ lim.depth) :
    Meets lim P pMain d [L,cut,S.card,subsetMask S,j,base,work] μ (time L)
      (fun r μ' => r = value ∧ Kept μ μ' work) := by
  have hr := subsetRank_lt hS
  have hmul := Nat.mul_le_mul_right (downsetCap L cut) (Nat.succ_le_succ hj)
  have haddr : readAddr cut base j S < work := by
    unfold readAddr
    simp only [Nat.succ_mul,Nat.add_mul,Nat.one_mul] at hmul hdata
    omega
  have hindex : j*downsetCap L cut ≤ readAddr cut base j S := by unfold readAddr; omega
  apply Meets.of_body hmain
  unfold body time
  have hs := LightDownsetSize.meets (d := d+1) (μ := μ)
    hSize C hOffset hw hspace hword hcut (by omega)
  light_call hs using LightDownsetSize.time,LightDownsetAddress.time with cap μ₁ ⟨hcap,hkeep₁⟩
  have ha := LightDownsetAddress.meets (d := d+1) (μ := μ₁)
    hAddress C hOffset hw hspace hword (subsetMask_isMask S) (by omega)
  light_call ha using LightDownsetSize.time,LightDownsetAddress.time with rank μ₂ ⟨hrank,hkeep₂⟩
  have hrankS : rank = (subsetRank S : ℤ) := hrank
  have hread₂ : μ₂ (readAddr cut base j S) = value :=
    (hkeep₂ _ haddr).trans ((hkeep₁ _ haddr).trans hread)
  have haddrZ : ((base : ℤ)+(j : ℤ)*(downsetCap L cut : ℤ)+(subsetRank S : ℤ)).toNat =
      readAddr cut base j S := by
    have hh : (base : ℤ)+(j : ℤ)*(downsetCap L cut : ℤ)+(subsetRank S : ℤ) =
        (readAddr cut base j S : ℤ) := by simp [readAddr]
    rw [hh,Int.toNat_natCast]
  have hreadZ : μ₂ (((base : ℤ)+(j : ℤ)*(downsetCap L cut : ℤ)+(subsetRank S : ℤ)).toNat) = value := by
    rw [haddrZ,hread₂]
  light_set value using hcap,hrankS,hreadZ,readAddr,LightDownsetSize.time,LightDownsetAddress.time
  exact ⟨by simp,hkeep₁.trans hkeep₂⟩

def program : Program :=
  [body 1 2,LightDownsetSize.body 3 10,LightDownsetAddress.body 3 10,
    LightSubsetSetup.body 4 8 9,buildBody 5 6,fillBody,rowBody 7,
    LightArray.linearBody,powTableBody,rankBody 9,LightSubsetOffset.body]

theorem program_procs : LightSubsetSetup.Procs program 3 4 5 6 7 8 9 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem program_meets {μ : ℕ → ℤ} {L cut base j work d : ℕ}
    (S : Finset (Fin L)) (value : ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdata : base+(L+1)*downsetCap L cut ≤ work)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hS : S.card ≤ cut) (hj : j ≤ L)
    (hread : μ (readAddr cut base j S) = value) (hd : d+L+5 ≤ lim.depth) :
    Meets lim program 0 d [L,cut,S.card,subsetMask S,j,base,work] μ (time L)
      (fun r μ' => r = value ∧ Kept μ μ' work) :=
  meets rfl rfl rfl program_procs rfl S value hw hcut hdata hspace hword hS hj hread hd

theorem box_program_meets {μ : ℕ → ℤ} {L cut base j work d : ℕ}
    (flags : Finset (Fin L)) (weight : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdata : base+(L+1)*downsetCap L cut ≤ work)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hflags : flags.card ≤ cut) (hj : j ≤ L)
    (hstored : LightBoxStages.StoredThrough μ base cut weight L) (hd : d+L+5 ≤ lim.depth) :
    Meets lim program 0 d [L,cut,flags.card,subsetMask flags,j,base,work] μ (time L)
      (fun r μ' => r = SparseBoxes.boxSum flags (flags ∩ BoxStages.initialCoords L j) weight ∧
        Kept μ μ' work) := by
  apply program_meets flags _ hw hcut hdata hspace hword hflags hj ?_ hd
  simpa only [readAddr,LightBoxStages.stageBase] using
    LightBoxStages.stored_box_lookup hstored hj flags hflags

theorem forced_program_meets {μ : ℕ → ℤ} {L cut base j work d : ℕ}
    (pre tail : Finset (Fin L)) (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdata : base+(L+1)*downsetCap L cut ≤ work)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hcard : (pre ∪ tail).card ≤ cut) (hj : j ≤ L)
    (hp : Disjoint pre (SubsetStages.suffix L j)) (ht : tail ⊆ SubsetStages.suffix L j)
    (hstored : LightZetaStages.StoredThrough μ base cut f L) (hd : d+L+5 ≤ lim.depth) :
    Meets lim program 0 d [L,cut,(pre ∪ tail).card,subsetMask (pre ∪ tail),j,base,work] μ (time L)
      (fun r μ' => r = ∑ x ∈ tail.powerset, f (pre ∪ x) ∧ Kept μ μ' work) := by
  apply program_meets (pre ∪ tail) _ hw hcut hdata hspace hword hcard hj ?_ hd
  simpa only [readAddr,LightZetaStages.stageBase] using
    LightZetaStages.stored_forced_lookup hstored hj pre tail hp ht hcard

theorem time_bound (L : ℕ) : time L ≤ 2800*(L+1)^2 := by
  have hs := LightDownsetSize.time_bound L
  have ha := LightDownsetAddress.time_bound L
  have hp : 1 ≤ (L+1)^2 := Nat.one_le_pow' 2 L
  unfold time
  omega

end ThreeSum.LightStageLookup
