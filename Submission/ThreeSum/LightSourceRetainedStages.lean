import Submission.ThreeSum.LightSourceStages

/-!
# Source stages gathered from a retained original-input histogram

The histogram is built once for a source band and fixed modulus/offset by
`LightSourceHistogram`. This program then gathers the independently trimmed
source for each occurrence vector and runs the actual suffix transforms.
Neither the original array nor the full histogram is rescanned in this loop.
-/

namespace ThreeSum.LightSourceRetainedStages

open Light SubsetAddress LightSubsetAddress LightPascal LightZetaCell

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

def source {L : ℕ} (m : ℕ) (endpoint : Finset (Fin L) → ℤ)
    (flag : Finset (Fin L) → ℕ) (hist : ℕ → ℕ) (S : Finset (Fin L)) : ℤ :=
  ((if flag S = 1 then hist (LightResidues.residue m 1 (endpoint S)) else 0 : ℕ) : ℤ)

theorem source_abs_le {L m B : ℕ} (hm : 0 < m)
    (endpoint : Finset (Fin L) → ℤ) (flag : Finset (Fin L) → ℕ) (hist : ℕ → ℕ)
    (hhist : ∀ r < m, hist r ≤ B) (S : Finset (Fin L)) :
    |source m endpoint flag hist S| ≤ (B : ℤ) := by
  unfold source
  rw [Int.abs_natCast]
  apply Int.ofNat_le.mpr
  split
  · exact hhist _ (LightResidues.residue_lt hm 1 _)
  · omega

/-- Arguments: raw endpoints, independent flags, retained histogram, output
stage base, modulus, reusable work, width, cutoff, mask scratch, exact cap. -/
def body (pGather pZeta : ℕ) : Stmt :=
  .call pGather [v 0,v 1,v 2,v 3,v 9,v 4,v 5] 10 ;;
  .call pZeta [v 6,v 7,v 3,v 8,v 5] 10

def time (L cut E : ℕ) : ℕ :=
  LightSourceGather.time (downsetCap L cut) E+LightZetaStages.time L cut+100

def space (work L E : ℕ) : ℕ :=
  max (work+(Nat.log 2 (E+1)+2)) (work+tableSize L+(L+1))

def word (L m E B : ℕ) : ℕ :=
  4*E+4*m+16+B+(L+1)*2^(L+1)+2^L*B

structure Procs (P : Program) (pMain : ℕ) where
  pGather : ℕ
  pEmod : ℕ
  pZeta : ℕ
  gather : P[pGather]? = some (LightSourceGather.body pEmod)
  emod : P[pEmod]? = some emodBody
  zeta : LightSourceStages.ZetaProcs P pZeta
  main : P[pMain]? = some (body pGather pZeta)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {raw flags table base m work L cut maskBase E B : ℕ}
    (endpoint : Finset (Fin L) → ℤ) (flag : Finset (Fin L) → ℕ) (hist : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+8 ≤ lim.depth)
    (hm : 0 < m) (hcut : cut ≤ L)
    (hraw : raw+downsetCap L cut ≤ base) (hflags : flags+downsetCap L cut ≤ base)
    (htable : table+m ≤ base) (hdata : base+(L+1)*downsetCap L cut ≤ maskBase)
    (hmasks : maskBase+downsetCap L cut ≤ work)
    (hspace : space work L E ≤ lim.space)
    (hword : (word L m E B : ℤ) ≤ lim.word)
    (hrawRead : ∀ i < downsetCap L cut,
      μ (raw+i) = endpoint (SourceTableLayout.setAt L cut i))
    (hrawBound : ∀ S, S.card ≤ cut → |endpoint S| ≤ (E : ℤ))
    (hflagRead : ∀ i < downsetCap L cut,
      μ (flags+i) = (flag (SourceTableLayout.setAt L cut i) : ℤ))
    (hflagBound : ∀ S, S.card ≤ cut → flag S ≤ 1)
    (hhistRead : ∀ r < m, μ (table+r) = (hist r : ℤ))
    (hhistBound : ∀ r < m, hist r ≤ B) :
    Meets lim P pMain d [raw,flags,table,base,m,work,L,cut,maskBase,downsetCap L cut]
      μ (time L cut E) (fun _ ν =>
        LightZetaStages.StoredThrough ν base cut (source m endpoint flag hist) L ∧
        Kept μ ν base) := by
  have hsGather : work+(Nat.log 2 (E+1)+2) ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hsZeta : work+tableSize L+(L+1) ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hwGather : (4*E+4*m+16 : ℤ) ≤ lim.word := by
    have hh : 4*E+4*m+16 ≤ word L m E B := by unfold word; omega
    exact_mod_cast (Int.ofNat_le.mpr hh).trans hword
  have hwB : (B : ℤ) ≤ lim.word := by
    have hh : B ≤ word L m E B := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwZeta : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : (L+1)*2^(L+1) ≤ word L m E B := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwValues : ((2^L*B : ℕ) : ℤ) ≤ lim.word := by
    have hh : 2^L*B ≤ word L m E B := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hcap : downsetCap L cut ≤ (L+1)*downsetCap L cut :=
    Nat.le_mul_of_pos_left _ (by omega)
  apply Meets.of_body C.main
  unfold body time
  have hg := LightSourceGather.meets C.gather C.emod (d := d+1) (μ := μ)
    (raw := raw) (flags := flags) (table := table) (dst := base)
    (n := downsetCap L cut) (m := m) (work := work) (U := E) (B := B)
    (fun i => endpoint (SourceTableLayout.setAt L cut i))
    (fun i => flag (SourceTableLayout.setAt L cut i)) hist
    hw (by omega) hm hraw hflags htable (by omega) hsGather hwGather hwB
    hrawRead (fun i hi => hrawBound _ (SourceTableLayout.setAt_card hi))
    hflagRead (fun i hi => hflagBound _ (SourceTableLayout.setAt_card hi)) hhistRead hhistBound
  light_call hg using LightSourceGather.time,LightZetaStages.time with r ν₁ ⟨out,kept₁⟩
  have htableAt : TableAt ν₁ base cut (source m endpoint flag hist) := by
    apply SourceTableLayout.tableAt_of_setAt
    exact out
  have hz := C.zeta.meets (d := d+1) (μ := ν₁) (L := L) (cut := cut)
    (base := base) (maskBase := maskBase) (work := work) (U := B)
    (source m endpoint flag hist) hw hcut hdata hmasks hsZeta hwZeta hwValues htableAt
    (fun S _ => source_abs_le hm endpoint flag hist hhistBound S) (by omega)
  light_call hz using LightSourceGather.time,LightZetaStages.time with r ν₂ ⟨stored,kept₂⟩
  refine ⟨stored,?_⟩
  intro a ha
  exact (kept₂ a ⟨by omega,Or.inl (by omega)⟩).trans
    (kept₁ a ⟨by omega,Or.inl ha⟩)

def program : Program :=
  [body 1 3,LightSourceGather.body 2,emodBody,LightZetaStages.body 4 5,
    LightDownsetSize.body 9 16,LightZetaPass.body 6 7,
    LightSubsetEnumerationSetup.body 14 18,LightZetaBatch.body 8,
    LightZetaCell.body 9 16 17 15,LightSubsetSetup.body 10 14 15,
    buildBody 11 12,fillBody,rowBody 13,LightArray.linearBody,powTableBody,
    rankBody 15,LightSubsetOffset.body,LightMaskErase.body 17,LightSubsetEnumeration.body 18]

def programProcs : Procs program 0 :=
  ⟨1,2,3,rfl,rfl,⟨4,5,6,18,7,8,9,10,11,12,13,14,15,16,17,
    rfl,rfl,rfl,rfl,rfl,rfl,rfl,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,rfl⟩

theorem program_length : program.length = 19 := rfl

theorem time_bound {L cut E : ℕ} (hcut : cut ≤ L) :
    time L cut E ≤ 157*downsetCap L cut*(Nat.log 2 (E+1)+1)+
      6000*(L+1)^4*(downsetCap L cut+1)+106 := by
  have hg := LightSourceGather.time_bound (downsetCap L cut) E
  have hz := LightZetaStages.time_bound hcut
  unfold time
  omega

end ThreeSum.LightSourceRetainedStages
