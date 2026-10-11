import Submission.ThreeSum.LightSourceBuild
import Submission.ThreeSum.SourceTableLayout
import Submission.ThreeSum.LightZetaStages

/-!
# Original-input histogram construction followed by all suffix zeta stages

This fixed program constructs a trimmed source table from the physical input
array, then feeds that exact table into the existing costed suffix transform.
The rank/enumeration proof connects the sequential source writes to the
compact addresses. No initially populated source or zeta table is assumed.
-/

namespace ThreeSum.LightSourceStages

open Light SubsetAddress LightSubsetAddress LightPascal LightZetaCell

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

/-- This record identifies literal bodies of the existing zeta program;
it contains no execution or semantic assumptions. -/
structure ZetaProcs (P : Program) (pMain : ℕ) where
  pSize : ℕ
  pPass : ℕ
  pEnumSetup : ℕ
  pEnum : ℕ
  pBatch : ℕ
  pCell : ℕ
  pSetup : ℕ
  pBuild : ℕ
  pFill : ℕ
  pRow : ℕ
  pLinear : ℕ
  pPowers : ℕ
  pRank : ℕ
  pOffset : ℕ
  pErase : ℕ
  main : P[pMain]? = some (LightZetaStages.body pSize pPass)
  size : P[pSize]? = some (LightDownsetSize.body pSetup pOffset)
  pass : P[pPass]? = some (LightZetaPass.body pEnumSetup pBatch)
  enumSetup : P[pEnumSetup]? = some (LightSubsetEnumerationSetup.body pPowers pEnum)
  enumeration : P[pEnum]? = some (LightSubsetEnumeration.body pEnum)
  batch : P[pBatch]? = some (LightZetaBatch.body pCell)
  cell : P[pCell]? = some (LightZetaCell.body pSetup pOffset pErase pRank)
  setup : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank
  offset : P[pOffset]? = some LightSubsetOffset.body
  erase : P[pErase]? = some (LightMaskErase.body pErase)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem ZetaProcs.meets {pMain : ℕ} (C : ZetaProcs P pMain)
    {μ : ℕ → ℤ} {L cut base maskBase work U : ℕ} (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdata : base+(L+1)*downsetCap L cut ≤ maskBase)
    (hmasks : maskBase+downsetCap L cut ≤ work)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^L*U : ℕ) : ℤ) ≤ lim.word)
    (hread : TableAt μ base cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U)
    (hd : d+L+7 ≤ lim.depth) :
    Meets lim P pMain d [L,cut,base,maskBase,work] μ (LightZetaStages.time L cut)
      (fun _ ν => LightZetaStages.StoredThrough ν base cut f L ∧
        KeptBut μ ν maskBase base ((L+1)*downsetCap L cut)) :=
  LightZetaStages.meets C.main C.size C.pass C.enumSetup C.enumeration C.batch C.cell
    C.setup C.offset C.erase f hw hcut hdata hmasks hspace hword hvalueWord hread hvalues hd

def source {L : ℕ} (μ : ℕ → ℤ) (src N p m : ℕ) (shift : ℤ)
    (endpoint : Finset (Fin L) → ℤ) (flag : Finset (Fin L) → ℕ)
    (S : Finset (Fin L)) : ℤ :=
  ((if flag S = 1 then
    LightHistogram.count (fun j => LightSourceResidues.key p m shift (μ (src+j)))
      (LightResidues.residue m 1 (endpoint S)) N else 0 : ℕ) : ℤ)

theorem source_abs_le {L : ℕ} (μ : ℕ → ℤ) (src N p m : ℕ) (shift : ℤ)
    (endpoint : Finset (Fin L) → ℤ) (flag : Finset (Fin L) → ℕ)
    (S : Finset (Fin L)) : |source μ src N p m shift endpoint flag S| ≤ (N : ℤ) := by
  unfold source
  rw [Int.abs_natCast]
  apply Int.ofNat_le.mpr
  split
  · exact LightHistogram.count_le ..
  · omega

/-- Arguments: original input/count, raw/flag arrays, both moduli, histogram,
base of stored stages, key scratch, shared work, signed carry, width, cutoff,
mask scratch, and exact mask count returned by the enumeration stage. -/
def body (pSource pZeta : ℕ) : Stmt :=
  .call pSource [v 0,v 1,v 2,v 3,v 14,v 4,v 5,v 6,v 7,v 8,v 9,v 10] 15 ;;
  .call pZeta [v 11,v 12,v 7,v 13,v 9] 15

def time (N L cut p m U D E : ℕ) : ℕ :=
  LightSourceBuild.time N (downsetCap L cut) p m U D E+LightZetaStages.time L cut+100

def space (work L p U D E : ℕ) : ℕ :=
  max (LightSourceBuild.space work p U D E) (work+tableSize L+(L+1))

def word (N L p m U D E : ℕ) : ℕ :=
  LightSourceBuild.word p m U D E+(L+1)*2^(L+1)+2^L*N

structure Procs (P : Program) (pMain : ℕ) where
  pSource : ℕ
  pZeta : ℕ
  sourceProcs : LightSourceBuild.Procs P pSource
  zeta : ZetaProcs P pZeta
  main : P[pMain]? = some (body pSource pZeta)

theorem Procs.meets {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {src N raw flags p m hist base codes work L cut maskBase U D E : ℕ} {shift : ℤ}
    (endpoint : Finset (Fin L) → ℤ) (flag : Finset (Fin L) → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+8 ≤ lim.depth)
    (hp : 0 < p) (hm : 0 < m) (hcut : cut ≤ L)
    (hsrc : src+N ≤ hist)
    (hraw : raw+downsetCap L cut ≤ hist) (hflags : flags+downsetCap L cut ≤ hist)
    (hhist : hist+m ≤ base) (hdata : base+(L+1)*downsetCap L cut ≤ maskBase)
    (hmasks : maskBase+downsetCap L cut ≤ codes) (hcodes : codes+N ≤ work)
    (hspace : space work L p U D E ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (word N L p m U D E : ℤ) ≤ lim.word)
    (hvalues : ∀ i < N, |μ (src+i)| ≤ (U : ℤ))
    (hrawRead : ∀ i < downsetCap L cut,
      μ (raw+i) = endpoint (SourceTableLayout.setAt L cut i))
    (hrawBound : ∀ S, S.card ≤ cut → |endpoint S| ≤ (E : ℤ))
    (hflagRead : ∀ i < downsetCap L cut,
      μ (flags+i) = (flag (SourceTableLayout.setAt L cut i) : ℤ))
    (hflagBound : ∀ S, S.card ≤ cut → flag S ≤ 1) :
    Meets lim P pMain d [src,N,raw,flags,p,m,hist,base,codes,work,shift,L,cut,maskBase,downsetCap L cut]
      μ (time N L cut p m U D E) (fun _ ν =>
        LightZetaStages.StoredThrough ν base cut (source μ src N p m shift endpoint flag) L ∧
        (∀ r < m, ν (hist+r) = (LightHistogram.count
          (fun j => LightSourceResidues.key p m shift (μ (src+j))) r N : ℤ)) ∧
        Kept μ ν hist) := by
  have hsSource : LightSourceBuild.space work p U D E ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hsZeta : work+tableSize L+(L+1) ≤ lim.space := (le_max_right _ _).trans hspace
  have hwSource : (LightSourceBuild.word p m U D E : ℤ) ≤ lim.word := by
    have hh : LightSourceBuild.word p m U D E ≤ word N L p m U D E := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwZeta : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : (L+1)*2^(L+1) ≤ word N L p m U D E := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwValues : ((2^L*N : ℕ) : ℤ) ≤ lim.word := by
    have hh : 2^L*N ≤ word N L p m U D E := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hcap : downsetCap L cut ≤ (L+1)*downsetCap L cut := Nat.le_mul_of_pos_left _ (by omega)
  apply Meets.of_body C.main
  unfold body time
  have hs := C.sourceProcs.meets (d := d+1) (μ := μ) (src := src) (N := N)
    (raw := raw) (flags := flags) (n := downsetCap L cut) (p := p) (m := m)
    (hist := hist) (dst := base) (codes := codes) (work := work) (U := U) (D := D) (E := E)
    (shift := shift) (fun i => endpoint (SourceTableLayout.setAt L cut i))
    (fun i => flag (SourceTableLayout.setAt L cut i)) hw (by omega) hp hm
    hsrc hraw hflags hhist (by omega) hcodes hsSource hshift hwSource hvalues hrawRead
    (fun i hi => hrawBound _ (SourceTableLayout.setAt_card hi)) hflagRead
    (fun i hi => hflagBound _ (SourceTableLayout.setAt_card hi))
  light_call hs using LightSourceBuild.time,LightSourceHistogram.time,LightSourceResidues.time,
    LightSourceGather.time,LightZetaStages.time with r ν₁ ⟨out,counts,kept₁⟩
  have htable : TableAt ν₁ base cut (source μ src N p m shift endpoint flag) := by
    apply SourceTableLayout.tableAt_of_setAt
    exact out
  have hz := C.zeta.meets (d := d+1) (μ := ν₁) (L := L) (cut := cut)
    (base := base) (maskBase := maskBase) (work := work) (U := N)
    (source μ src N p m shift endpoint flag) hw hcut hdata (by omega) hsZeta hwZeta hwValues
    htable (fun S _ => source_abs_le μ src N p m shift endpoint flag S) (by omega)
  light_call hz using LightSourceBuild.time,LightSourceHistogram.time,LightSourceResidues.time,
    LightSourceGather.time,LightZetaStages.time with r ν₂ ⟨stored,kept₂⟩
  refine ⟨stored,?_,?_⟩
  · intro r hr
    exact (kept₂ _ ⟨by omega,Or.inl (by omega)⟩).trans (counts r hr)
  · intro a ha
    exact (kept₂ a ⟨by omega,Or.inl (by omega)⟩).trans (kept₁ a ha)

def program : Program :=
  [body 1 8,LightSourceBuild.body 2 7,LightSourceHistogram.body 3 5,LightSourceResidues.body 4,
    emodBody,LightHistogram.histogramBody 6,fillBody,LightSourceGather.body 4,
    LightZetaStages.body 9 10,LightDownsetSize.body 14 21,LightZetaPass.body 11 12,
    LightSubsetEnumerationSetup.body 19 23,LightZetaBatch.body 13,
    LightZetaCell.body 14 21 22 20,LightSubsetSetup.body 15 19 20,
    buildBody 16 17,fillBody,rowBody 18,LightArray.linearBody,powTableBody,
    rankBody 20,LightSubsetOffset.body,LightMaskErase.body 22,LightSubsetEnumeration.body 23]

def programProcs : Procs program 0 :=
  ⟨1,8,⟨2,7,⟨3,4,5,6,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,
    ⟨9,10,11,23,12,13,14,15,16,17,18,19,20,21,22,
      rfl,rfl,rfl,rfl,rfl,rfl,rfl,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,rfl⟩

theorem time_bound {N L cut p m U D E : ℕ} (hcut : cut ≤ L) :
    time N L cut p m U D E ≤
      278*N*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+
      157*downsetCap L cut*(Nat.log 2 (E+1)+1)+13*m+
      6000*(L+1)^4*(downsetCap L cut+1)+269 := by
  have hs := LightSourceBuild.time_bound N (downsetCap L cut) p m U D E
  have hz := LightZetaStages.time_bound hcut
  unfold time
  omega

end ThreeSum.LightSourceStages
