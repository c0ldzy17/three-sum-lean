import Submission.ThreeSum.LightSourceGather

/-!
# Building a trimmed source array from original signed inputs

The host first constructs the two-modulus original-input histogram, then
gathers it at the actual endpoint residues. All original input incidences
are counted once, and every subset-mask entry receives its exact independent
trimmed source multiplicity. Both stages share remainder scratch.
-/

namespace ThreeSum.LightSourceBuild

open Light

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

/-- Arguments: original source and count; endpoint and flag arrays and count;
first modulus, global modulus, histogram, output, key scratch, remainder
scratch, and signed carry offset. -/
def body (pHistogram pGather : ℕ) : Stmt :=
  .call pHistogram [v 0,v 7,v 1,v 5,v 6,v 9,v 10,v 11] 12 ;;
  .call pGather [v 2,v 3,v 7,v 8,v 4,v 6,v 10] 12

def time (N n p m U D E : ℕ) : ℕ :=
  LightSourceHistogram.time N p m U D + LightSourceGather.time n E + 100

def word (p m U D E : ℕ) : ℕ := LightSourceResidues.word p m U D+4*E+4*m+16

def space (work p U D E : ℕ) : ℕ :=
  max (LightSourceResidues.space work p U D) (work+(Nat.log 2 (E+1)+2))

structure Procs (P : Program) (pMain : ℕ) where
  pHistogram : ℕ
  pGather : ℕ
  histogram : LightSourceHistogram.Procs P pHistogram
  gather : P[pGather]? = some (LightSourceGather.body histogram.pEmod)
  main : P[pMain]? = some (body pHistogram pGather)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {src N raw flags n p m hist dst codes work U D E : ℕ} {shift : ℤ}
    (endpoint : ℕ → ℤ) (flag : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hp : 0 < p) (hm : 0 < m)
    (hsrc : src+N ≤ hist) (hraw : raw+n ≤ hist) (hflags : flags+n ≤ hist)
    (hhist : hist+m ≤ dst) (hdst : dst+n ≤ codes) (hcodes : codes+N ≤ work)
    (hspace : space work p U D E ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (word p m U D E : ℤ) ≤ lim.word)
    (hvalues : ∀ i < N, |μ (src+i)| ≤ (U : ℤ))
    (hrawRead : ∀ i < n, μ (raw+i) = endpoint i)
    (hrawBound : ∀ i < n, |endpoint i| ≤ (E : ℤ))
    (hflagRead : ∀ i < n, μ (flags+i) = (flag i : ℤ))
    (hflagBound : ∀ i < n, flag i ≤ 1) :
    Meets lim P pMain d [src,N,raw,flags,n,p,m,hist,dst,codes,work,shift]
      μ (time N n p m U D E) (fun _ ν =>
        (∀ i < n, ν (dst+i) = (LightSourceGather.value m endpoint flag
          (fun r => LightHistogram.count
            (fun j => LightSourceResidues.key p m shift (μ (src+j))) r N) i : ℤ)) ∧
        (∀ r < m, ν (hist+r) = (LightHistogram.count
          (fun j => LightSourceResidues.key p m shift (μ (src+j))) r N : ℤ)) ∧
        Kept μ ν hist) := by
  have hspaceH : LightSourceResidues.space work p U D ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hspaceG : work+(Nat.log 2 (E+1)+2) ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hwordH : (LightSourceResidues.word p m U D : ℤ) ≤ lim.word := by
    have hh : LightSourceResidues.word p m U D ≤ word p m U D E := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwordG : (4*E+4*m+16 : ℤ) ≤ lim.word := by
    have hh : 4*E+4*m+16 ≤ word p m U D E := by unfold word; omega
    exact (by exact_mod_cast hh : (4*E+4*m+16 : ℤ) ≤ (word p m U D E : ℤ)).trans hword
  have hcountWord : (N : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (by omega : N ≤ lim.space)).trans hw
  apply Meets.of_body S.main
  unfold body time
  have hh := S.histogram.meets (d := d+1) (μ := μ) (src := src) (hist := hist)
    (n := N) (p := p) (m := m) (codes := codes) (work := work) (U := U) (D := D)
    (shift := shift) hw (by omega) hp hm (by omega) (by omega) hcodes hspaceH
    hshift hwordH hvalues
  light_call hh using LightSourceHistogram.time,LightSourceResidues.time,
    LightResidues.residueBudget,LightHistogram.histogramTime,LightHistogram.countTime,
    LightSourceGather.time with r ν₁ ⟨_,counts,kept₁⟩
  have rawRead : ∀ i < n, ν₁ (raw+i) = endpoint i := by
    intro i hi
    exact (kept₁ _ ⟨by omega,Or.inl (by omega)⟩).trans (hrawRead i hi)
  have flagRead : ∀ i < n, ν₁ (flags+i) = (flag i : ℤ) := by
    intro i hi
    exact (kept₁ _ ⟨by omega,Or.inl (by omega)⟩).trans (hflagRead i hi)
  have hg := LightSourceGather.meets (d := d+1) (μ := ν₁)
    (raw := raw) (flags := flags) (table := hist) (dst := dst) (n := n) (m := m)
    (work := work) (U := E) (B := N) S.gather S.histogram.emod endpoint flag
    (fun r => LightHistogram.count (fun j => LightSourceResidues.key p m shift (μ (src+j))) r N)
    hw (by omega) hm (by omega) (by omega) hhist (by omega) hspaceG hwordG hcountWord
    rawRead hrawBound flagRead hflagBound counts
    (fun r _ => LightHistogram.count_le _ r N)
  light_call hg using LightSourceHistogram.time,LightSourceResidues.time,
    LightResidues.residueBudget,LightHistogram.histogramTime,LightHistogram.countTime,
    LightSourceGather.time with r ν₂ ⟨out,kept₂⟩
  refine ⟨out,?_,?_⟩
  · intro r hr
    exact (kept₂ _ ⟨by omega,Or.inl (by omega)⟩).trans (counts r hr)
  · intro a ha
    exact (kept₂ a ⟨by omega,Or.inl (by omega)⟩).trans
      (kept₁ a ⟨by omega,Or.inl ha⟩)

def program : Program :=
  [body 1 6,LightSourceHistogram.body 2 4,LightSourceResidues.body 3,emodBody,
    LightHistogram.histogramBody 5,fillBody,LightSourceGather.body 3]

def programProcs : Procs program 0 :=
  ⟨1,6,⟨2,3,4,5,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩

theorem program_meets
    {μ : ℕ → ℤ} {src N raw flags n p m hist dst codes work U D E : ℕ} {shift : ℤ}
    (endpoint : ℕ → ℤ) (flag : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hp : 0 < p) (hm : 0 < m)
    (hsrc : src+N ≤ hist) (hraw : raw+n ≤ hist) (hflags : flags+n ≤ hist)
    (hhist : hist+m ≤ dst) (hdst : dst+n ≤ codes) (hcodes : codes+N ≤ work)
    (hspace : space work p U D E ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (word p m U D E : ℤ) ≤ lim.word)
    (hvalues : ∀ i < N, |μ (src+i)| ≤ (U : ℤ))
    (hrawRead : ∀ i < n, μ (raw+i) = endpoint i)
    (hrawBound : ∀ i < n, |endpoint i| ≤ (E : ℤ))
    (hflagRead : ∀ i < n, μ (flags+i) = (flag i : ℤ))
    (hflagBound : ∀ i < n, flag i ≤ 1) :
    Meets lim program 0 d [src,N,raw,flags,n,p,m,hist,dst,codes,work,shift]
      μ (time N n p m U D E) (fun _ ν =>
        (∀ i < n, ν (dst+i) = (LightSourceGather.value m endpoint flag
          (fun r => LightHistogram.count
            (fun j => LightSourceResidues.key p m shift (μ (src+j))) r N) i : ℤ)) ∧
        (∀ r < m, ν (hist+r) = (LightHistogram.count
          (fun j => LightSourceResidues.key p m shift (μ (src+j))) r N : ℤ)) ∧
        Kept μ ν hist) := by
  exact programProcs.meets endpoint flag hw hd hp hm hsrc hraw hflags hhist hdst hcodes
    hspace hshift hword hvalues hrawRead hrawBound hflagRead hflagBound

theorem time_bound (N n p m U D E : ℕ) :
    time N n p m U D E ≤
      278*N*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+
      157*n*(Nat.log 2 (E+1)+1)+13*m+169 := by
  have hh := LightSourceHistogram.time_bound N p m U D
  have hg := LightSourceGather.time_bound n E
  unfold time
  omega

end ThreeSum.LightSourceBuild
