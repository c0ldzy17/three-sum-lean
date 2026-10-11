import Submission.ThreeSum.LightSourceResidues
import Submission.ThreeSum.LightHistogram

/-!
# Exact source histogram from original signed inputs

This complete wrapper computes the two-modulus key of every original input,
clears the histogram, and increments it once per input incidence. The carry
offset is supplied as a signed integer. No residue-array or histogram oracle
appears in the input contract.
-/

namespace ThreeSum.LightSourceHistogram

open Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

/-- Arguments: original source, histogram destination, item count, first
modulus, histogram modulus, key scratch, remainder scratch, carry offset. -/
def body (pKeys pHistogram : ℕ) : Stmt :=
  .call pKeys [v 0,v 5,v 2,v 3,v 4,v 6,v 7] 8 ;;
  .call pHistogram [v 5,v 1,v 2,v 4] 8

def time (n p m U D : ℕ) : ℕ :=
  LightSourceResidues.time n p U D + LightHistogram.histogramTime n m + 40

structure Procs (P : Program) (pMain : ℕ) where
  pKeys : ℕ
  pEmod : ℕ
  pHistogram : ℕ
  pFill : ℕ
  keys : P[pKeys]? = some (LightSourceResidues.body pEmod)
  emod : P[pEmod]? = some emodBody
  histogram : P[pHistogram]? = some (LightHistogram.histogramBody pFill)
  fill : P[pFill]? = some fillBody
  main : P[pMain]? = some (body pKeys pHistogram)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {src hist n p m codes work U D : ℕ} {shift : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hp : 0 < p) (hm : 0 < m)
    (hsrc : src+n ≤ codes) (hhist : hist+m ≤ codes) (hcodes : codes+n ≤ work)
    (hspace : LightSourceResidues.space work p U D ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ))
    (hword : (LightSourceResidues.word p m U D : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src+i)| ≤ (U : ℤ)) :
    Meets lim P pMain d [src,hist,n,p,m,codes,work,shift] μ (time n p m U D)
      (fun _ ν =>
        (∀ i < n, ν (codes+i) =
          (LightSourceResidues.key p m shift (μ (src+i)) : ℤ)) ∧
        (∀ r < m, ν (hist+r) = (LightHistogram.count
          (fun i => LightSourceResidues.key p m shift (μ (src+i))) r n : ℤ)) ∧
        KeptBut μ ν codes hist m) := by
  have hwork : work ≤ lim.space := by
    unfold LightSourceResidues.space at hspace
    omega
  apply Meets.of_body S.main
  unfold body time
  have hkeys := LightSourceResidues.meets (d := d+1) (μ := μ)
    (src := src) (dst := codes) (n := n) (p := p) (m := m) (work := work)
    (U := U) (D := D) (shift := shift) S.keys S.emod hw hd hp hm
    (by omega) hcodes hspace (Or.inl hsrc) hshift hword hvalues
  light_call hkeys using LightSourceResidues.time,LightResidues.residueBudget,
    LightHistogram.histogramTime,LightHistogram.countTime
    with r ν₁ ⟨keys,kept₁⟩
  have hhistogram := LightHistogram.histogram_meets (d := d+1) (μ := ν₁)
    (src := codes) (dst := hist) (n := n) (p := m) S.histogram S.fill
    (fun i => LightSourceResidues.key p m shift (μ (src+i))) hw hd
    (by omega) (by omega) (Or.inr hhist) keys
    (fun i _ => LightSourceResidues.key_lt hm shift (μ (src+i)))
  light_call hhistogram using LightSourceResidues.time,LightResidues.residueBudget,
    LightHistogram.histogramTime,LightHistogram.countTime
    with r ν₂ ⟨counts,kept₂⟩
  refine ⟨?_,counts,?_⟩
  · intro i hi
    exact (kept₂ _ (Or.inr (by omega))).trans (keys i hi)
  · intro a ⟨ha,hout⟩
    exact (kept₂ a hout).trans (kept₁ a ⟨by omega,Or.inl ha⟩)

def program : Program :=
  [body 1 3,LightSourceResidues.body 2,emodBody,LightHistogram.histogramBody 4,fillBody]

def programProcs : Procs program 0 := ⟨1,2,3,4,rfl,rfl,rfl,rfl,rfl⟩

theorem program_meets
    {μ : ℕ → ℤ} {src hist n p m codes work U D : ℕ} {shift : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hp : 0 < p) (hm : 0 < m)
    (hsrc : src+n ≤ codes) (hhist : hist+m ≤ codes) (hcodes : codes+n ≤ work)
    (hspace : LightSourceResidues.space work p U D ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ))
    (hword : (LightSourceResidues.word p m U D : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src+i)| ≤ (U : ℤ)) :
    Meets lim program 0 d [src,hist,n,p,m,codes,work,shift] μ (time n p m U D)
      (fun _ ν =>
        (∀ i < n, ν (codes+i) =
          (LightSourceResidues.key p m shift (μ (src+i)) : ℤ)) ∧
        (∀ r < m, ν (hist+r) = (LightHistogram.count
          (fun i => LightSourceResidues.key p m shift (μ (src+i))) r n : ℤ)) ∧
        KeptBut μ ν codes hist m) := by
  exact programProcs.meets hw hd hp hm hsrc hhist hcodes hspace hshift hword hvalues

theorem time_bound (n p m U D : ℕ) :
    time n p m U D ≤
      278*n*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+13*m+63 := by
  have hr := LightSourceResidues.time_bound n p U D
  unfold time LightHistogram.histogramTime LightHistogram.countTime fillTime
  nlinarith

end ThreeSum.LightSourceHistogram
