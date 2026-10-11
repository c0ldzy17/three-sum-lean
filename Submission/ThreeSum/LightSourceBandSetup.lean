import Submission.ThreeSum.LightSourceBandBatch
import Submission.ThreeSum.LightSmallDivide

/-!
# Original source array to a complete packed band catalog

The band count, truncated capacity, all pointer-table addresses, and shared
remainder scratch are computed by actual RAM expressions. Each original
slice is visited once by the existing code/histogram/prefix/scatter program.
-/

namespace ThreeSum.LightSourceBandSetup

open Light BandPartition SourceBandLayout

set_option maxHeartbeats 3000000
set_option maxRecDepth 18000

def addressBody (pBatch : ℕ) : Stmt :=
  .set 9 (v 6 +' k 6 *' v 8) ;;
  .set 10 (k 3 *' v 4 +' k 1 +' k 2 *' v 7) ;;
  .set 11 (v 9 +' v 8 *' v 10) ;;
  .call pBatch [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11] 12 ;;
  .set 0 (v 11)

def countBody (pDivide pBatch : ℕ) : Stmt :=
  .set 8 (k 0) ;;
  .ite (k 0 <' v 1)
    (.call pDivide [v 1 -' k 1,v 2] 8 ;;
      .set 8 (v 8 +' k 1)) .skip ;;
  addressBody pBatch

def body (pDivide pBatch : ℕ) : Stmt :=
  .set 7 (v 2) ;;
  .ite (v 1 <' v 2) (.set 7 (v 1)) .skip ;;
  countBody pDivide pBatch

def addressTime (n g p m U D : ℕ) : ℕ := LightSourceBandBatch.time n g p m U D+250
def countTime (n g p m U D : ℕ) : ℕ :=
  LightSmallDivide.time (n-1) g+LightSourceBandBatch.time n g p m U D+350
def time (n g p m U D : ℕ) : ℕ :=
  LightSmallDivide.time (n-1) g+LightSourceBandBatch.time n g p m U D+500

structure Procs (P : Program) (pMain : ℕ) where
  pDivide : ℕ
  pBatch : ℕ
  divide : P[pDivide]? = some LightSmallDivide.body
  batch : LightSourceBandBatch.Procs P pBatch
  main : P[pMain]? = some (body pDivide pBatch)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem address_ends {pBatch : ℕ} (C : LightSourceBandBatch.Procs P pBatch)
    {μ : ℕ → ℤ} {src n g p m base U D K : ℕ} {shift : ℤ} (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+5 < lim.depth)
    (hg : 0 < g) (hp : 0 < p) (hm : 0 < m) (hsrc : src+n ≤ base) (hK : K=size n g)
    (hspace : LightSourceResidues.space (work base n g m) p U D ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (LightSourceBandStep.word n g p m U D : ℤ) ≤ lim.word)
    (hread : ∀ j < n, μ (src+j)=f j) (hvalues : ∀ j < n, |f j| ≤ (U : ℤ)) :
    Ends lim P d (addressBody pBatch)
      ⟨frame [src,n,g,p,m,shift,base,cap n g,K],μ⟩
      (addressTime n g p m U D) (fun σ =>
        σ.loc 0=(work base n g m : ℤ) ∧
        (∀ i < size n g, SourceBandData.At σ.mem f base n g p m shift i) ∧ Kept μ σ.mem base) := by
  subst K
  have hwork : work base n g m ≤ lim.space := by unfold LightSourceResidues.space at hspace; omega
  have hdata : data base n g ≤ work base n g m := data_le_hist base n g m (size n g)
  have hcapN : cap n g ≤ n := min_le_left _ _
  have hcapG : cap n g ≤ g := min_le_right _ _
  have hdataAddr : base+6*size n g ≤ lim.space := hdata.trans hwork
  have hcountprod : (6 : ℤ)*(size n g : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show 6*size n g ≤ lim.space by omega) :
      (6 : ℤ)*(size n g : ℤ) ≤ lim.space).trans hw
  have hstrideN : 3*m+1+2*cap n g ≤ LightSourceBandStep.word n g p m U D := by
    unfold LightSourceBandStep.word LightSourceResidues.word
    omega
  have hstrideZ : (3 : ℤ)*(m : ℤ)+1+2*(cap n g : ℤ) ≤ lim.word :=
    (by exact_mod_cast hstrideN : (3 : ℤ)*(m : ℤ)+1+2*(cap n g : ℤ) ≤
      (LightSourceBandStep.word n g p m U D : ℤ)).trans hword
  have h32 : (32 : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show 32 ≤ LightSourceBandStep.word n g p m U D by
      unfold LightSourceBandStep.word LightSourceResidues.word; omega)).trans hword
  have hworkProd : (size n g : ℤ)*(stride n g m : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show size n g*stride n g m ≤ lim.space by unfold work hist at hwork; omega) :
      (size n g : ℤ)*(stride n g m : ℤ) ≤ lim.space).trans hw
  have hworkProdN : (0 : ℤ) ≤ (size n g : ℤ)*(stride n g m : ℤ) := by positivity
  have hworkAddr : (data base n g : ℤ)+(size n g : ℤ)*(stride n g m : ℤ) ≤ lim.word :=
    (by exact_mod_cast hwork :
      (data base n g : ℤ)+(size n g : ℤ)*(stride n g m : ℤ) ≤ lim.space).trans hw
  unfold addressBody addressTime
  light_set (data base n g : ℕ) using data
  light_set (stride n g m : ℕ) using stride
  light_set (work base n g m : ℕ) using work,hist
  have hrun := C.meets (d := d+1) (μ := μ) (src := src) (n := n) (g := g) (p := p) (m := m)
    (base := base) (U := U) (D := D) (shift := shift)
    f hw (by omega) hg hp hm hsrc hspace hshift hword hread hvalues
  light_call hrun with r ν ⟨stored,kept⟩
  light_set (work base n g m : ℕ)
  exact ⟨rfl,stored,kept⟩

theorem count_ends {pDivide pBatch : ℕ} (hdivide : P[pDivide]? = some LightSmallDivide.body)
    (C : LightSourceBandBatch.Procs P pBatch)
    {μ : ℕ → ℤ} {src n g p m base U D K : ℕ} {shift : ℤ} (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+5 < lim.depth)
    (hg : 0 < g) (hp : 0 < p) (hm : 0 < m) (hsrc : src+n ≤ base) (hK : K=cap n g)
    (hspace : LightSourceResidues.space (work base n g m) p U D ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (LightSourceBandStep.word n g p m U D : ℤ) ≤ lim.word)
    (hread : ∀ j < n, μ (src+j)=f j) (hvalues : ∀ j < n, |f j| ≤ (U : ℤ)) :
    Ends lim P d (countBody pDivide pBatch)
      ⟨frame [src,n,g,p,m,shift,base,K],μ⟩
      (countTime n g p m U D) (fun σ =>
        σ.loc 0=(work base n g m : ℤ) ∧
        (∀ i < size n g, SourceBandData.At σ.mem f base n g p m shift i) ∧ Kept μ σ.mem base) := by
  subst K
  have hwordN : ((n+g+2 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show n+g+2 ≤ LightSourceBandStep.word n g p m U D by
      unfold LightSourceBandStep.word; omega)).trans hword
  have hcount := size_le n g
  have haddressTime : addressTime n g p m U D=LightSourceBandBatch.time n g p m U D+250 := rfl
  unfold countBody countTime
  light_set (0 : ℕ)
  light_if hn hn : (0 : ℤ) < (n : ℤ)
  · have hnN : n ≠ 0 := by omega
    have hmval : size n g=(n-1)/g+1 := by simp [size,hnN]
    have hdiv := LightSmallDivide.meets (d := d+1) (a := n-1) (b := g) hdivide μ
      ((Int.ofNat_le.mpr (by omega : n-1+g+2 ≤ n+g+2)).trans hwordN)
    light_call hdiv with q ν ⟨hq,hmem⟩
    subst ν
    light_set (size n g : ℕ) using hmval,hq
    light_piece (address_ends C f hw hd hg hp hm hsrc rfl hspace hshift hword hread hvalues)
  · have hnN : n=0 := by omega
    have hzero : 0=size n g := by simp [size,hnN]
    light_piece (address_ends C (K := 0) f hw hd hg hp hm hsrc hzero hspace hshift hword hread hvalues)

theorem Procs.meets {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {src n g p m base U D : ℕ} {shift : ℤ} (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+5 < lim.depth)
    (hg : 0 < g) (hp : 0 < p) (hm : 0 < m) (hsrc : src+n ≤ base)
    (hspace : LightSourceResidues.space (work base n g m) p U D ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (LightSourceBandStep.word n g p m U D : ℤ) ≤ lim.word)
    (hread : ∀ j < n, μ (src+j)=f j) (hvalues : ∀ j < n, |f j| ≤ (U : ℤ)) :
    Meets lim P pMain d [src,n,g,p,m,shift,base] μ (time n g p m U D) (fun r ν =>
      r=(work base n g m : ℤ) ∧
      (∀ i < size n g, SourceBandData.At ν f base n g p m shift i) ∧ Kept μ ν base) := by
  have hwordN : ((n+g+2 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show n+g+2 ≤ LightSourceBandStep.word n g p m U D by
      unfold LightSourceBandStep.word; omega)).trans hword
  have hcountTime : countTime n g p m U D=
      LightSmallDivide.time (n-1) g+LightSourceBandBatch.time n g p m U D+350 := rfl
  apply Meets.of_body C.main
  unfold body time
  light_set (g : ℕ)
  light_if hsmall hsmall : (n : ℤ) < (g : ℤ)
  · have hcap : n=cap n g := by unfold cap; omega
    light_set (n : ℕ)
    light_piece (count_ends C.divide C.batch (K := n) f hw hd hg hp hm hsrc hcap
      hspace hshift hword hread hvalues)
  · have hcap : g=cap n g := by unfold cap; omega
    light_piece (count_ends C.divide C.batch (K := g) f hw hd hg hp hm hsrc hcap
      hspace hshift hword hread hvalues)

theorem time_bound (n g p m U D : ℕ) (hg : 0 < g) :
    time n g p m U D ≤ 1016*n*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+
      size n g*(233*m+1713)+560 := by
  have hb := LightSourceBandBatch.time_bound n g p m U D hg
  have hdiv : LightSmallDivide.time (n-1) g ≤ 20*n+40 := by
    have hh := Nat.div_le_self (n-1) g
    unfold LightSmallDivide.time
    omega
  have hn : n ≤ n*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  unfold time
  nlinarith

end ThreeSum.LightSourceBandSetup
