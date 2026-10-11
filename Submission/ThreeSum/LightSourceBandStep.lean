import Submission.ThreeSum.SourceBandData

/-! # One actual original-band histogram, buckets, and six pointer headers -/

namespace ThreeSum.LightSourceBandStep

open Light BandPartition SourceBandLayout

set_option maxHeartbeats 3000000
set_option maxRecDepth 18000

def tailBody (pOriginal : ℕ) : Stmt :=
  .set 15 (v 14 -' v 13) ;;
  .set 16 (v 9 +' v 12 *' v 10) ;;
  .set 17 (v 16 +' v 4) ;;
  .set 18 (v 17 +' v 7) ;;
  .set 19 (v 18 +' v 4 +' k 1) ;;
  .set 20 (v 19 +' v 4) ;;
  .call pOriginal [v 0 +' v 13,v 15,v 3,v 4,v 5,v 16,v 17,v 18,v 19,v 20,v 11] 21 ;;
  .store (v 6 +' k 6 *' v 12) (v 13) ;;
  .store (v 6 +' k 6 *' v 12 +' k 1) (v 15) ;;
  .store (v 6 +' k 6 *' v 12 +' k 2) (v 17) ;;
  .store (v 6 +' k 6 *' v 12 +' k 3) (v 16) ;;
  .store (v 6 +' k 6 *' v 12 +' k 4) (v 18) ;;
  .store (v 6 +' k 6 *' v 12 +' k 5) (v 20)

def body (pOriginal : ℕ) : Stmt :=
  .set 13 (v 12 *' v 2) ;;
  .set 14 ((v 12 +' k 1) *' v 2) ;;
  .ite (v 1 <' v 14) (.set 14 (v 1)) .skip ;;
  tailBody pOriginal

def charge (n g p m U D : ℕ) : ℕ :=
  498*cap n g*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+233*m+333

def tailTime (n g p m U D : ℕ) : ℕ := charge n g p m U D+1000
def time (n g p m U D : ℕ) : ℕ := charge n g p m U D+1200

def word (n g p m U D : ℕ) : ℕ := LightSourceResidues.word p m U D+n+g+2

structure Procs (P : Program) (pMain : ℕ) where
  pOriginal : ℕ
  original : LightSourceBucketOriginal.Procs P pOriginal
  main : P[pMain]? = some (body pOriginal)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem original_time_le (n g p m U D i : ℕ) :
    LightSourceBucketOriginal.time (len n g i) p m U D ≤ charge n g p m U D := by
  have ht := LightSourceBucketOriginal.time_bound (len n g i) p m U D
  apply ht.trans
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 498 (len_le_cap n g i))) (233*m)) 333

theorem tail_ends {pOriginal : ℕ} (C : LightSourceBucketOriginal.Procs P pOriginal)
    {μ : ℕ → ℤ} {src n g p m base U D i last : ℕ} {shift : ℤ} (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+3 < lim.depth)
    (hg : 0 < g) (hp : 0 < p) (hm : 0 < m) (hi : i < size n g)
    (hsrc : src+n ≤ base) (hlast : last=stop n g i)
    (hspace : LightSourceResidues.space (work base n g m) p U D ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (word n g p m U D : ℤ) ≤ lim.word)
    (hread : ∀ j < n, μ (src+j)=f j) (hvalues : ∀ j < n, |f j| ≤ (U : ℤ)) :
    Ends lim P d (tailBody pOriginal)
      ⟨frame [src,n,g,p,m,shift,base,cap n g,size n g,data base n g,stride n g m,
        work base n g m,i,start g i,last],μ⟩
      (tailTime n g p m U D) (fun σ =>
        SourceBandData.At σ.mem f base n g p m shift i ∧
        KeptBut μ σ.mem (hist base n g m i) (base+6*i) 6) := by
  subst last
  have hwork : work base n g m ≤ lim.space := by
    unfold LightSourceResidues.space at hspace
    omega
  have hcap := len_le_cap n g i
  have hflat := flat_end_le_work (base := base) (m := m) hi
  have hhead := header_end (base := base) (m := m) hi
  have hdata := data_le_hist base n g m i
  have hhist : hist base n g m i ≤ work base n g m := by
    unfold flat cursor offsets codes at hflat
    omega
  have hb : base ≤ hist base n g m i := by unfold data at hdata; omega
  have hstop := stop_le n g i
  have hstart := start_lt_stop hg hi
  have hlen := start_add_len hg hi
  have hprod : (i : ℤ)*(stride n g m : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show i*stride n g m ≤ lim.space by unfold hist at hhist; omega) :
      (i : ℤ)*(stride n g m : ℤ) ≤ lim.space).trans hw
  have hprodN : (0 : ℤ) ≤ (i : ℤ)*(stride n g m : ℤ) := by positivity
  have hheadprod : (6 : ℤ)*(i : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show 6*i ≤ lim.space by omega) : (6 : ℤ)*(i : ℤ) ≤ lim.space).trans hw
  have hcodes : codes base n g m i ≤ work base n g m := by
    unfold flat cursor offsets at hflat
    omega
  have hoffsets : offsets base n g m i ≤ work base n g m := by
    unfold flat cursor at hflat
    omega
  have hcursor : cursor base n g m i ≤ work base n g m := by unfold flat at hflat; omega
  have hhistAddr : (data base n g : ℤ)+(i : ℤ)*(stride n g m : ℤ) ≤ lim.word :=
    (by exact_mod_cast (hhist.trans hwork) :
      (data base n g : ℤ)+(i : ℤ)*(stride n g m : ℤ) ≤ lim.space).trans hw
  have hcodesAddr : hist base n g m i+m ≤ lim.space := hcodes.trans hwork
  have hoffsetsAddr : codes base n g m i+cap n g ≤ lim.space := hoffsets.trans hwork
  have hcursorAddr : offsets base n g m i+m+1 ≤ lim.space := hcursor.trans hwork
  have hflatAddr : cursor base n g m i+m ≤ lim.space := by unfold flat at hflat; omega
  have hword' : (LightSourceResidues.word p m U D : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show LightSourceResidues.word p m U D ≤ word n g p m U D by
      unfold word; omega)).trans hword
  unfold tailBody tailTime
  light_set (len n g i : ℕ) using len
  light_set (hist base n g m i : ℕ) using hist
  light_set (codes base n g m i : ℕ) using codes
  light_set (offsets base n g m i : ℕ) using offsets
  light_set (cursor base n g m i : ℕ) using cursor
  light_set (flat base n g m i : ℕ) using flat
  have horiginal := C.meets (d := d+1) (μ := μ) (src := src+start g i) (N := len n g i)
    (p := p) (m := m) (shift := shift) (hist := hist base n g m i) (codes := codes base n g m i)
    (offsets := offsets base n g m i) (cursor := cursor base n g m i) (flat := flat base n g m i)
    (work := work base n g m) (U := U) (D := D) hw (by omega) hp hm (by omega)
    le_rfl (by unfold offsets; omega) le_rfl le_rfl (by omega) hspace hshift hword'
    (by
      intro j hj
      have hj' := input_index hg hi hj
      rw [Nat.add_assoc,hread _ hj']
      exact hvalues _ hj')
  light_call (horiginal.mono_time (original_time_le n g p m U D i))
    with r ν ⟨buckets,counts,keys,kept⟩
  light_store (base+6*i) (start g i : ℕ)
  light_store (base+6*i+1) (len n g i : ℕ)
  light_store (base+6*i+2) (codes base n g m i : ℕ)
  light_store (base+6*i+3) (hist base n g m i : ℕ)
  light_store (base+6*i+4) (offsets base n g m i : ℕ)
  light_store (base+6*i+5) (flat base n g m i : ℕ)
  dsimp only
  have hkey : ∀ j < len n g i,
      LightSourceResidues.key p m shift (μ (src+start g i+j))=key f g p m shift i j := by
    intro j hj
    rw [Nat.add_assoc,hread _ (input_index hg hi hj)]
    rfl
  have stored := buckets_congr buckets hkey
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_,⟨?_,?_⟩⟩,?_⟩
  · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),
      Function.update_of_ne (by omega),Function.update_of_ne (by omega),
      Function.update_of_ne (by omega),Function.update_self]
  · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),
      Function.update_of_ne (by omega),Function.update_of_ne (by omega),Function.update_self]
  · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),
      Function.update_of_ne (by omega),Function.update_self]
  · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),Function.update_self]
  · rw [Function.update_of_ne (by omega),Function.update_self]
  · exact Function.update_self ..
  · intro j hj
    have ha : base+6*i+6 ≤ codes base n g m i+j := by unfold codes; omega
    repeat' rw [Function.update_of_ne (by omega)]
    exact (keys j hj).trans (congrArg Int.ofNat (hkey j hj))
  · intro q hq
    repeat' rw [Function.update_of_ne (by omega)]
    exact (counts q hq).trans (congrArg Int.ofNat (count_congr hkey le_rfl q))
  · intro q hq
    have ha : base+6*i+6 ≤ offsets base n g m i+q := by unfold offsets codes; omega
    repeat' rw [Function.update_of_ne (by omega)]
    exact stored.offsets q hq
  · intro j hj
    have ha : base+6*i+6 ≤ flat base n g m i+SourceBuckets.position (key f g p m shift i) (len n g i) j := by
      unfold flat cursor offsets codes
      omega
    repeat' rw [Function.update_of_ne (by omega)]
    exact stored.indices j hj
  · intro x hx
    repeat' rw [Function.update_of_ne (by omega)]
    exact kept x hx.1

theorem Procs.meets {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {src n g p m base U D i : ℕ} {shift : ℤ} (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+3 < lim.depth)
    (hg : 0 < g) (hp : 0 < p) (hm : 0 < m) (hi : i < size n g)
    (hsrc : src+n ≤ base)
    (hspace : LightSourceResidues.space (work base n g m) p U D ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (word n g p m U D : ℤ) ≤ lim.word)
    (hread : ∀ j < n, μ (src+j)=f j) (hvalues : ∀ j < n, |f j| ≤ (U : ℤ)) :
    Meets lim P pMain d
      [src,n,g,p,m,shift,base,cap n g,size n g,data base n g,stride n g m,work base n g m,i]
      μ (time n g p m U D) (fun _ ν =>
        SourceBandData.At ν f base n g p m shift i ∧
        KeptBut μ ν (hist base n g m i) (base+6*i) 6) := by
  have hidx : i*g < n := start_lt hg hi
  have hcount := size_le n g
  have hnext : (i+1)*g ≤ n+g := by nlinarith
  have hwordN : ((n+g+2 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show n+g+2 ≤ word n g p m U D by unfold word; omega)).trans hword
  have hprod : (i : ℤ)*(g : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show i*g ≤ n+g+2 by omega) :
      (i : ℤ)*(g : ℤ) ≤ ((n+g+2 : ℕ) : ℤ)).trans hwordN
  have hprodN : (0 : ℤ) ≤ (i : ℤ)*(g : ℤ) := by positivity
  have hnextZ : ((i : ℤ)+1)*(g : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show (i+1)*g ≤ n+g+2 by omega) :
      ((i : ℤ)+1)*(g : ℤ) ≤ ((n+g+2 : ℕ) : ℤ)).trans hwordN
  have hnextN : (0 : ℤ) ≤ ((i : ℤ)+1)*(g : ℤ) := by positivity
  have htailTime : tailTime n g p m U D=charge n g p m U D+1000 := rfl
  apply Meets.of_body C.main
  unfold body time
  light_set (start g i : ℕ) using start,tailTime
  light_set ((i+1)*g : ℕ) using tailTime
  light_if hlarge hlarge : (n : ℤ) < (((i+1)*g : ℕ) : ℤ) using tailTime
  · have hmin : n=stop n g i := by unfold stop; omega
    light_set (n : ℕ) using tailTime
    light_piece (tail_ends C.original (last := n) f hw hd hg hp hm hi hsrc hmin
      hspace hshift hword hread hvalues)
  · have hmin : (i+1)*g=stop n g i := by unfold stop; omega
    light_piece (tail_ends C.original (last := (i+1)*g) f hw hd hg hp hm hi hsrc hmin
      hspace hshift hword hread hvalues)

end ThreeSum.LightSourceBandStep
