import Submission.ThreeSum.LightBandRawAStep
import Submission.ThreeSum.BandRawAMemory

/-!
# The actual flattened A-incidence catalog

The loop reads each four-cell owner record once. Successful records append
only their actual truncated A band. Parallel value, owner-slot, and sorted
position arrays are packed using capacity g times the owner count.
-/

namespace ThreeSum.LightBandRawA

open Light BandCandidateRows BandRawA

set_option maxHeartbeats 2200000
set_option maxRecDepth 8000

def capacity (N g : ℕ) : ℕ := g*N
def ownerBase (vals N g : ℕ) : ℕ := vals+capacity N g
def positionBase (vals N g : ℕ) : ℕ := ownerBase vals N g+capacity N g
def space (vals N g : ℕ) : ℕ := positionBase vals N g+capacity N g
def word (n g N : ℕ) : ℕ := n+g+N+20
def time (N g : ℕ) : ℕ := N*(LightBandRawAStep.time g+200)+100

/-- Record base/count, sorted A base/length, g, first output address. -/
def body (pStep : ℕ) : Stmt :=
  .set 6 (v 4 *' v 1) ;;
  .set 7 (v 5 +' v 6) ;;
  .set 8 (v 7 +' v 6) ;;
  .set 9 (k 0) ;;
  .for 10 (v 1) (
    .set 11 (M (v 0 +' k 4 *' v 10)) ;;
    .set 12 (M (v 0 +' k 4 *' v 10 +' k 1)) ;;
    .call pStep [v 2,v 3,v 4,v 11,v 12,v 10,v 5,v 7,v 8,v 9] 9) ;;
  .set 0 (v 9)

def Inv (μ : ℕ → ℤ) (rs : List Record) (f : ℕ → ℤ)
    (records src n g vals i : ℕ) (σ : State) : Prop :=
  ∃ (flag a : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [records,rs.length,src,n,g,vals,capacity rs.length g,
      ownerBase vals rs.length g,positionBase vals rs.length g,count n g rs i,i,flag,a],ν⟩ ∧
    Stored ν vals (ownerBase vals rs.length g) (positionBase vals rs.length g)
      f (firstRows n g rs i) ∧ Kept μ ν vals

structure Procs (P : Program) (pMain : ℕ) where
  pStep : ℕ
  pRow : ℕ
  pCopy : ℕ
  pFill : ℕ
  step : P[pStep]?=some (LightBandRawAStep.body pRow)
  row : P[pRow]?=some (LightBandRawARow.body pCopy pFill)
  copy : P[pCopy]?=some copyBody
  fill : P[pFill]?=some fillBody
  main : P[pMain]?=some (body pStep)

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {records src n g vals : ℕ} {rs : List Record} {f : ℕ → ℤ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth) (hg : 0 < g)
    (hrecords : records+4*rs.length ≤ vals) (hsrc : src+n ≤ vals)
    (hspace : space vals rs.length g ≤ lim.space)
    (hword : (word n g rs.length : ℤ) ≤ lim.word)
    (hvalid : ∀ i < rs.length, (rs.getD i default).flag=1 →
      (rs.getD i default).a < BandPartition.size n g)
    (hrecordRead : Seg μ records (cells rs))
    (hread : ∀ j < n, μ (src+j)=f j) :
    Meets lim P pMain d [records,rs.length,src,n,g,vals] μ (time rs.length g)
      (fun r ν => r=((items n g rs).length : ℤ) ∧
        Stored ν vals (ownerBase vals rs.length g) (positionBase vals rs.length g)
          f (items n g rs) ∧ Kept μ ν vals) := by
  have hspace' : vals+capacity rs.length g+capacity rs.length g+capacity rs.length g ≤ lim.space := hspace
  have hcapWord : (g : ℤ)*(rs.length : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show capacity rs.length g ≤ lim.space by omega) :
      (g : ℤ)*(rs.length : ℤ) ≤ (lim.space : ℤ)).trans hw
  have hcapNonneg : (0 : ℤ) ≤ (g : ℤ)*(rs.length : ℤ) := by positivity
  have hnWord : (n : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word; omega : n ≤ word n g rs.length)).trans hword
  have hgWord : (g : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word; omega : g ≤ word n g rs.length)).trans hword
  have hNWord : (rs.length : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word; omega : rs.length ≤ word n g rs.length)).trans hword
  have howner : ownerBase vals rs.length g+capacity rs.length g=positionBase vals rs.length g := rfl
  have hvalues : vals+capacity rs.length g=ownerBase vals rs.length g := rfl
  have hposition : positionBase vals rs.length g+capacity rs.length g ≤ lim.space := hspace
  apply Meets.of_body S.main
  unfold body time
  light_set (capacity rs.length g : ℕ) using capacity
  light_set (ownerBase vals rs.length g : ℕ) using ownerBase
  light_set (positionBase vals rs.length g : ℕ) using positionBase
  light_set (0 : ℕ)
  refine Ends.pieceThen (Ends.for
    (T := rs.length*(LightBandRawAStep.time g+200)+6)
    (Q := Inv μ rs f records src n g vals rs.length)
    (Inv μ rs f records src n g vals) rs.length
    (LightBandRawAStep.time g+192) ?start ?round ?done ?bound) ?finish
  case start =>
    refine ⟨0,0,μ,?_,Stored.empty _ _ _ _ _,SameOn.refl⟩
    simp only [count_zero]
    simp [update_frame_setLocal]
    exact (frame_append_zeros [records,rs.length,src,n,g,vals,capacity rs.length g,
      ownerBase vals rs.length g,positionBase vals rs.length g,0,0] 2).symm
  case round =>
    rintro i _ hi _ ⟨flag,a,ν,rfl,stored,kept⟩
    have hnext : count n g rs (i+1) ≤ capacity rs.length g := by
      have hb := count_bound n g rs (i+1)
      have hm := Nat.mul_le_mul_left g (show i+1 ≤ rs.length by omega)
      exact hb.trans hm
    have hfit : count n g rs i+(BandRawA.row n g i (rs.getD i default)).length ≤ capacity rs.length g := by
      rwa [count_succ] at hnext
    have hstored : Seg ν records (cells rs) :=
      hrecordRead.of_kept kept (by simpa only [cells_length] using hrecords)
    have hfields := record_fields (seg_record hstored hi)
    have hflag := hfields.1
    have hA := hfields.2.1
    have hstepWord : ((n+g+i+10 : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (by unfold word; omega : n+g+i+10 ≤ word n g rs.length)).trans hword
    have hflagAddr : ((records : ℤ)+4*(i : ℤ)).toNat=records+4*i := by omega
    have hAAddr : ((records : ℤ)+4*(i : ℤ)+1).toNat=records+4*i+1 := by omega
    light_set ((rs.getD i default).flag : ℕ) using hflagAddr,hflag
    light_set ((rs.getD i default).a : ℕ) using hAAddr,hA
    have hc := LightBandRawAStep.meets (d := d+1) (μ := ν)
      (src := src) (n := n) (g := g) (owner := i) (r := rs.getD i default)
      (values := vals) (owners := ownerBase vals rs.length g)
      (positions := positionBase vals rs.length g) (previous := count n g rs i)
      (capacity := capacity rs.length g) S.step S.row S.copy S.fill hw (by omega) hg
      (hvalid i hi) hsrc hvalues.le howner.le hposition hfit hstepWord
    light_call hc with result ν₁ ⟨hresult,hout,hkeep⟩
    have hresult' : result=(count n g rs (i+1) : ℤ) := by
      simpa only [count_succ] using hresult
    have hold : Stored ν₁ vals (ownerBase vals rs.length g) (positionBase vals rs.length g)
        f (firstRows n g rs i) :=
      stored.keep_before_append hkeep hvalues.le howner.le hfit
    have hrowStored : Stored ν₁ (vals+count n g rs i)
        (ownerBase vals rs.length g+count n g rs i)
        (positionBase vals rs.length g+count n g rs i) f (BandRawA.row n g i (rs.getD i default)) := by
      apply row_stored
      intro j hj
      have hp := row_position_lt hj
      refine ⟨?_,(hout j hj).2.1,(hout j hj).2.2⟩
      rw [(hout j hj).1,kept _ (by omega)]
      simpa only [Nat.add_assoc] using hread _ hp
    refine ⟨by simp,(rs.getD i default).flag,(rs.getD i default).a,ν₁,?_,?_,?_⟩
    · simp [update_frame_setLocal,hresult']
    · rw [firstRows_succ]
      exact hold.append hrowStored
    · intro addr ha
      rw [hkeep addr ⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega)⟩,kept addr ha]
  case done =>
    rintro _ _ ⟨flag,a,ν,rfl,stored,kept⟩
    exact ⟨flag,a,ν,rfl,stored,kept⟩
  case bound =>
    rintro i _ _ _ ⟨flag,a,ν,rfl,_,_⟩
    light_side
  case finish =>
    rintro _ ⟨flag,a,ν,rfl,stored,kept⟩
    have hc := count_bound n g rs rs.length
    have hcWord : (count n g rs rs.length : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (show count n g rs rs.length ≤ lim.space by
        change count n g rs rs.length ≤ capacity rs.length g at hc
        omega)).trans hw
    light_set (count n g rs rs.length : ℕ)
    exact ⟨rfl,stored,kept⟩

def program : Program :=
  [body 1,LightBandRawAStep.body 2,LightBandRawARow.body 3 4,copyBody,fillBody]

def programProcs : Procs program 0 := ⟨1,2,3,4,rfl,rfl,rfl,rfl,rfl⟩

theorem program_meets
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth) (hg : 0 < g)
    (hrecords : records+4*rs.length ≤ vals) (hsrc : src+n ≤ vals)
    (hspace : space vals rs.length g ≤ lim.space)
    (hword : (word n g rs.length : ℤ) ≤ lim.word)
    (hvalid : ∀ i < rs.length, (rs.getD i default).flag=1 →
      (rs.getD i default).a < BandPartition.size n g)
    (hrecordRead : Seg μ records (cells rs))
    (hread : ∀ j < n, μ (src+j)=f j) :
    Meets lim program 0 d [records,rs.length,src,n,g,vals] μ (time rs.length g)
      (fun r ν => r=((items n g rs).length : ℤ) ∧
        Stored ν vals (ownerBase vals rs.length g) (positionBase vals rs.length g)
          f (items n g rs) ∧ Kept μ ν vals) :=
  programProcs.meets hw hd hg hrecords hsrc hspace hword hvalid hrecordRead hread

/-- The physical candidate list supplies every successful A-index validity
fact required by the actual incidence loop. -/
theorem Procs.meets_candidates {pMain : ℕ} (S : Procs P pMain)
    (A B C : BandEnumeration.Family) (hA : A.size=BandPartition.size n g)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth) (hg : 0 < g)
    (hrecords : records+4*(BandCandidateRows.records A B C).length ≤ vals)
    (hsrc : src+n ≤ vals)
    (hspace : space vals (BandCandidateRows.records A B C).length g ≤ lim.space)
    (hword : (word n g (BandCandidateRows.records A B C).length : ℤ) ≤ lim.word)
    (hrecordRead : Seg μ records (cells (BandCandidateRows.records A B C)))
    (hread : ∀ j < n, μ (src+j)=f j) :
    Meets lim P pMain d [records,(BandCandidateRows.records A B C).length,src,n,g,vals]
      μ (time (BandCandidateRows.records A B C).length g)
      (fun r ν => r=((items n g (BandCandidateRows.records A B C)).length : ℤ) ∧
        Stored ν vals (ownerBase vals (BandCandidateRows.records A B C).length g)
          (positionBase vals (BandCandidateRows.records A B C).length g)
          f (items n g (BandCandidateRows.records A B C)) ∧ Kept μ ν vals) := by
  apply S.meets hw hd hg hrecords hsrc hspace hword _ hrecordRead hread
  intro i hi hf
  simpa only [hA] using (getD_sound hi hf).1

theorem time_bound (N g : ℕ) : time N g ≤ 1000*(N+1)*(g+1) := by
  unfold time LightBandRawAStep.time LightBandRawARow.time copyTime fillTime
  nlinarith

end ThreeSum.LightBandRawA
