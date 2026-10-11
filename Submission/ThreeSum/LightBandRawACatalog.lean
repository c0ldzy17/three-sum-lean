import Submission.ThreeSum.LightBandCandidates
import Submission.ThreeSum.LightBandRawA
import Submission.ThreeSum.LightHeaderBands

/-!
# Read the retained headers, build owner records, and extract A incidences

The fixed program reads the actual sorted-A length and all three actual
band counts from the retained headers. It constructs the exact physical
BC, AB, AC records, then copies their flagged A bands into the three packed
value/owner/position arrays. No supplied enumeration or hidden input list
is used by either machine loop.
-/

namespace ThreeSum.LightBandRawACatalog

open Light BandEnumeration BandCandidateRows BandRawA

set_option maxHeartbeats 2100000
set_option maxRecDepth 8000

/-- Tables, record output, sorted A, A/B/C headers, g, value output. -/
def body (pCandidates pRaw : ℕ) : Stmt :=
  .set 8 (M (v 3)) ;;
  .set 9 (M (v 3 +' k 1)) ;;
  .set 10 (M (v 4 +' k 1)) ;;
  .set 11 (M (v 5 +' k 1)) ;;
  .call pCandidates [v 0,v 1,v 9,v 10,v 11] 12 ;;
  .call pRaw [v 1,v 12,v 2,v 8,v 6,v 7] 0

def time (a b c g : ℕ) : ℕ :=
  LightBandCandidates.time a b c+LightBandRawA.time (LightBandEnumeration.count a b c) g+300

def word (n a b c g : ℕ) : ℕ :=
  LightBandCandidates.word a b c+LightBandRawA.word n g (LightBandEnumeration.count a b c)+20

def space (vals a b c g : ℕ) : ℕ :=
  LightBandRawA.space vals (LightBandEnumeration.count a b c) g

structure Procs (P : Program) (pMain : ℕ) where
  pCandidates : ℕ
  pRaw : ℕ
  candidates : LightBandCandidates.Procs P pCandidates
  raw : LightBandRawA.Procs P pRaw
  main : P[pMain]?=some (body pCandidates pRaw)

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {tables rec src headerA headerB headerC nA nB nC g vals : ℕ} {f : ℕ → ℤ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain) (A B C : Family)
    (hA : A.size=BandPartition.size nA g)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+3 < lim.depth) (hg : 0 < g)
    (htable : tables+LightBandEnumeration.count A.size B.size C.size ≤ rec)
    (hsrc : src+nA ≤ rec) (hheadA : headerA+2 ≤ rec)
    (hheadB : headerB+2 ≤ rec) (hheadC : headerC+2 ≤ rec)
    (hrec : rec+4*LightBandEnumeration.count A.size B.size C.size ≤ vals)
    (hspace : space vals A.size B.size C.size g ≤ lim.space)
    (hword : (word nA A.size B.size C.size g : ℤ) ≤ lim.word)
    (hheaderA : LightHeaderBands.At μ headerA nA A)
    (hheaderB : LightHeaderBands.At μ headerB nB B)
    (hheaderC : LightHeaderBands.At μ headerC nC C)
    (htables : LightBandEnumeration.Tables μ tables A B C)
    (hread : ∀ j < nA, μ (src+j)=f j) :
    Meets lim P pMain d [tables,rec,src,headerA,headerB,headerC,g,vals]
      μ (time A.size B.size C.size g)
      (fun r ν => r=((items nA g (records A B C)).length : ℤ) ∧
        Seg ν rec (cells (records A B C)) ∧
        Stored ν vals (LightBandRawA.ownerBase vals (LightBandEnumeration.count A.size B.size C.size) g)
          (LightBandRawA.positionBase vals (LightBandEnumeration.count A.size B.size C.size) g)
          f (items nA g (records A B C)) ∧ Kept μ ν rec) := by
  have hvals : vals ≤ lim.space := by
    unfold space LightBandRawA.space LightBandRawA.positionBase LightBandRawA.ownerBase at hspace
    omega
  have hcandidateSpace : LightBandCandidates.space rec A.size B.size C.size ≤ lim.space := by
    unfold LightBandCandidates.space
    omega
  have hcandidateWord : (LightBandCandidates.word A.size B.size C.size : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word; omega :
      LightBandCandidates.word A.size B.size C.size ≤ word nA A.size B.size C.size g)).trans hword
  have hrawWord : (LightBandRawA.word nA g (LightBandEnumeration.count A.size B.size C.size) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word; omega :
      LightBandRawA.word nA g (LightBandEnumeration.count A.size B.size C.size) ≤
        word nA A.size B.size C.size g)).trans hword
  have h1Word : (1 : ℤ) ≤ lim.word := by
    have hh : 1 ≤ word nA A.size B.size C.size g := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hnRead := hheaderA.1
  have haRead := hheaderA.2.1
  have hbRead := hheaderB.2.1
  have hcRead := hheaderC.2.1
  have haAddr : ((headerA : ℤ)+1).toNat=headerA+1 := by omega
  have hbAddr : ((headerB : ℤ)+1).toNat=headerB+1 := by omega
  have hcAddr : ((headerC : ℤ)+1).toNat=headerC+1 := by omega
  apply Meets.of_body S.main
  unfold body time
  light_set (nA : ℕ) using hnRead
  light_set (A.size : ℕ) using haAddr,haRead
  light_set (B.size : ℕ) using hbAddr,hbRead
  light_set (C.size : ℕ) using hcAddr,hcRead
  light_call (S.candidates.meets (d := d+1) A B C hw (by omega)
    htable hcandidateSpace hcandidateWord htables)
    with countResult ν₁ ⟨hcount,hrecords,hkeepCandidates⟩
  have hsource : ∀ j < nA, ν₁ (src+j)=f j := by
    intro j hj
    rw [hkeepCandidates _ (Or.inl (by omega))]
    exact hread j hj
  have hraw := S.raw.meets_candidates (d := d+1) (records := rec) (src := src)
    (vals := vals) (n := nA) (g := g) (f := f) A B C hA hw (by omega) hg
    (by simpa only [records_length] using hrec) (by omega)
    (by simpa only [records_length,space] using hspace)
    (by simpa only [records_length] using hrawWord) hrecords hsource
  have hraw' : Meets lim P S.pRaw (d+1)
      [rec,LightBandEnumeration.count A.size B.size C.size,src,nA,g,vals] ν₁
      (LightBandRawA.time (LightBandEnumeration.count A.size B.size C.size) g)
      (fun r ν => r=((items nA g (records A B C)).length : ℤ) ∧
        Stored ν vals (LightBandRawA.ownerBase vals (LightBandEnumeration.count A.size B.size C.size) g)
          (LightBandRawA.positionBase vals (LightBandEnumeration.count A.size B.size C.size) g)
          f (items nA g (records A B C)) ∧ Kept ν₁ ν vals) := by
    simpa only [records_length] using hraw
  light_call hraw' using hcount with result ν₂ ⟨hresult,hstored,hkeepRaw⟩
  refine ⟨hresult,?_,hstored,?_⟩
  · exact hrecords.of_kept hkeepRaw (by simpa only [cells_length,records_length] using hrec)
  · intro addr ha
    change ν₂ addr=μ addr
    rw [hkeepRaw addr (by omega),hkeepCandidates addr (Or.inl ha)]

def program : Program :=
  [body 1 11,
    LightBandCandidates.body 2 5 8,
    LightBandCandidatesTable.body 3,LightBandCandidatesRow.body 4,LightBandCandidatesCell.body .bc,
    LightBandCandidatesTable.body 6,LightBandCandidatesRow.body 7,LightBandCandidatesCell.body .ab,
    LightBandCandidatesTable.body 9,LightBandCandidatesRow.body 10,LightBandCandidatesCell.body .ac,
    LightBandRawA.body 12,LightBandRawAStep.body 13,LightBandRawARow.body 14 15,copyBody,fillBody]

def programProcs : Procs program 0 where
  pCandidates := 1
  pRaw := 11
  candidates := ⟨2,5,8,3,6,9,4,7,10,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  raw := ⟨12,13,14,15,rfl,rfl,rfl,rfl,rfl⟩
  main := rfl

theorem program_meets (A B C : Family) (hA : A.size=BandPartition.size nA g)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+3 < lim.depth) (hg : 0 < g)
    (htable : tables+LightBandEnumeration.count A.size B.size C.size ≤ rec)
    (hsrc : src+nA ≤ rec) (hheadA : headerA+2 ≤ rec)
    (hheadB : headerB+2 ≤ rec) (hheadC : headerC+2 ≤ rec)
    (hrec : rec+4*LightBandEnumeration.count A.size B.size C.size ≤ vals)
    (hspace : space vals A.size B.size C.size g ≤ lim.space)
    (hword : (word nA A.size B.size C.size g : ℤ) ≤ lim.word)
    (hheaderA : LightHeaderBands.At μ headerA nA A)
    (hheaderB : LightHeaderBands.At μ headerB nB B)
    (hheaderC : LightHeaderBands.At μ headerC nC C)
    (htables : LightBandEnumeration.Tables μ tables A B C)
    (hread : ∀ j < nA, μ (src+j)=f j) :
    Meets lim program 0 d [tables,rec,src,headerA,headerB,headerC,g,vals]
      μ (time A.size B.size C.size g)
      (fun r ν => r=((items nA g (records A B C)).length : ℤ) ∧
        Seg ν rec (cells (records A B C)) ∧
        Stored ν vals (LightBandRawA.ownerBase vals (LightBandEnumeration.count A.size B.size C.size) g)
          (LightBandRawA.positionBase vals (LightBandEnumeration.count A.size B.size C.size) g)
          f (items nA g (records A B C)) ∧ Kept μ ν rec) :=
  programProcs.meets A B C hA hw hd hg htable hsrc hheadA hheadB hheadC hrec hspace hword
    hheaderA hheaderB hheaderC htables hread

theorem time_bound (a b c g : ℕ) :
    time a b c g ≤ 3000*(LightBandEnumeration.count a b c+a+b+c+1)*(g+1) := by
  have hc := LightBandCandidates.time_bound a b c
  have hr := LightBandRawA.time_bound (LightBandEnumeration.count a b c) g
  unfold time
  nlinarith

end ThreeSum.LightBandRawACatalog
