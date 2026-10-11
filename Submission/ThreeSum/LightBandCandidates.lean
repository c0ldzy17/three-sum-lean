import Submission.ThreeSum.LightBandCandidatesTable

/-!
# All actual flagged band-owner records

The fixed program reads the three retained rectangular lookup tables and
writes one four-cell record for each cell, in the same BC, AB, AC order.
The record position is its permanent owner-slot identity.
-/

namespace ThreeSum.LightBandCandidates

open Light BandEnumeration BandCandidateRows

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

def body (pBC pAB pAC : ℕ) : Stmt :=
  .set 5 (v 3 *' v 4) ;;
  .set 6 (v 2 *' v 3) ;;
  .set 7 (v 2 *' v 4) ;;
  .set 8 (v 5 +' v 6 +' v 7) ;;
  .call pBC [v 0,v 1,v 3,v 4] 9 ;;
  .call pAB [v 0 +' v 5,v 1 +' k 4 *' v 5,v 2,v 3] 9 ;;
  .call pAC [v 0 +' v 5 +' v 6,v 1 +' k 4 *' (v 5 +' v 6),v 2,v 4] 9 ;;
  .set 0 (v 8)

def time (a b c : ℕ) : ℕ :=
  LightBandCandidatesTable.time b c+LightBandCandidatesTable.time a b+
    LightBandCandidatesTable.time a c+250

def word (a b c : ℕ) : ℕ := a+b+c+10

def space (dst a b c : ℕ) : ℕ := dst+4*LightBandEnumeration.count a b c

structure Procs (P : Program) (pMain : ℕ) where
  pBC : ℕ
  pAB : ℕ
  pAC : ℕ
  pRowBC : ℕ
  pRowAB : ℕ
  pRowAC : ℕ
  pCellBC : ℕ
  pCellAB : ℕ
  pCellAC : ℕ
  bc : P[pBC]?=some (LightBandCandidatesTable.body pRowBC)
  ab : P[pAB]?=some (LightBandCandidatesTable.body pRowAB)
  ac : P[pAC]?=some (LightBandCandidatesTable.body pRowAC)
  rowBC : P[pRowBC]?=some (LightBandCandidatesRow.body pCellBC)
  rowAB : P[pRowAB]?=some (LightBandCandidatesRow.body pCellAB)
  rowAC : P[pRowAC]?=some (LightBandCandidatesRow.body pCellAC)
  cellBC : P[pCellBC]?=some (LightBandCandidatesCell.body .bc)
  cellAB : P[pCellAB]?=some (LightBandCandidatesCell.body .ab)
  cellAC : P[pCellAC]?=some (LightBandCandidatesCell.body .ac)
  main : P[pMain]?=some (body pBC pAB pAC)

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {src dst : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain) (A B C : Family)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hsrc : src+LightBandEnumeration.count A.size B.size C.size ≤ dst)
    (hspace : space dst A.size B.size C.size ≤ lim.space)
    (hword : (word A.size B.size C.size : ℤ) ≤ lim.word)
    (htables : LightBandEnumeration.Tables μ src A B C) :
    Meets lim P pMain d [src,dst,A.size,B.size,C.size] μ (time A.size B.size C.size)
      (fun r ν => r=(LightBandEnumeration.count A.size B.size C.size : ℤ) ∧
        Seg ν dst (cells (records A B C)) ∧
        SameOutside μ ν dst (4*LightBandEnumeration.count A.size B.size C.size)) := by
  let U := A.size+B.size+C.size
  let bcN := B.size*C.size
  let abN := A.size*B.size
  let acN := A.size*C.size
  have hcount : LightBandEnumeration.count A.size B.size C.size=bcN+abN+acN := rfl
  have hsrc' : src+bcN+abN+acN ≤ dst := by simpa only [hcount,Nat.add_assoc] using hsrc
  have hspace' : dst+4*(bcN+abN+acN) ≤ lim.space := hspace
  have hAU : A.size ≤ U := by unfold U; omega
  have hBU : B.size ≤ U := by unfold U; omega
  have hCU : C.size ≤ U := by unfold U; omega
  have hwordU : ((U+10 : ℕ) : ℤ) ≤ lim.word := hword
  have hAWord : (A.size : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : A.size ≤ U+10)).trans hwordU
  have hBWord : (B.size : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : B.size ≤ U+10)).trans hwordU
  have hCWord : (C.size : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : C.size ≤ U+10)).trans hwordU
  have hbcWord : (B.size : ℤ)*(C.size : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show bcN ≤ lim.space by omega) :
      (B.size : ℤ)*(C.size : ℤ) ≤ (lim.space : ℤ)).trans hw
  have habWord : (A.size : ℤ)*(B.size : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show abN ≤ lim.space by omega) :
      (A.size : ℤ)*(B.size : ℤ) ≤ (lim.space : ℤ)).trans hw
  have hacWord : (A.size : ℤ)*(C.size : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show acN ≤ lim.space by omega) :
      (A.size : ℤ)*(C.size : ℤ) ≤ (lim.space : ℤ)).trans hw
  have hbcNonneg : (0 : ℤ) ≤ (B.size : ℤ)*(C.size : ℤ) := by positivity
  have habNonneg : (0 : ℤ) ≤ (A.size : ℤ)*(B.size : ℤ) := by positivity
  have hacNonneg : (0 : ℤ) ≤ (A.size : ℤ)*(C.size : ℤ) := by positivity
  have hbcBound : ∀ j < B.size, ∀ k < C.size,
      LightBandLookup.result A.lower A.upper A.size (C.lower k-B.upper j) ≤ U := by
    intro j _ k _
    exact (LightBandLookup.result_le _ _ _ _ A.sorted).trans hAU
  have habBound : ∀ i < A.size, ∀ j < B.size,
      LightBandLookup.result C.lower C.upper C.size (A.lower i+B.lower j) ≤ U := by
    intro i _ j _
    exact (LightBandLookup.result_le _ _ _ _ C.sorted).trans hCU
  have hacBound : ∀ i < A.size, ∀ k < C.size,
      LightBandLookup.result B.lower B.upper B.size (C.lower k-A.lower i) ≤ U := by
    intro i _ k _
    exact (LightBandLookup.result_le _ _ _ _ B.sorted).trans hBU
  apply Meets.of_body S.main
  unfold body time
  light_set (bcN : ℕ) using bcN
  light_set (abN : ℕ) using abN
  light_set (acN : ℕ) using acN
  light_set (bcN+abN+acN : ℕ)
  have hcBC := LightBandCandidatesTable.meets_segment (d := d+1) (μ := μ)
    (src := src) (dst := dst) .bc S.bc S.rowBC S.cellBC hw (by omega)
    (by change src+bcN ≤ dst; omega) (by change dst+4*bcN ≤ lim.space; omega)
    hwordU hBU hCU hbcBound htables.1
  light_call hcBC using LightBandCandidatesTable.time,LightBandCandidatesRow.time,
    LightBandCandidatesCell.time with unused ν₁ ⟨hbc,hkeepBC⟩
  have habRead : ∀ i < A.size, ∀ j < B.size,
      ν₁ (src+bcN+i*B.size+j)=
        (LightBandLookup.result C.lower C.upper C.size (A.lower i+B.lower j) : ℤ) := by
    intro i hi j hj
    have hh := index_lt hi hj
    rw [hkeepBC _ (Or.inl (by change i*B.size+j < abN at hh; omega))]
    exact htables.2.1 i hi j hj
  have hcAB := LightBandCandidatesTable.meets_segment (d := d+1) (μ := ν₁)
    (src := src+bcN) (dst := dst+4*bcN) .ab S.ab S.rowAB S.cellAB hw (by omega)
    (by change src+bcN+abN ≤ dst+4*bcN; omega)
    (by change dst+4*bcN+4*abN ≤ lim.space; omega)
    hwordU hAU hBU habBound habRead
  light_call hcAB using LightBandCandidatesTable.time,LightBandCandidatesRow.time,
    LightBandCandidatesCell.time with unused ν₂ ⟨hab,hkeepAB⟩
  have hacRead : ∀ i < A.size, ∀ k < C.size,
      ν₂ (src+bcN+abN+i*C.size+k)=
        (LightBandLookup.result B.lower B.upper B.size (C.lower k-A.lower i) : ℤ) := by
    intro i hi k hk
    have hh := index_lt hi hk
    rw [hkeepAB _ (Or.inl (by change i*C.size+k < acN at hh; omega)),
      hkeepBC _ (Or.inl (by change i*C.size+k < acN at hh; omega))]
    exact htables.2.2 i hi k hk
  have hcAC := LightBandCandidatesTable.meets_segment (d := d+1) (μ := ν₂)
    (src := src+bcN+abN) (dst := dst+4*(bcN+abN)) .ac S.ac S.rowAC S.cellAC hw (by omega)
    (by change src+bcN+abN+acN ≤ dst+4*(bcN+abN); omega)
    (by change dst+4*(bcN+abN)+4*acN ≤ lim.space; omega)
    hwordU hAU hCU hacBound hacRead
  light_call hcAC using LightBandCandidatesTable.time,LightBandCandidatesRow.time,
    LightBandCandidatesCell.time with unused ν₃ ⟨hac,hkeepAC⟩
  have hbc' : Seg ν₃ dst (cells (rect B.size C.size (BandCandidateRows.bc A B C))) := by
    apply (hbc.of_sameOutside hkeepAB (Or.inl (by rw [cells_length,rect_length]))).of_sameOutside
      hkeepAC (Or.inl (by rw [cells_length,rect_length]; change dst+4*bcN ≤ dst+4*(bcN+abN); omega))
  have hab' : Seg ν₃ (dst+4*bcN) (cells (rect A.size B.size (BandCandidateRows.ab A B C))) :=
    hab.of_sameOutside hkeepAC (Or.inl (by
      rw [cells_length,rect_length]
      change dst+4*bcN+4*abN ≤ dst+4*(bcN+abN)
      omega))
  light_set (LightBandEnumeration.count A.size B.size C.size : ℕ) using hcount
  refine ⟨rfl,?_,?_⟩
  · rw [records,cells,List.flatMap_append,List.flatMap_append]
    change Seg ν₃ dst (cells (rect B.size C.size (BandCandidateRows.bc A B C)) ++
      (cells (rect A.size B.size (BandCandidateRows.ab A B C)) ++ cells (rect A.size C.size (BandCandidateRows.ac A B C))))
    apply seg_append.mpr
    refine ⟨hbc',?_⟩
    rw [cells_length,rect_length]
    apply seg_append.mpr
    refine ⟨hab',?_⟩
    rw [cells_length,rect_length]
    change Seg ν₃ (dst+4*bcN+4*abN)
      (cells (rect A.size C.size (fun i k => make .ac i k
        (LightBandLookup.result B.lower B.upper B.size (C.lower k-A.lower i)))))
    rw [show dst+4*bcN+4*abN=dst+4*(bcN+abN) by ring]
    exact hac
  · intro a ha
    change ν₃ a=μ a
    unfold Outside at ha
    rw [hkeepAC a (by unfold Outside; rw [hcount] at ha; omega),
      hkeepAB a (by unfold Outside; rw [hcount] at ha; omega),
      hkeepBC a (by unfold Outside; rw [hcount] at ha; omega)]

def program : Program :=
  [body 1 2 3,LightBandCandidatesTable.body 4,LightBandCandidatesTable.body 5,
    LightBandCandidatesTable.body 6,LightBandCandidatesRow.body 7,
    LightBandCandidatesRow.body 8,LightBandCandidatesRow.body 9,
    LightBandCandidatesCell.body .bc,LightBandCandidatesCell.body .ab,LightBandCandidatesCell.body .ac]

def programProcs : Procs program 0 :=
  ⟨1,2,3,4,5,6,7,8,9,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem program_meets (A B C : Family)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hsrc : src+LightBandEnumeration.count A.size B.size C.size ≤ dst)
    (hspace : space dst A.size B.size C.size ≤ lim.space)
    (hword : (word A.size B.size C.size : ℤ) ≤ lim.word)
    (htables : LightBandEnumeration.Tables μ src A B C) :
    Meets lim program 0 d [src,dst,A.size,B.size,C.size] μ (time A.size B.size C.size)
      (fun r ν => r=(LightBandEnumeration.count A.size B.size C.size : ℤ) ∧
        Seg ν dst (cells (records A B C)) ∧
        SameOutside μ ν dst (4*LightBandEnumeration.count A.size B.size C.size)) :=
  programProcs.meets A B C hw hd hsrc hspace hword htables

theorem time_bound (a b c : ℕ) :
    time a b c ≤ 1000*(LightBandEnumeration.count a b c+a+b+c+1) := by
  unfold time LightBandCandidatesTable.time LightBandCandidatesRow.time
    LightBandCandidatesCell.time LightBandEnumeration.count
  nlinarith

end ThreeSum.LightBandCandidates
