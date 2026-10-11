import Submission.ThreeSum.WantedRecordOrder

/-!
# Completeness of the physical wanted-record array

The pair array produced by the selected-offset join covers every original
guarded wanted label. Conversely every stored pair selects such a label.
These statements concern the actual emitted array, including duplicate
integer keys at different source positions.
-/

namespace ThreeSum.WantedRecordCoverage

open Light GlobalEncoding GlobalKeyEnumeration WantedRecordOrder

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000

theorem label_surjective {xs : List ℤ} {h J : ℕ}
    (w : RawReporting.Wanted h J (Fin xs.length)) :
    ∃ i j, ∃ hi : i < 3*xs.length,
      j < LightGuardedWanted.totalKeys h J ∧ label h J i j hi=w := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp (RawAKeyLists.mem_records xs (w.2.1,w.1))
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp (mem_globalRecords h J w.2.2)
  have hi' : i.val < 3*xs.length := by
    simpa only [RawAKeyLists.records_length] using i.isLt
  have hj' : j.val < LightGuardedWanted.totalKeys h J := by
    have hj0 : j.val < OutputDecodeRecords.localCount h^J := by
      simpa only [OutputDecodeRecords.globalRecords_length'] using j.isLt
    exact hj0
  have hrec : (RawAKeyLists.records xs).getD i.val (0,⟨0,input_length_pos hi'⟩)=
      (w.2.1,w.1) := by
    simpa only [List.getD_eq_getElem _ _ i.isLt,List.get_eq_getElem] using hi
  rw [records_getD hi'] at hrec
  have hposition := congrArg (fun r : Fin 3 × Fin xs.length => r.2) hrec
  have hlift := congrArg (fun r : Fin 3 × Fin xs.length => r.1) hrec
  dsimp only at hposition hlift
  have hout : LightOutputDecodeOriginal.output h J j.val=w.2.2 := by
    simpa only [LightOutputDecodeOriginal.output,
      List.getD_eq_getElem _ _ j.isLt,List.get_eq_getElem] using hj
  refine ⟨i.val,j.val,hi',hj',?_⟩
  unfold label
  rw [hposition,hlift,hout]

theorem output_pair {μ : ℕ → ℤ} {free M P h J slot : ℕ} {shift : ℤ} {xs : List ℤ}
    (H : LightWantedSetup.Output μ free M (LightGuardedWanted.left P xs)
      (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J) shift)
    (hk : slot < (μ free).toNat) :
    ∃ i j, ∃ hi : i < 3*xs.length,
      j < LightGuardedWanted.totalKeys h J ∧
      μ (LightWantedSetup.pairBase free (3*xs.length) (LightGuardedWanted.totalKeys h J) M+2*slot)=(i : ℤ) ∧
      μ (LightWantedSetup.pairBase free (3*xs.length) (LightGuardedWanted.totalKeys h J) M+2*slot+1)=(j : ℤ) ∧
      label h J i j hi ∈ RawAKeyLists.wanted M P xs h J shift := by
  rcases H with ⟨hcount,_,_,_,ps,hlen,_,hmem,hseg⟩
  have hk' : slot < ps.length := by rw [hlen]; simpa only [hcount,Int.toNat_natCast] using hk
  let p := ps.getD slot (0,0)
  have hp : p ∈ ps := by
    rw [show p=ps[slot] from List.getD_eq_getElem _ _ hk']
    exact List.getElem_mem hk'
  have hb := (hmem p.1 p.2).mp hp
  have hread := segment_pair hseg hk'
  refine ⟨p.1,p.2,hb.1,hb.2.1,hread.1,hread.2,?_⟩
  exact (mem_wanted_iff hb.1 hb.2.1).mpr hb.2.2

theorem output_complete {μ : ℕ → ℤ} {free M P h J : ℕ} {shift : ℤ} {xs : List ℤ}
    (H : LightWantedSetup.Output μ free M (LightGuardedWanted.left P xs)
      (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J) shift)
    {w : RawReporting.Wanted h J (Fin xs.length)}
    (hw : w ∈ RawAKeyLists.wanted M P xs h J shift) :
    ∃ slot i j, ∃ hi : i < 3*xs.length,
      slot < (μ free).toNat ∧ j < LightGuardedWanted.totalKeys h J ∧
      μ (LightWantedSetup.pairBase free (3*xs.length) (LightGuardedWanted.totalKeys h J) M+2*slot)=(i : ℤ) ∧
      μ (LightWantedSetup.pairBase free (3*xs.length) (LightGuardedWanted.totalKeys h J) M+2*slot+1)=(j : ℤ) ∧
      label h J i j hi=w := by
  obtain ⟨i,j,hi,hj,he⟩ := label_surjective w
  have hdiv := (mem_wanted_iff hi hj).mp (he.symm ▸ hw)
  rcases H with ⟨hcount,_,_,_,ps,hlen,_,hmem,hseg⟩
  have hp : (i,j) ∈ ps := (hmem i j).mpr ⟨hi,hj,hdiv⟩
  obtain ⟨k,hk⟩ := List.mem_iff_get.mp hp
  have hget : ps.getD k.val (0,0)=(i,j) := by
    simpa only [List.getD_eq_getElem _ _ k.isLt,List.get_eq_getElem] using hk
  have hread := segment_pair hseg k.isLt
  rw [hget] at hread
  refine ⟨k.val,i,j,hi,?_,hj,hread.1,hread.2,he⟩
  rw [hcount,Int.toNat_natCast,← hlen]
  exact k.isLt

end ThreeSum.WantedRecordCoverage
