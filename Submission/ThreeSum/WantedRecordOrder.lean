import Submission.ThreeSum.LightGuardedWanted
import Submission.ThreeSum.LightOutputDecodeOriginal

/-!
# Original wanted labels behind the interleaved pair indices

Left indices recover the A-incidence position and its lift. Right indices
recover the unchanged global output record. The maps retain distinct source
positions even when their integer key values coincide.
-/

namespace ThreeSum.WantedRecordOrder

open GlobalEncoding GlobalKeyEnumeration RawIncidences RawAKeyLists
open OutputDecodeOrder

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

theorem input_length_pos {xs : List ℤ} {i : ℕ} (hi : i < 3*xs.length) : 0 < xs.length := by omega

theorem records_getD {xs : List ℤ} {i : ℕ} (hi : i < 3*xs.length) :
    (RawAKeyLists.records xs).getD i (0,⟨0,input_length_pos hi⟩) =
      (⟨i/xs.length,(Nat.div_lt_iff_lt_mul (input_length_pos hi)).mpr hi⟩,
        ⟨i%xs.length,Nat.mod_lt _ (input_length_pos hi)⟩) := by
  have hN : 0 < xs.length := input_length_pos hi
  change (RawAKeyLists.records xs).getD i (0,⟨0,hN⟩)=_
  have hq : i/xs.length < 3 := (Nat.div_lt_iff_lt_mul (input_length_pos hi)).mpr hi
  have hr : i%xs.length < xs.length := Nat.mod_lt _ (input_length_pos hi)
  have he : i/xs.length*xs.length+i%xs.length=i := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod i xs.length
  unfold RawAKeyLists.records List.product
  conv_lhs => rw [← he]
  rw [getD_flatMap_uniform _ _ xs.length (by simp) (0 : Fin 3)
    ((0,⟨0,hN⟩) : RawAKeyLists.Record xs)
    (by simpa only [List.length_finRange] using hq) hr]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map,List.length_finRange] using hr),
    List.getElem_map]
  congr 1
  · rw [List.getD_eq_getElem _ _ (by simpa only [List.length_finRange] using hq)]
    apply Fin.ext
    simp
  · apply Fin.ext
    simp

theorem key_getD {P : ℤ} {xs : List ℤ} {i : ℕ} (hi : i < 3*xs.length) :
    (RawAKeyLists.keys P xs).getD i 0=
      xs.getD (i%xs.length) 0%P+
        lift ⟨i/xs.length,(Nat.div_lt_iff_lt_mul (input_length_pos hi)).mpr hi⟩*P := by
  unfold RawAKeyLists.keys
  rw [List.getD_map_of_lt _ (by rwa [RawAKeyLists.records_length])
    ((0,⟨0,input_length_pos hi⟩) : RawAKeyLists.Record xs) 0,records_getD hi]
  rfl

def label {xs : List ℤ} (h J i j : ℕ) (hi : i < 3*xs.length) :
    RawReporting.Wanted h J (Fin xs.length) :=
  (⟨i%xs.length,Nat.mod_lt _ (input_length_pos hi)⟩,
    (⟨i/xs.length,(Nat.div_lt_iff_lt_mul (input_length_pos hi)).mpr hi⟩,
      LightOutputDecodeOriginal.output h J j))

theorem mem_wanted_iff {M h J i j : ℕ} {P shift : ℤ} {xs : List ℤ}
    (hi : i < 3*xs.length) (hj : j < LightGuardedWanted.totalKeys h J) :
    label h J i j hi ∈ RawAKeyLists.wanted M P xs h J shift ↔
      (M : ℤ) ∣ (RawAKeyLists.keys P xs).getD i 0+shift-(globalKeys h J).getD j 0 := by
  rw [RawAKeyLists.mem_wanted,key_getD hi,
    OutputDecodeRecords.original_global_key (show j < OutputDecodeRecords.localCount h^J from hj)]
  rfl

theorem label_injective {xs : List ℤ} {h J i i' j j' : ℕ}
    (hi : i < 3*xs.length) (hi' : i' < 3*xs.length)
    (hj : j < LightGuardedWanted.totalKeys h J) (hj' : j' < LightGuardedWanted.totalKeys h J)
    (he : label h J i j hi=label h J i' j' hi') : i=i' ∧ j=j' := by
  have hr : i%xs.length=i'%xs.length := congrArg (fun w => w.1.val) he
  have hq : i/xs.length=i'/xs.length := congrArg (fun w => w.2.1.val) he
  have ho := congrArg (fun w => w.2.2) he
  have hj0 : j < (globalRecords h J).length := by
    rwa [OutputDecodeRecords.globalRecords_length']
  have hj1 : j' < (globalRecords h J).length := by
    rwa [OutputDecodeRecords.globalRecords_length']
  have hget : (globalRecords h J).get ⟨j,hj0⟩=(globalRecords h J).get ⟨j',hj1⟩ := by
    simpa only [label,LightOutputDecodeOriginal.output,List.getD_eq_getElem _ _ hj0,
      List.getD_eq_getElem _ _ hj1,List.get_eq_getElem] using ho
  have hh := congrArg Fin.val ((globalRecords_nodup h J).injective_get hget)
  refine ⟨?_,hh⟩
  have hi0 := Nat.div_add_mod i xs.length
  have hi1 := Nat.div_add_mod i' xs.length
  rw [hq,hr] at hi0
  omega

theorem cells_getD_left (ps : List (ℕ × ℕ)) (k : ℕ) :
    (WantedPairs.cells ps).getD (2*k) 0=((ps.getD k (0,0)).1 : ℤ) := by
  induction ps generalizing k with
  | nil => simp [WantedPairs.cells]
  | cons p ps ih =>
    cases k with
    | zero => rfl
    | succ k => simpa [WantedPairs.cells,Nat.mul_succ,Nat.add_assoc] using ih k

theorem cells_getD_right (ps : List (ℕ × ℕ)) (k : ℕ) :
    (WantedPairs.cells ps).getD (2*k+1) 0=((ps.getD k (0,0)).2 : ℤ) := by
  induction ps generalizing k with
  | nil => simp [WantedPairs.cells]
  | cons p ps ih =>
    cases k with
    | zero => rfl
    | succ k => simpa [WantedPairs.cells,Nat.mul_succ,Nat.add_assoc] using ih k

theorem segment_pair {μ : ℕ → ℤ} {base k : ℕ} {ps : List (ℕ × ℕ)}
    (H : Light.Seg μ base (WantedPairs.cells ps)) (hk : k < ps.length) :
    μ (base+2*k)=((ps.getD k (0,0)).1 : ℤ) ∧
      μ (base+2*k+1)=((ps.getD k (0,0)).2 : ℤ) := by
  have h0 : 2*k < (WantedPairs.cells ps).length := by rw [WantedPairs.cells_length]; omega
  have h1 : 2*k+1 < (WantedPairs.cells ps).length := by rw [WantedPairs.cells_length]; omega
  constructor
  · rw [← cells_getD_left, List.getD_eq_getElem _ _ h0]
    exact H _ h0
  · rw [← cells_getD_right,List.getD_eq_getElem _ _ h1, Nat.add_assoc]
    exact H _ h1

end ThreeSum.WantedRecordOrder
