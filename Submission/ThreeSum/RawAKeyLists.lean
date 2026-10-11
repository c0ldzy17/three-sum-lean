import Submission.ThreeSum.GlobalKeyOffset
import Submission.ThreeSum.LocalKeyArraySemantics

/-!
# Original A positions and all three guarded lifts

The physical key order is lift-major, preserving every original position.
The selected-offset count is transported to the unchanged guarded wanted
labels used by raw reporting, including repeated input values.
-/

namespace ThreeSum.RawAKeyLists

open GlobalEncoding RawIncidences GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open scoped BigOperators

set_option maxHeartbeats 900000

abbrev Record (xs : List ℤ) := Fin 3 × Fin xs.length

def records (xs : List ℤ) : List (Record xs) :=
  (List.finRange 3).product (List.finRange xs.length)

def key (P : ℤ) (xs : List ℤ) (r : Record xs) : ℤ :=
  xs.getD r.2.val 0 % P+lift r.1*P

def keys (P : ℤ) (xs : List ℤ) : List ℤ := (records xs).map (key P xs)

theorem records_length (xs : List ℤ) : (records xs).length=3*xs.length := by
  calc
    _ = (List.finRange 3).length*(List.finRange xs.length).length := List.length_product _ _
    _ = _ := by rw [List.length_finRange,List.length_finRange]

theorem records_nodup (xs : List ℤ) : (records xs).Nodup :=
  (List.nodup_finRange 3).product (List.nodup_finRange xs.length)

theorem mem_records (xs : List ℤ) (r : Record xs) : r ∈ records xs := by
  exact List.mem_product.mpr ⟨List.mem_finRange _,List.mem_finRange _⟩

theorem keys_length (P : ℤ) (xs : List ℤ) : (keys P xs).length=3*xs.length := by
  rw [keys,List.length_map,records_length]

theorem keys_length_records (P : ℤ) (xs : List ℤ) :
    (keys P xs).length=(records xs).length := List.length_map ..

noncomputable def recordEquiv (xs : List ℤ) : Fin (records xs).length ≃ Record xs :=
  Equiv.ofBijective (records xs).get
    ⟨(records_nodup xs).injective_get,fun r => List.mem_iff_get.mp (mem_records xs r)⟩

theorem key_getD_record (P : ℤ) (xs : List ℤ) (i : Fin (records xs).length) :
    (keys P xs).getD i.val 0=key P xs (recordEquiv xs i) := by
  rw [keys,List.getD_eq_getElem _ _ (by simpa only [List.length_map] using i.isLt),
    List.getElem_map]
  rfl

theorem keys_eq_liftRows (P : ℤ) (xs : List ℤ) :
    keys P xs=(List.finRange 3).flatMap
      (fun j => xs.map (fun x => x%P+lift j*P)) := by
  unfold keys records
  simp only [List.product,List.map_flatMap,List.map_map,Function.comp_def]
  congr 1
  funext j
  calc
    _ = ((List.finRange xs.length).map xs.get).map (fun x => x%P+lift j*P) := by
      rw [List.map_map]
      congr 1
      funext i
      simp only [key,List.getD_eq_getElem _ _ i.isLt,List.get_eq_getElem,Function.comp_def]
    _ = _ := by rw [List.map_get_finRange]

theorem key_bounded {P : ℤ} (hP : 0 < P) (xs : List ℤ) (r : Record xs) :
    |key P xs r| ≤ 2*P := by
  have hn := Int.emod_nonneg (xs.getD r.2.val 0) hP.ne'
  have hu := Int.emod_lt_of_pos (xs.getD r.2.val 0) hP
  have hl : -1 ≤ lift r.1 ∧ lift r.1 ≤ 1 := by
    rcases lift_small r.1 with hh | hh | hh <;> rw [hh] <;> norm_num
  unfold key
  apply abs_le.mpr
  constructor <;> nlinarith

theorem keys_bounded {P : ℤ} (hP : 0 < P) (xs : List ℤ) :
    ∀ x ∈ keys P xs, |x| ≤ 2*P := by
  intro x hx
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hx
  exact key_bounded hP xs r

theorem sum_keys_eq (P : ℤ) (xs : List ℤ) (f : ℤ → ℕ) :
    (∑ i : Fin (keys P xs).length, f ((keys P xs).getD i.val 0))=
      ∑ i : Fin xs.length, ∑ j : Fin 3, f (xs.getD i.val 0%P+lift j*P) := by
  rw [keys_length_records]
  calc
    _ = ∑ r : Record xs, f (key P xs r) := by
      apply Fintype.sum_equiv (recordEquiv xs)
      intro i
      rw [key_getD_record]
    _ = _ := by rw [Fintype.sum_prod_type,Finset.sum_comm]; rfl

def guardedCount (M : ℕ) (P : ℤ) (xs : List ℤ) (h J : ℕ) (d : ℤ) : ℕ :=
  ∑ i : Fin xs.length, ∑ j : Fin 3, ∑ q : GlobalOutput h J,
    if (M : ℤ) ∣ xs.getD i.val 0%P+lift j*P+d-globalKey q then 1 else 0

theorem wantedCount_eq_guardedCount (M : ℕ) (P : ℤ) (xs : List ℤ) (h J : ℕ) (d : ℤ) :
    GlobalKeyOffset.wantedCount M (keys P xs) h J d=guardedCount M P xs h J d := by
  rw [GlobalKeyOffset.wantedCount_eq_divisibility]
  simpa only [guardedCount] using sum_keys_eq P xs
    (fun x => ∑ q : GlobalOutput h J, if (M : ℤ) ∣ x+d-globalKey q then 1 else 0)

def selected (M : ℕ) [NeZero M] (P : ℤ) (xs : List ℤ) (h J : ℕ) : ℕ :=
  GlobalKeyOffset.selected M (keys P xs) h J

theorem selected_lt (M : ℕ) [NeZero M] (P : ℤ) (xs : List ℤ) (h J : ℕ) :
    selected M P xs h J < M := GlobalKeyOffset.selected_lt ..

theorem selected_guarded_bound (M : ℕ) [NeZero M] (P : ℤ) (xs : List ℤ) (h J : ℕ) :
    M*guardedCount M P xs h J (selected M P xs h J) ≤
      3*xs.length*(scheduleSize h^J*LocalCoverBounds.outputCount (512*h) h^J) := by
  have hh := GlobalKeyOffset.selected_wanted_bound M (keys P xs) h J
  simpa only [wantedCount_eq_guardedCount,keys_length,selected] using hh

def wanted (M : ℕ) (P : ℤ) (xs : List ℤ) (h J : ℕ) (d : ℤ) :
    Finset (RawReporting.Wanted h J (Fin xs.length)) :=
  Finset.univ.filter fun w =>
    (M : ℤ) ∣ xs.getD w.1.val 0%P+lift w.2.1*P+d-globalKey w.2.2

theorem mem_wanted {M h J : ℕ} {P d : ℤ} {xs : List ℤ}
    {w : RawReporting.Wanted h J (Fin xs.length)} :
    w ∈ wanted M P xs h J d ↔
      (M : ℤ) ∣ xs.getD w.1.val 0%P+lift w.2.1*P+d-globalKey w.2.2 := by
  simp only [wanted,Finset.mem_filter,Finset.mem_univ,true_and]

theorem wanted_card (M : ℕ) (P : ℤ) (xs : List ℤ) (h J : ℕ) (d : ℤ) :
    (wanted M P xs h J d).card=guardedCount M P xs h J d := by
  rw [wanted,Finset.card_eq_sum_ones,Finset.sum_filter,Fintype.sum_prod_type]
  unfold guardedCount
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_prod_type]

theorem raw_wanted_mem {h J : ℕ} {P d : ℤ} {xs : List ℤ}
    {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {T : Finset (Original (Fin xs.length) β γ)} {b : β → ℤ} {c : γ → ℤ}
    {r : RawItem h J (Fin xs.length) β γ}
    (hr : r ∈ rawOn h J P d T (fun i => xs.getD i.val 0) b c) :
    RawReporting.wantedOf r ∈ wanted (localPrime h^J) P xs h J d := by
  apply mem_wanted.mpr
  have hh := (mem_witnesses.mp (mem_rawOn.mp hr).2).2
  simpa only [globalModulus,Nat.cast_pow,RawReporting.wantedOf,tupleKey] using hh

end ThreeSum.RawAKeyLists
