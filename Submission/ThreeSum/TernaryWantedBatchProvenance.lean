import Submission.ThreeSum.TernaryWantedBatchIndex
import Mathlib.Data.List.NodupEquivFin

/-! Emission positions retain target occurrence IDs, even if distinct targets
have the same original requester position and produce identical query words. -/
noncomputable section
namespace ThreeSum.TernaryWantedBatchProvenance
open TernaryWantedRadix TernaryWantedLittleEndian

abbrev Descriptor := ℕ×List ℕ

def descriptors (P J : ℕ) (raws : List ℤ) (targets : ℕ→ℤ) : ℕ→List Descriptor
  | 0 => []
  | n+1 => descriptors P J raws targets n ++
      (wantedOutputs (P : ℤ) raws J (targets n)).map (fun xs => (n,xs))

def emit (R S : ℕ) (words maps : List ℕ) (positions : ℕ→ℕ) (d : Descriptor) :
    TernaryWantedBatchIndex.Entry :=
  (positions d.1,encode words R 0 1 d.2,encode maps S 0 1 d.2)

theorem mapped_entries (P R S J : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ→ℤ) (positions : ℕ→ℕ) (n : ℕ) :
    (descriptors P J raws targets n).map (emit R S words maps positions)=
      TernaryWantedBatchIndex.entries P R S J raws words maps targets positions n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [descriptors,List.map_append,List.map_map,ih,TernaryWantedBatchIndex.entries,
      TernaryWantedLittleEndian.wantedCodes,List.map_map,Function.comp_def,emit]

theorem mem_descriptors (P J : ℕ) (raws : List ℤ) (targets : ℕ→ℤ) (n : ℕ)
    (d : Descriptor) : d∈descriptors P J raws targets n ↔
      d.1<n ∧ d.2∈wantedOutputs (P : ℤ) raws J (targets d.1) := by
  induction n with
  | zero => simp [descriptors]
  | succ n ih =>
    rw [descriptors,List.mem_append,ih]
    constructor
    · rintro (⟨ht,hs⟩|hm)
      · exact ⟨by omega,hs⟩
      · obtain ⟨xs,hxs,he⟩ := List.mem_map.mp hm
        subst d
        exact ⟨by omega,hxs⟩
    · rintro ⟨ht,hs⟩
      by_cases hn : d.1<n
      · exact Or.inl ⟨hn,hs⟩
      · have he : d.1=n := by omega
        exact Or.inr (List.mem_map.mpr ⟨d.2,by simpa only [he] using hs,by ext <;> simp [he]⟩)

theorem descriptors_nodup (P J : ℕ) (raws : List ℤ) (targets : ℕ→ℤ) (n : ℕ) :
    (descriptors P J raws targets n).Nodup := by
  induction n with
  | zero => simp [descriptors]
  | succ n ih =>
    rw [descriptors,List.nodup_append]
    refine ⟨ih,(wantedOutputs_nodup _ _ _ _).map (fun x y h => (Prod.mk.inj h).2),?_⟩
    intro d hd e he hde
    subst e
    have ht := ((mem_descriptors P J raws targets n d).mp hd).1
    obtain ⟨xs,hxs,hx⟩ := List.mem_map.mp he
    have hh := congrArg Prod.fst hx
    omega

/-- An actual output ordinal decodes to its unique target/carry occurrence
and unique local output-record sequence. Equal emitted triples are harmless. -/
def decode (P R S J : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ→ℤ) (positions : ℕ→ℕ) (n : ℕ)
    (j : Fin (TernaryWantedBatchIndex.entries P R S J raws words maps targets positions n).length) :
    Descriptor :=
  (descriptors P J raws targets n).get ⟨j.val,by
    have hh := congrArg List.length (mapped_entries P R S J raws words maps targets positions n)
    simpa only [List.length_map] using j.isLt.trans_eq hh.symm⟩

theorem decode_mem (P R S J : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ→ℤ) (positions : ℕ→ℕ) (n : ℕ) (j) :
    decode P R S J raws words maps targets positions n j∈descriptors P J raws targets n :=
  List.get_mem _ _

theorem decode_injective (P R S J : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ→ℤ) (positions : ℕ→ℕ) (n : ℕ) :
    Function.Injective (decode P R S J raws words maps targets positions n) := by
  intro i j he
  apply Fin.ext
  exact congrArg (fun t : Fin (descriptors P J raws targets n).length => t.val)
    ((descriptors_nodup P J raws targets n).injective_get he)

theorem emit_decode (P R S J : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ→ℤ) (positions : ℕ→ℕ) (n : ℕ) (j) :
    emit R S words maps positions (decode P R S J raws words maps targets positions n j)=
      TernaryWantedBatchIndex.get
        (TernaryWantedBatchIndex.entries P R S J raws words maps targets positions n) j.val := by
  have hh := congrArg (fun xs => xs[j.val]?)
    (mapped_entries P R S J raws words maps targets positions n)
  rw [List.getElem?_map,List.getElem?_eq_getElem (show j.val<(descriptors P J raws targets n).length from by
    have hl := congrArg List.length (mapped_entries P R S J raws words maps targets positions n)
    simpa only [List.length_map] using j.isLt.trans_eq hl.symm),
    List.getElem?_eq_getElem j.isLt] at hh
  simp only [Option.map_some] at hh
  simpa only [decode,List.get_eq_getElem,TernaryWantedBatchIndex.get,
    List.getD_eq_getElem _ _ j.isLt] using Option.some.inj hh

end ThreeSum.TernaryWantedBatchProvenance
