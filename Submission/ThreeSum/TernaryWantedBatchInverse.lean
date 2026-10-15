import Submission.ThreeSum.TernaryWantedBatchProvenance

noncomputable section
namespace ThreeSum.TernaryWantedBatchInverse
open TernaryWantedBatchProvenance

theorem exists_decode (P R S J : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ→ℤ) (positions : ℕ→ℕ) (n : ℕ) (d : Descriptor)
    (hd : d∈descriptors P J raws targets n) :
    ∃ j : Fin (TernaryWantedBatchIndex.entries P R S J raws words maps targets positions n).length,
      decode P R S J raws words maps targets positions n j=d := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hd
  have hl := congrArg List.length (mapped_entries P R S J raws words maps targets positions n)
  simp only [List.length_map] at hl
  refine ⟨⟨i.val,by simpa only [←hl] using i.isLt⟩,?_⟩
  exact hi

end ThreeSum.TernaryWantedBatchInverse
