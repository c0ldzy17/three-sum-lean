import Submission.ThreeSum.TernaryArenaSourceModel

noncomputable section
namespace ThreeSum.TernaryArenaSourceCertificate
open TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps
open TernaryArenaSourceSetup TernaryCanonicalDictionaries TernaryNativeCompleteFrontend
open LightTernarySourceHost TernaryCodeSemantics
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

theorem sources (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) :
    Sources (setup (r := r) maps τ cap Q I) maps cap := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [setup,source,size]
  · simp [setup,source,size]
  · intro j hj; rfl
  · intro j hj; rfl
  · intro j hj
    exact (congrArg (fun W => (address W : ℤ))
      (TernaryArenaSourceModel.word_spec maps cap I false ⟨j,hj⟩)).trans
      (TernaryCanonicalSourceBank.dictionary_word false maps cap ⟨j,hj⟩).symm
  · intro j hj
    exact (congrArg (fun W => (address W : ℤ))
      (TernaryArenaSourceModel.word_spec maps cap I true ⟨j,hj⟩)).trans
      (TernaryCanonicalSourceBank.dictionary_word true maps cap ⟨j,hj⟩).symm
  · intro j hj
    exact (congrArg (fun n : ℕ => (n : ℤ))
      (TernaryArenaSourceModel.group_spec maps cap I false ⟨j,hj⟩)).trans
      (TernaryCanonicalSourceBank.dictionary_group false maps cap ⟨j,hj⟩).symm
  · intro j hj
    exact (congrArg (fun n : ℕ => (n : ℤ))
      (TernaryArenaSourceModel.group_spec maps cap I true ⟨j,hj⟩)).trans
      (TernaryCanonicalSourceBank.dictionary_group true maps cap ⟨j,hj⟩).symm

theorem source_typed (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (j : ℕ) (hj : j<LightTernarySourceHost.size (source (r := r) maps cap I right).xs r) :
    HasType ((TernaryBankCanonical.enumeration (N m r) (cut m r)).word
      ((source (r := r) maps cap I right).key j)) (fun d => r*fixedAlpha m d) := by
  have hbound : j<(localRecords maps cap right).length^r := by
    simpa only [source,LightTernarySourceHost.size,List.length_map] using hj
  have hword := TernaryArenaSourceModel.word_spec maps cap I right ⟨j,hbound⟩
  exact hword ▸ TernaryCanonicalSourceBank.typed right maps cap ⟨j,hbound⟩

theorem source_factorial (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (j : ℕ) (hj : j<LightTernarySourceHost.size (source (r := r) maps cap I right).xs r) :
    ((source (r := r) maps cap I right).factor : ℤ)=
      TernaryConvolution.factorial ((TernaryBankCanonical.enumeration (N m r) (cut m r)).word
        ((source (r := r) maps cap I right).key j)) := by
  rw [TernaryConvolution.factorial_eq_power_two,source_typed maps cap I right j hj 2]
  rfl

theorem source_rank (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (j : ℕ) (hj : j<LightTernarySourceHost.size (source (r := r) maps cap I right).xs r) :
    TernaryBank.rank ((TernaryBankCanonical.enumeration (N m r) (cut m r)).word
      ((source (r := r) maps cap I right).key j))=r*alphaRank m := by
  rw [TernaryDimensionBounds.rank_eq_counts,source_typed maps cap I right j hj 1,
    source_typed maps cap I right j hj 2]
  unfold alphaRank
  ring

end ThreeSum.TernaryArenaSourceCertificate
