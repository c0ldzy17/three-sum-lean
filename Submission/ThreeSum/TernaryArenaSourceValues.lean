import Submission.ThreeSum.TernaryArenaSourceCertificate

noncomputable section
namespace ThreeSum.TernaryArenaSourceValues
open Light TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps
open TernaryArenaSourceSetup TernaryNativeCompleteFrontend LightTernarySourceHost
open scoped BigOperators
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
attribute [local instance] Classical.propDecidable

theorem homogeneous (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (weight : ℕ→ℤ) (g : ℕ) :
    ∀ W, (source (r := r) maps cap I right).values
      (TernaryBankCanonical.enumeration (N m r) (cut m r)).word weight g W≠0 →
      TernaryBank.rank W=r*alphaRank m := by
  intro W hW
  have hp : TernarySourceHostModel.physical (source (r := r) maps cap I right).records
      (TernaryBankCanonical.enumeration (N m r) (cut m r)).word
      (source (r := r) maps cap I right).key (source (r := r) maps cap I right).group
      weight g W≠0 := by
    intro he
    apply hW
    simp only [TernarySourceExecutionFactory.Setup.values,he,mul_zero]
  apply TernarySourceHostModel.physical_homogeneous _ _ _ _ _ _ ?_ g W hp
  intro x hx
  exact TernaryArenaSourceCertificate.source_rank maps cap I right x.2
    ((TernarySourceHostModel.mem_records _ _ _ _ _ _).mp hx).2.1

private theorem physical_abs {N : ℕ} (S : TernarySourceExecutionFactory.Setup)
    (E : ℕ→TritWord N) (weight : ℕ→ℤ) (g : ℕ) (W : TritWord N)
    (hw : ∀i<S.NL, |weight i|≤(S.weightU : ℤ)) :
    |TernarySourceHostModel.physical S.records E S.key S.group weight g W|≤
      (S.NL*size S.xs S.J*S.weightU : ℕ) := by
  unfold TernarySourceHostModel.physical TernaryWeightedPhysicalSources.histogram
  calc
    _≤∑x∈TernarySourceHostModel.channel S.records S.group g,
      |if E (S.key x.2)=W then weight x.1 else 0| := Finset.abs_sum_le_sum_abs _ _
    _≤∑ _x∈TernarySourceHostModel.channel S.records S.group g, (S.weightU : ℤ) := by
      apply Finset.sum_le_sum
      intro x hx
      have hm := (TernarySourceHostModel.mem_records _ _ _ _ _ _).mp (Finset.mem_filter.mp hx).1
      split_ifs
      · exact hw x.1 hm.1
      · simp
    _=((TernarySourceHostModel.channel S.records S.group g).card : ℤ)*S.weightU := by simp
    _≤(S.NL*size S.xs S.J*S.weightU : ℕ) := by
      have hc : (TernarySourceHostModel.channel S.records S.group g).card≤S.NL*size S.xs S.J := by
        exact (Finset.card_filter_le _ _).trans ((Finset.card_filter_le _ _).trans_eq (by simp))
      exact_mod_cast Nat.mul_le_mul_right S.weightU hc

theorem bound (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (weight : ℕ→ℤ) (g : ℕ) (W : TritWord (N m r))
    (hw : ∀i<(source (r := r) maps cap I right).NL, |weight i|≤(I.weightCap : ℤ)) :
    |(source (r := r) maps cap I right).values
      (TernaryBankCanonical.enumeration (N m r) (cut m r)).word weight g W|≤
      (valueCap (r := r) maps cap I : ℤ) := by
  let S := source (r := r) maps cap I right
  let E := (TernaryBankCanonical.enumeration (N m r) (cut m r)).word
  have hf : ∀x∈S.records, (S.factor : ℤ)=TernaryConvolution.factorial (E (S.key x.2)) := by
    intro x hx
    exact TernaryArenaSourceCertificate.source_factorial maps cap I right x.2
      ((TernarySourceHostModel.mem_records _ _ _ _ _ _).mp hx).2.1
  change |TernaryConvolution.factorial W*TernarySourceHostModel.physical S.records E S.key S.group weight g W|≤_
  rw [←TernarySourceHostModel.factor_physical S.records E S.key S.group weight S.factor hf g W,
    abs_mul,abs_of_nonneg (Nat.cast_nonneg S.factor)]
  apply le_trans (mul_le_mul_of_nonneg_left (physical_abs S E weight g W hw) (Nat.cast_nonneg S.factor))
  have hn : S.NL*size S.xs S.J≤I.nB*(localRecords maps cap false).length^r+
      I.nC*(localRecords maps cap true).length^r+1 := by
    cases right <;> simp only [S,source,size,List.length_map,Bool.false_eq_true,ite_false,ite_true] <;> omega
  exact_mod_cast (show S.factor*(S.NL*size S.xs S.J*S.weightU)≤valueCap (r := r) maps cap I by
    dsimp [valueCap]
    simpa only [S,source,mul_assoc,mul_left_comm,mul_comm] using
      Nat.mul_le_mul_left (2^(r*fixedAlpha m 2)*I.weightCap) hn)

end ThreeSum.TernaryArenaSourceValues
