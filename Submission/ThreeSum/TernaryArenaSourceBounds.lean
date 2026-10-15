import Submission.ThreeSum.TernaryArenaPrefixFootprints

noncomputable section
namespace ThreeSum.TernaryArenaSourceBounds
open TernaryArenaPrefixFootprints TernaryArenaSourceSetup
open TernaryCoverGoodMaps TernaryLocalParameters LightTernarySourceHost TernaryNativeCompleteFrontend
set_option maxHeartbeats 6000000

/-- The literal join can retain every original-position/dictionary-tuple
pair. This bound retains all repeated physical representations. -/
theorem total_le (M NL NR : ℕ) (left right : ℕ→ℤ) :
    WantedResidueKeys.total M left right NL NR 0≤NL*NR := by
  unfold WantedResidueKeys.total WantedPairs.count
  calc
    _≤∑ _i∈Finset.range NL, NR := by
      apply Finset.sum_le_sum
      intro i hi
      exact LightHistogram.count_le _ _ _
    _=NL*NR := by simp

theorem radix_space_le {m W : ℕ} (hm : m≤W) (hW : 1≤W) (j : ℕ) :
    LightRadixKeys.space 0 m j≤(j+1)*(W^j+1) := by
  have hoff (i : ℕ) (hi : i≤j) : LightRadixKeys.offset m i ≤ i *(W^j+1) := by
    induction i with
    | zero => simp [LightRadixKeys.offset]
    | succ i ih =>
      have h1:=ih (by omega)
      have h2: m^i≤W^j := (Nat.pow_le_pow_left hm _).trans (Nat.pow_le_pow_right hW (by omega))
      rw [LightRadixKeys.offset]
      nlinarith
  have hh:=hoff j le_rfl
  have hp:=Nat.pow_le_pow_left hm j
  unfold LightRadixKeys.space
  nlinarith

theorem join_space_le {M NL NR U n W j : ℕ} (left right : ℕ→ℤ)
    (hl : NL≤n) (hr : NR≤W^j) :
    LightWantedSetup.space 0 M left right NL NR U 0 0≤
      10+n+2*W^j+4*M+U+2*n*W^j := by
  have ht:=total_le M NL NR left right
  have hb : NL*NR≤n*W^j := Nat.mul_le_mul hl hr
  have hu:=Nat.log_le_self 2 (U+1)
  have hp:=Nat.log_le_self 2 (M+1)
  have hmax : max (Nat.log 2 (U+1)+2) (Nat.log 2 (M+0+1)+2)≤U+M+3 := by
    simp only [Nat.add_zero]
    apply max_le <;> omega
  unfold LightWantedSetup.space
  apply max_le
  · unfold LightSourceResidues.space LightWantedSetup.pairBase LightWantedSetup.bucketBase
      LightWantedSetup.rightCodes LightWantedSetup.leftCodes LightSourceBucketSetup.next
    nlinarith
  · unfold LightWantedSetup.pairBase LightWantedSetup.bucketBase
      LightWantedSetup.rightCodes LightWantedSetup.leftCodes LightSourceBucketSetup.next
    nlinarith


variable {p m F r : ℕ} [Fact p.Prime]

theorem local_le (maps : Fin F→Weight m p) (cap : ℕ) (right : Bool) :
    (localRecords maps cap right).length≤sourceWidth maps cap := by
  cases right <;> unfold sourceWidth <;> omega

theorem source_space (maps : Fin F→Weight m p) (cap : ℕ) (I : Input)
    (right : Bool) (n : ℕ) (hnB : I.nB≤n) (hnC : I.nC≤n) :
    LightRadixKeys.space 0 (source (r := r) maps cap I right).xs.length r≤
      (r+1)*((sourceWidth maps cap)^r+1) ∧
    count (source (r := r) maps cap I right).xs p r (p^r)
      (source (r := r) maps cap I right).NL (source (r := r) maps cap I right).input≤
        n*(sourceWidth maps cap)^r ∧
    LightWantedSetup.space 0 (p^r) (source (r := r) maps cap I right).input
      (dictionary (source (r := r) maps cap I right).xs p r)
      (source (r := r) maps cap I right).NL
      (size (source (r := r) maps cap I right).xs r) (p*(p+1)^r) 0 0≤
        10+n+2*(sourceWidth maps cap)^r+4*p^r+p*(p+1)^r+2*n*(sourceWidth maps cap)^r := by
  have hn : (source (r := r) maps cap I right).NL≤n := by
    cases right
    · simpa [source] using hnB
    · simpa [source] using hnC
  have hlocal : (source (r := r) maps cap I right).xs.length≤sourceWidth maps cap := by
    simpa [source] using local_le maps cap right
  have hW : 1≤sourceWidth maps cap := by unfold sourceWidth; omega
  have hsize : size (source (r := r) maps cap I right).xs r≤(sourceWidth maps cap)^r :=
    Nat.pow_le_pow_left hlocal r
  refine ⟨radix_space_le hlocal hW r,?_,?_⟩
  · exact (total_le (p^r) _ _ _ _).trans (Nat.mul_le_mul hn hsize)
  · exact join_space_le _ _ hn hsize

end ThreeSum.TernaryArenaSourceBounds

namespace ThreeSum.TernaryArenaSourceBounds
open TernaryArenaPrefixFootprints TernaryArenaSourceSetup
open TernaryCoverGoodMaps TernaryLocalParameters LightTernarySourceHost TernaryNativeCompleteFrontend
variable {p m F r : ℕ} [Fact p.Prime]

theorem radix_word (P j : ℕ) :
    LightRadixKeys.word P P j=P+P*P*(P+1)^j+P+1 := by
  unfold LightRadixKeys.word LightRadixRows.word
  ring

/-- Every scalar source-host word requirement is bounded by the one
concrete source-word footprint. -/
theorem source_words (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (I : Input) (right : Bool) (n U : ℕ)
    (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hweight : I.weightCap≤weight H (4^fixedLength m) U)
    (hbank : nb m r≤(4^fixedLength m)^r) :
    let S := source (r := r) maps cap I right
    let A := numbers maps τ cap M b K H drift scale n U r
    LightRadixKeys.word S.p0 S.U0 r≤A.sourceWord ∧
    LightRadixKeys.word S.p1 S.U1 r≤A.sourceWord ∧
    LightRadixKeys.word S.p2 S.U2 r≤A.sourceWord ∧
    LightSourceResidues.word S.M S.M S.U 0≤A.sourceWord ∧
    S.bank+2^(S.W+1)+16≤A.sourceWord ∧
    S.groups*S.bank+1≤A.sourceWord ∧ S.factor≤A.sourceWord ∧
    S.factor*(count S.xs p r (p^r) S.NL S.input*I.weightCap)≤A.sourceWord ∧
    (count S.xs p r (p^r) S.NL S.input+1)*I.weightCap≤A.sourceWord := by
  have hspace := source_space (r := r) maps cap I right n hnB hnC
  have hhit := hspace.2.1
  have hf : 2^(r*fixedAlpha m 2)=(2^fixedAlpha m 2)^r := by
    rw [←pow_mul,Nat.mul_comm]
  have hpow : 2^(2*(r*fixedLength m)+1)=2*(4^fixedLength m)^r := by
    rw [pow_succ,show 2*(r*fixedLength m)=2*fixedLength m*r by ring,pow_mul]
    norm_num [pow_mul,mul_comm]
  have hhist : F^r*nb m r+1≤F^r*((4^fixedLength m)^r)+1 := by gcongr
  have hweighted := Nat.mul_le_mul (Nat.le_refl ((2^fixedAlpha m 2)^r))
    (Nat.mul_le_mul hhit hweight)
  have hhistweight := Nat.mul_le_mul (Nat.add_le_add_right hhit 1) hweight
  dsimp only
  dsimp [source] at hhit hweighted hhistweight ⊢
  simp only [radix_word,hf,hpow]
  dsimp [numbers]
  unfold LightSourceResidues.word
  have hpow0 : 2^(2*(r*fixedLength m))=(4^fixedLength m)^r := by
    rw [show 2*(r*fixedLength m)=(2*fixedLength m)*r by ring,pow_mul]
    norm_num [pow_mul]
  have hpowN : 2^(2*N m r)=(4^fixedLength m)^r := by simpa only [N] using hpow0
  simp only [hpowN,hpow0,Nat.mul_assoc] at hweighted ⊢
  clear hspace hhit hnB hnC hweight hpow hf
  have hpZ : (0 : ℤ)≤(p : ℤ) := by positivity
  have hRZ : (0 : ℤ)≤(4 : ℤ)^fixedLength m := by positivity
  have hRcast : (0 : ℤ)≤(((4^fixedLength m : ℕ) : ℤ)) := by positivity
  have hRbase : (0 : ℤ)≤((4 : ℕ) : ℤ)^fixedLength m := by positivity
  have hFZ : (0 : ℤ)≤(F : ℤ) := by positivity
  repeat' apply And.intro
  all_goals omega


theorem bank_size (m j : ℕ) : nb m j≤(4^fixedLength m)^j := by
  have hsub : (bankCodes m j).toFinset⊆Finset.range (4^(N m j)) := by
    intro x hx
    exact Finset.mem_range.mpr (TernaryAddresses.mem_codes_lt (List.mem_toFinset.mp hx))
  have hn := TernaryAddresses.codes_nodup (N m j) (cut m j)
  have hh := Finset.card_le_card hsub
  change (TernaryAddresses.codes (N m j) (cut m j)).toFinset.card≤_ at hh
  rw [List.toFinset_card_of_nodup hn,Finset.card_range] at hh
  simpa [nb,bankCodes,N,←pow_mul,Nat.mul_comm j] using hh

theorem value_cap (maps : Fin F→Weight m p) (cap : ℕ) (I : Input)
    (n U H : ℕ) (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hweight : I.weightCap≤weight H (4^fixedLength m) U) :
    valueCap (r := r) maps cap I≤(2^fixedAlpha m 2)^r*
      weight H (4^fixedLength m) U*(2*n*(sourceWidth maps cap)^r+1) := by
  have hl:=Nat.pow_le_pow_left (local_le maps cap false) r
  have hr:=Nat.pow_le_pow_left (local_le maps cap true) r
  have hsum : I.nB*(localRecords maps cap false).length^r+
      I.nC*(localRecords maps cap true).length^r+1≤2*n*(sourceWidth maps cap)^r+1 := by
    nlinarith [Nat.mul_le_mul hnB hl,Nat.mul_le_mul hnC hr]
  unfold valueCap
  rw [show 2^(r*fixedAlpha m 2)=(2^fixedAlpha m 2)^r by rw [←pow_mul,Nat.mul_comm]]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hweight) hsum

end ThreeSum.TernaryArenaSourceBounds
