import Submission.ThreeSum.TernaryArenaFrontBounds
import Submission.ThreeSum.TernaryTensorWordResources

noncomputable section
namespace ThreeSum.TernaryArenaTensorBounds
open TernaryArenaPrefixFootprints TernaryArenaSourceSetup TernaryArenaSourceBounds
open TernaryArenaFrontBounds TernaryCoverGoodMaps TernaryLocalParameters
open TernaryNativeCompleteFrontend TernaryNativeMomentBounds
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000

/-- Exact native physical-pair bound; every map occurrence and tuple remains
in the count. The larger power is used solely for word resources. -/
theorem score_bound (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (n U H : ℕ)
    (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hw : I.weightCap≤weight H (4^fixedLength m) U) :
    scoreBound (setup (r := r) maps τ cap Q I)≤
      ((4^fixedLength m)^r)^2*n^2*((sourceWidth maps cap)^r)^2*
        (weight H (4^fixedLength m) U)^2 := by
  have hL := Nat.pow_le_pow_left (local_le maps cap false) r
  have hR := Nat.pow_le_pow_left (local_le maps cap true) r
  have hQ : 1≤(4^fixedLength m)^r := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ (by decide : 1≤4))
  have h2 : 2^(N m r)≤((4^fixedLength m)^r)^2 := by
    have hp := Nat.pow_le_pow_left (by decide : 2≤4) (N m r)
    have he : 4^(N m r)=(4^fixedLength m)^r := by unfold N; rw [Nat.mul_comm,pow_mul]
    rw [he] at hp
    exact hp.trans (by nlinarith)
  have hpair : pairBound (setup (r := r) maps τ cap Q I)≤
      (n*(sourceWidth maps cap)^r)*(n*(sourceWidth maps cap)^r) := by
    dsimp [pairBound,setup,source,LightTernarySourceHost.size]
    simp only [List.length_map]
    exact Nat.mul_le_mul (Nat.mul_le_mul hnB hL) (Nat.mul_le_mul hnC hR)
  unfold scoreBound
  calc
    _≤((n*(sourceWidth maps cap)^r)*(n*(sourceWidth maps cap)^r))*
        (((4^fixedLength m)^r)^2)*weight H (4^fixedLength m) U*weight H (4^fixedLength m) U :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hpair h2) hw) hw
    _=_ := by ring

theorem word_mono {K J count count' V V' U U' : ℕ}
    (hc : count≤count') (hv : V≤V') (hu : U≤U') :
    TernaryTensorWordResources.word K J count V U≤
      TernaryTensorWordResources.word K J count' V' U' := by
  unfold TernaryTensorWordResources.word TernaryTensorWordResources.potentialWord
    TernaryTensorWordResources.polynomialBound
  gcongr

theorem word_bound (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (n U tagBound : ℕ)
    (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightTernaryDimensions.J M b n U))
    (hweight : I.weightCap≤weight H (4^fixedLength m) U)
    (htag : tagBound≤2*(4^fixedLength m)+1) :
    TernaryTensorWordResources.word K (LightTernaryDimensions.J M b n U)
      (entries (r := r) maps τ I).length (scoreBound (setup (r := r) maps τ cap Q I)) tagBound≤
      (numbers maps τ cap M b K H drift scale n U r).potentialWord+
        (numbers maps τ cap M b K H drift scale n U r).tensorWord := by
  have hc := wanted_count (r := r) maps τ I M b n U hO
  have hv := score_bound (r := r) maps τ cap Q I n U H hnB hnC hweight
  have h := word_mono (K := K) (J := LightTernaryDimensions.J M b n U) hc hv htag
  apply h.trans
  unfold TernaryTensorWordResources.word TernaryTensorWordResources.potentialWord
    TernaryTensorWordResources.polynomialBound LightWeightRow.word
  dsimp only [numbers]
  have hRcast : (0 : ℤ)≤(((4^fixedLength m : ℕ) : ℤ)) := by positivity
  simp only [Nat.add_assoc]
  norm_num only
  omega


theorem tensor_words_le_total (maps : Fin F→Weight m p) (τ cap M b K H drift scale n U j : ℕ) :
    (numbers maps τ cap M b K H drift scale n U j).potentialWord+
      (numbers maps τ cap M b K H drift scale n U j).tensorWord≤
      total maps τ cap M b K H drift scale n U j := by
  unfold total
  generalize numbers maps τ cap M b K H drift scale n U j=A
  change A.potentialWord+A.tensorWord≤A.list.sum
  rw [Numbers.sum_list]
  omega

theorem spatial (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (I : Input) (n U : ℕ)
    (hO : I.requesterCount≤n*2^(LightTernaryDimensions.J M b n U))
    (HC : Fits I.capacity (numbers maps τ cap M b K H drift scale n U r)) :
    106≤I.capacity ∧ 4≤I.capacity ∧ 5≤I.capacity ∧
    TernaryPairedColumnEnumeration.width K+1≤I.capacity ∧
    (entries (r := r) maps τ I).length*(LightTernaryDimensions.J M b n U+2)^4≤I.capacity := by
  have hlocal := HC.localSize
  have htensor := HC.tensorCells
  have hc := wanted_count (r := r) maps τ I M b n U hO
  have hcell := Nat.mul_le_mul_right ((LightTernaryDimensions.J M b n U+2)^4) hc
  dsimp only [numbers] at hlocal htensor
  repeat' apply And.intro
  all_goals omega

end ThreeSum.TernaryArenaTensorBounds
