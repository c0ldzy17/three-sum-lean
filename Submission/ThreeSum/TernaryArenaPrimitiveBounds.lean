import Submission.ThreeSum.TernaryArenaSourceBounds
import Submission.ThreeSum.TernaryArenaSeedPrimitiveGuards

noncomputable section
namespace ThreeSum.TernaryArenaPrimitiveBounds
open TernaryArenaPrefixFootprints TernaryArenaSourceSetup TernaryArenaSourceBounds
open TernaryCoverGoodMaps TernaryLocalParameters TernaryNativeCompleteFrontend
open TernaryArenaSeedCandidate LightTernarySeedScoreFactory
set_option maxHeartbeats 6000000
variable {p m F r : ℕ} [Fact p.Prime]

theorem append_mono {len p b power power' : ℕ} (hb : b≤p) (hp : power≤power') :
    LightTernaryAppendKeys.word len p b power≤LightTernaryAppendKeys.word len p p power' := by
  unfold LightTernaryAppendKeys.word LightSignedRowHash.word
  gcongr

theorem word_bound (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (I : Input) (A : Inputs) (seed positionCap n U : ℕ)
    (D : Data (config p r I A seed))
    (hJ : A.J=LightTernaryDimensions.J M b n U)
    (hnB : I.nB≤n) (hnC : I.nC≤n) (hpos : positionCap≤n)
    (hB : D.bB<p) (hC : D.bC<p) (hO : D.bO<p) :
    TernaryArenaSeedPrimitiveGuards.word maps τ I A seed positionCap D≤
      (numbers maps τ cap M b K H drift scale n U r).sourceWord := by
  have hpp : p^(r-1)≤p^r := Nat.pow_le_pow_right (Fact.out : p.Prime).one_lt.le (by omega)
  have hwB := append_mono (len := A.J+2) hB.le hpp
  have hwC := append_mono (len := A.J+2) hC.le hpp
  have hwO := append_mono (len := A.J+2) hO.le hpp
  have hnBB := Nat.mul_le_mul hnB hnB
  have hnCC := Nat.mul_le_mul hnC hnC
  have hmod := Nat.mul_le_mul_right p hpp
  have hraw : (TernaryGoodOutputCatalog.raws maps τ).length≤wantedWidth maps τ := by
    unfold wantedWidth; omega
  unfold TernaryArenaSeedPrimitiveGuards.word TernaryArenaSeedPrimitiveGuards.rawCap
  rw [hJ] at hwB hwC hwO ⊢
  dsimp only [numbers]
  have ha : 0≤LightTernaryAppendKeys.word (LightTernaryDimensions.J M b n U+2) p p (p^r) := Nat.zero_le _
  have hRcast : (0 : ℤ)≤(((4^fixedLength m : ℕ) : ℤ)) := by positivity
  omega


theorem spatial (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (I : Input) (A : Inputs) (n U : ℕ)
    (hJ : A.J=LightTernaryDimensions.J M b n U)
    (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightTernaryDimensions.J M b n U))
    (HC : Fits I.capacity (numbers maps τ cap M b K H drift scale n U r)) :
    I.nB≤I.capacity ∧ I.nC≤I.capacity ∧ I.requesterCount≤I.capacity ∧
    A.J+2≤I.capacity ∧ A.J*p^(r-1)≤I.capacity ∧ p^(r-1)*p≤I.capacity ∧
    3*I.requesterCount*(F*TernaryGoodOutputCatalog.cap m p τ)^r≤I.capacity ∧
    Nat.log 2 (2*TernaryArenaSeedPrimitiveGuards.rawCap m p r+1)+2≤I.capacity := by
  have hdepth := HC.depth
  have hsource := HC.sourceWord
  have hspan := HC.spanCells
  have htensor := HC.tensorCells
  have hmatrix := HC.originalMatrixCells
  have hpp : p^(r-1)≤p^r := Nat.pow_le_pow_right (Fact.out : p.Prime).one_lt.le (by omega)
  have hmod := Nat.mul_le_mul_right p hpp
  have hsp := Nat.mul_le_mul_left A.J hpp
  have hwant : F*TernaryGoodOutputCatalog.cap m p τ≤wantedWidth maps τ := by
    unfold wantedWidth; omega
  have hwpow := Nat.pow_le_pow_left hwant r
  have hcount := Nat.mul_le_mul hO hwpow
  have hΛ : 3≤(LightTernaryDimensions.J M b n U+2)^4 := by
    have hh := Nat.pow_le_pow_left (show 2≤LightTernaryDimensions.J M b n U+2 by omega) 4
    norm_num at hh
    omega
  have hfull := Nat.mul_le_mul hcount hΛ
  have htargets : I.requesterCount≤n*2^(LightTernaryDimensions.J M b n U)*
      (LightTernaryDimensions.J M b n U+2) := hO.trans
    (Nat.le_mul_of_pos_right _ (by omega))
  have hlog := Nat.log_le_self 2 (2*(p*(p+1)^r)+1)
  have hRcast : (0 : ℤ)≤(((4^fixedLength m : ℕ) : ℤ)) := by positivity
  dsimp only [numbers] at hdepth hsource hspan htensor hmatrix
  rw [hJ] at hsp ⊢
  have hspComm := hsp.trans_eq (Nat.mul_comm _ _)
  unfold TernaryArenaSeedPrimitiveGuards.rawCap
  have hfull' : 3*I.requesterCount*(F*TernaryGoodOutputCatalog.cap m p τ)^r≤
      n*2^(LightTernaryDimensions.J M b n U)*(wantedWidth maps τ)^r*
        (LightTernaryDimensions.J M b n U+2)^4 := by nlinarith only [hfull]
  repeat' apply And.intro
  all_goals omega

end ThreeSum.TernaryArenaPrimitiveBounds
