import Submission.ThreeSum.TernaryArenaFrontBounds
import Submission.ThreeSum.TernaryArenaArgumentBudget
import Submission.ThreeSum.TernaryArenaAllocationResources

noncomputable section
namespace ThreeSum.TernaryArenaFinalBounds
open Light TernaryArenaLayout TernaryArenaSourceSetup TernaryArenaPrefixFootprints
open TernaryCoverGoodMaps TernaryLocalParameters
set_option maxHeartbeats 8000000
variable {p m F r : ℕ} [Fact p.Prime]

theorem words (maps : Fin F→Weight m p) (τ cap M b K H drift scale n U : ℕ) :
    (TernaryMomentDetectorResources.need (TernaryArenaPairMass.envelope maps cap M n) U H).word≤
      (numbers maps τ cap M b K H drift scale n U r).reporterWord ∧
    (TernaryMomentChannelResources.need (TernaryArenaPairMass.envelope maps cap M n) U (2*H)).word≤
      (numbers maps τ cap M b K H drift scale n U r).reporterWord := by
  have hd := (TernaryMomentDetectorResources.need_bound (TernaryArenaPairMass.envelope maps cap M n) U H).1
  dsimp only [numbers]
  generalize TernaryMomentDetectorResources.coefficient (TernaryArenaPairMass.envelope maps cap M n) H*
      (U+1)^TernaryMomentDetectorResources.degree H=dw at hd ⊢
  generalize (TernaryMomentChannelResources.need (TernaryArenaPairMass.envelope maps cap M n) U (2*H)).word=cw
  generalize 2^(2*(fixedLength m*r)+1)=pw
  omega

theorem cells (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (I : Input) (n U : ℕ)
    (hO : I.requesterCount≤n*2^(LightTernaryDimensions.J M b n U)) :
    (2*H+1)*(entries (r := r) maps τ I).length≤
      (numbers maps τ cap M b K H drift scale n U r).reporterCells ∧
    2*H+1≤(numbers maps τ cap M b K H drift scale n U r).reporterCells ∧
    4*n+2≤(numbers maps τ cap M b K H drift scale n U r).reporterCells ∧
    (entries (r := r) maps τ I).length≤
      (numbers maps τ cap M b K H drift scale n U r).reporterCells := by
  have hc := TernaryArenaFrontBounds.wanted_count (r := r) maps τ I M b n U hO
  have hm := Nat.mul_le_mul_left (2*H+1) hc
  dsimp only [numbers]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · omega
  · omega

theorem baseWord (maps : Fin F→Weight m p) (τ cap M b K H drift scale n U : ℕ) :
    TernaryArenaSourceControlBudget.baseWord m p F r≤
      (numbers maps τ cap M b K H drift scale n U r).sourceWord := by
  have h4 : 4^(N m r)=(4^fixedLength m)^r := by unfold N; rw [Nat.mul_comm r,pow_mul]
  have hlook : 2^(2*N m r+1)=2*(4^fixedLength m)^r := by
    rw [pow_succ,show 2*N m r=(2*fixedLength m)*r by unfold N; ring,pow_mul]
    norm_num [pow_mul]
    ring
  have hfactor : 2^(r*fixedAlpha m 2)=(2^fixedAlpha m 2)^r := by rw [Nat.mul_comm r,pow_mul]
  unfold TernaryArenaSourceControlBudget.baseWord
  rw [h4,hlook,hfactor]
  dsimp only [numbers,LightRadixKeys.word,LightRadixRows.word,LightSourceResidues.word]
  simp only [Nat.mul_assoc]
  have hR : (0 : ℤ)≤(4 : ℤ)^fixedLength m := by positivity
  have hRcast : (0 : ℤ)≤((4^fixedLength m : ℕ) : ℤ) := by positivity
  have hRbase : (0 : ℤ)≤((4 : ℕ) : ℤ)^fixedLength m := by positivity
  omega

/-- The fourth-power allocation pays the entire finite runtime argument
list, including all source and bank scalars. -/
theorem scalars (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (I : Input) (n U : ℕ)
    (hO : I.requesterCount≤n*2^(LightTernaryDimensions.J M b n U)) :
    TernaryArenaArgumentWords.scalarControl m p F r (entries (r := r) maps τ I).length≤
      TernaryArenaPrefixFootprints.envelope maps τ cap M b K H drift scale n U r := by
  let A := numbers maps τ cap M b K H drift scale n U r
  let T := total maps τ cap M b K H drift scale n U r
  have leT (x : ℕ) (hx : x∈A.list) : x≤T := List.le_sum_of_mem hx
  have hsource : A.sourceWord≤T := leT _ (by simp [Numbers.list])
  have hdepth : A.depth≤T := leT _ (by simp [Numbers.list])
  have hprefix : A.prefixCells≤T := leT _ (by simp [Numbers.list])
  have hreport : A.reporterCells≤T := leT _ (by simp [Numbers.list])
  have hcount := (cells maps τ cap M b K H drift scale I n U hO).2.2.2.trans hreport
  have hdep : 2*N m r+r+8≤A.depth := by
    dsimp [A,numbers,N]
    nlinarith
  have hb := baseWord (r := r) maps τ cap M b K H drift scale n U
  have hs := TernaryArenaArgumentBudget.scalar_le m p F r (entries (r := r) maps τ I).length A.sourceWord A.depth hb hdep
  have hS := hs.trans (Nat.add_le_add (Nat.mul_le_mul_left 16
    (Nat.pow_le_pow_left (show A.sourceWord+A.depth+1≤2*T+1 by omega) 2)) hcount)
  have hT : 100000000≤T := by dsimp [A,numbers] at hprefix; omega
  have hsq : 2000≤(T+1)^2 := by nlinarith
  have hlarge := Nat.mul_le_mul_left ((T+1)^2) hsq
  rw [←pow_add] at hlarge
  change _≤(T+1)^4
  nlinarith

theorem cleanup_words (maps : Fin F→Weight m p) (τ cap M b K H drift scale n U : ℕ) :
    2*n+2^(2*N m r+1)+16≤(numbers maps τ cap M b K H drift scale n U r).reporterWord ∧
    n*n+n+p^r+16≤(numbers maps τ cap M b K H drift scale n U r).reporterWord ∧
    2*U+3≤(numbers maps τ cap M b K H drift scale n U r).reporterWord := by
  have hn : N m r=fixedLength m*r := by unfold N; ring
  rw [hn]
  dsimp only [numbers]
  generalize TernaryMomentDetectorResources.coefficient (TernaryArenaPairMass.envelope maps cap M n) H*
      (U+1)^TernaryMomentDetectorResources.degree H=dw
  generalize (TernaryMomentChannelResources.need (TernaryArenaPairMass.envelope maps cap M n) U (2*H)).word=cw
  generalize 2^(2*(fixedLength m*r)+1)=pw
  omega

end ThreeSum.TernaryArenaFinalBounds
