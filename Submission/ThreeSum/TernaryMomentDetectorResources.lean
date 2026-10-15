import Submission.ThreeSum.TernaryMomentWeightBounds
import Submission.ThreeSum.PolynomialResources

/-! A concrete polynomial resource need for the reporting matrix and exact
zero detector. Backend dictionaries, banks and source kernels have their own
proved needs and are combined with this extra need by the final host. -/
noncomputable section
namespace ThreeSum.TernaryMomentDetectorResources
open TernaryNativeMomentBounds StageBounds

def input (B U H : ℕ) : ℕ := U+B*(2*U+1)^(2*H)
def need (B U H : ℕ) : Light.Need :=
  ⟨detectorWord (input B U H) H,(2*H+1)*(B+1),5⟩

def coefficient (B H : ℕ) : ℕ :=
  ((LightMomentDeterminant.wordCoefficient H).toNat+1)*
    (B*2^(2*H)+1)^(LightMomentDeterminant.wordDegree H+1)+
  (2*H+1)*(B+1)+5

def degree (H : ℕ) : ℕ :=(2*H+1)*(LightMomentDeterminant.wordDegree H+1)

theorem input_bound (B U H : ℕ) :
    input B U H+1≤(B*2^(2*H)+1)*(U+1)^(2*H+1) := by
  have hbase : 1≤U+1 := by omega
  have hpow := Nat.pow_le_pow_left (show 2*U+1≤2*(U+1) by omega) (2*H)
  have hlow := Nat.pow_le_pow_right hbase (show 2*H≤2*H+1 by omega)
  have hone : U+1≤(U+1)^(2*H+1) := by
    simpa using Nat.pow_le_pow_right hbase (show 1≤2*H+1 by omega)
  have hpow' : (2*U+1)^(2*H)≤2^(2*H)*(U+1)^(2*H+1) := by
    calc
      _ ≤ (2*(U+1))^(2*H) := hpow
      _ = 2^(2*H)*(U+1)^(2*H) := mul_pow _ _ _
      _ ≤ _ := Nat.mul_le_mul_left _ hlow
  have hm := Nat.mul_le_mul_left B hpow'
  unfold input
  nlinarith only [hm,hone]

theorem need_bound (B U H : ℕ) :
    (need B U H).word≤coefficient B H*(U+1)^degree H ∧
    (need B U H).cells≤coefficient B H*(U+1)^degree H ∧
    (need B U H).depth≤coefficient B H*(U+1)^degree H := by
  have hp := Nat.pow_le_pow_left (input_bound B U H) (LightMomentDeterminant.wordDegree H+1)
  have hm := Nat.mul_le_mul_left ((LightMomentDeterminant.wordCoefficient H).toNat+1) hp
  have hw : (need B U H).word≤
      (((LightMomentDeterminant.wordCoefficient H).toNat+1)*
        (B*2^(2*H)+1)^(LightMomentDeterminant.wordDegree H+1))*(U+1)^degree H := by
    simpa only [need,detectorWord,mul_pow,← pow_mul,degree,mul_assoc] using hm
  have h1 : 1≤(U+1)^degree H := Nat.one_le_pow _ _ (by omega)
  have hc : ((2*H+1)*(B+1))≤coefficient B H := by unfold coefficient; omega
  have hd : 5≤coefficient B H := by unfold coefficient; omega
  refine ⟨hw.trans (Nat.mul_le_mul_right _ (by unfold coefficient; omega)),?_,?_⟩
  · exact hc.trans (Nat.le_mul_of_pos_right _ h1)
  · exact hd.trans (Nat.le_mul_of_pos_right _ h1)

theorem polyNeed {B : ℕ→ℕ} {a : ℝ} (hB : PowerBound B a) (H : ℕ) :
    Light.PolyNeed (fun n U => need (B n) U H) := by
  let q := max a 0
  have hBq : PowerBound B q := hB.mono_exponent (le_max_left a 0)
  have hbase : PowerBound (fun n => B n*2^(2*H)+1) q := by
    have hm := hBq.mul (PowerBound.const (2^(2*H)))
    have hm' : PowerBound (fun n => B n*2^(2*H)) q := by simpa using hm
    exact hm'.add_same ((PowerBound.const 1).mono_exponent (by dsimp [q]; exact le_max_right _ _))
  have hmain : PowerBound (fun n =>
      ((LightMomentDeterminant.wordCoefficient H).toNat+1)*
        (B n*2^(2*H)+1)^(LightMomentDeterminant.wordDegree H+1))
      (((LightMomentDeterminant.wordDegree H+1 : ℕ) : ℝ)*q) := by
    simpa using (PowerBound.const ((LightMomentDeterminant.wordCoefficient H).toNat+1)).mul
      (hbase.pow (LightMomentDeterminant.wordDegree H+1))
  have hB1 : PowerBound (fun n => B n+1) q :=
    hBq.add_same
      ((PowerBound.const 1).mono_exponent (by dsimp [q]; exact le_max_right _ _))
  have hq : q≤((LightMomentDeterminant.wordDegree H+1 : ℕ) : ℝ)*q := by
    have hq0 : 0≤q := le_max_right _ _
    have hD : (1 : ℝ)≤((LightMomentDeterminant.wordDegree H+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    nlinarith
  have hcells : PowerBound (fun n => (2*H+1)*(B n+1))
      (((LightMomentDeterminant.wordDegree H+1 : ℕ) : ℝ)*q) := by
    have hh := (PowerBound.const (2*H+1)).mul (hB1.mono_exponent hq)
    simpa using hh
  have he : PowerBound (fun n => coefficient (B n) H)
      (((LightMomentDeterminant.wordDegree H+1 : ℕ) : ℝ)*q) := by
    have h0 : 0≤((LightMomentDeterminant.wordDegree H+1 : ℕ) : ℝ)*q := mul_nonneg (by positivity) (le_max_right _ _)
    exact (hmain.add_same hcells).add_same ((PowerBound.const 5).mono_exponent h0)
  apply PolynomialResources.polyNeed_of_envelope he (degree H)
  · intro n U
    exact (need_bound (B n) U H).1
  · intro n U
    exact (need_bound (B n) U H).2.1
  · intro n U
    exact (need_bound (B n) U H).2.2

/-- The envelope coefficient is the literal-pair count times the actual
factorial mass bound. No support oracle is used for arithmetic bounds. -/
theorem detectorInput_le {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (B U H : ℕ) (hpairs : pairBound S*2^N≤B) :
    detectorInput S U H ≤ input B U H := by
  unfold detectorInput momentBound input
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hpairs) _

theorem moments_le_input {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (B U H : ℕ) (hpairs : pairBound S*2^N≤B) (left right : ℕ→ℤ)
    (hleft : ∀ j<S.left.NL, |left j|≤(U : ℤ))
    (hright : ∀ j<S.right.NL, |right j|≤(U : ℤ)) :
    ∀ i, ∀ k≤2*H,
      |∑ p : TernaryNativePairMoments.Pair S i,
        TernaryNativePairMoments.mass S i p*TernaryNativePairMoments.mode left right p^k|
        ≤(input B U H : ℤ) := by
  intro i k hk
  exact (detector_moments_bound S left right hleft hright i k hk).trans
    (by exact_mod_cast detectorInput_le S B U H hpairs)

theorem target_le_input (B U H : ℕ) (x : ℤ) (hx : |x|≤(U : ℤ)) :
    |x|≤(input B U H : ℤ) :=
  hx.trans (by exact_mod_cast (Nat.le_add_right U (B*(2*U+1)^(2*H))))

theorem word_guard (B U H : ℕ) (lim : Light.Limits)
    (hw : ((need B U H).word : ℤ)≤lim.word) :
    max (input B U H : ℤ) (LightMomentDeterminant.wordBound (input B U H) H)≤lim.word :=
  (detector_word_bound (input B U H) H).trans hw

theorem workspace_bound {count : ℕ} (B U H : ℕ) (hc : count≤B) :
    (2*H+1)*count+(2*H+1)≤(need B U H).cells := by
  dsimp [need]
  nlinarith

end ThreeSum.TernaryMomentDetectorResources
