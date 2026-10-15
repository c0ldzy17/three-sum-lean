import Submission.ThreeSum.LightTernaryColorPrelude
import Submission.ThreeSum.PolynomialResources
import Submission.ThreeSum.ArithmeticStageBounds

/-! Linear space, polynomial words, and near-linear time for original-color
normalization. The original signed magnitude remains the bound parameter. -/
namespace ThreeSum.TernaryColorPreludeResources
open Light LightTernaryColorPrelude LightColorParametersCosts StageBounds
open Filter
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

theorem one_band_bounds (n : ℕ) :
    BandPartition.size n n≤ 1 ∧ ColorBandBounds.count n n≤ 3 ∧ ColorBandBounds.width n n≤ 2 := by
  by_cases hn : n=0
  · subst n
    norm_num [BandPartition.size,ColorBandBounds.count,ColorBandBounds.width,LightBandEnumeration.width]
  · obtain ⟨h,h',h''⟩:= one_band (by omega : 0<n)
    exact ⟨h.le,h'.le,h''.le⟩

theorem width_le (n : ℕ) : width n≤ n+1 := by
  unfold width
  exact Nat.add_le_add_right (LightScales.inputBits_le_self n) 1

theorem clog_le_width (n : ℕ) : Nat.clog 2 n≤ width n :=
  Nat.clog_le_of_le_pow (width_sufficient n)

theorem code_power_bound (n : ℕ) : 2^(width n+1)≤ 4*(n+1) := by
  have hh : 2^(Scales.inputBits n)≤ n+1 := by
    simpa [Scales.inputBits,Nat.log2_eq_log_two] using Nat.pow_log_le_add_one 2 n
  calc
    _=4*2^(Scales.inputBits n) := by
      unfold width
      rw [show Scales.inputBits n+1+1=Scales.inputBits n+2 by omega,pow_add]
      norm_num
      ring
    _≤ _ := Nat.mul_le_mul_left 4 hh

theorem space_bound (free n : ℕ) : space free n≤ free+14*n+width n+16 := by
  obtain ⟨_,hc,hw⟩:= one_band_bounds n
  unfold space LightColorBands.space ColorBandBounds.space work ce cv be bv ae av class2 class1 class0
  omega

theorem word_bound (n U : ℕ) : word n U≤ 1000*(n+1)*(U+1) := by
  obtain ⟨hs,_,_⟩:= one_band_bounds n
  have hp:= code_power_bound n
  have hw:= width_le n
  unfold word LightColorBands.word ColorBandBounds.word LightBandEnumeration.word
  nlinarith only [hs,hp,hw,Nat.zero_le (n*U)]

theorem depth_bound (n : ℕ) : depth n≤ 2*width n+n+18 := by
  obtain ⟨_,_,hw⟩:= one_band_bounds n
  have hc:= clog_le_width n
  unfold depth LightColorBands.depth ColorBandBounds.depth
  omega

def need (n U : ℕ) : Light.Need :=
  ⟨word n U,14*n+width n+20,2*width n+n+20⟩

theorem need_ok {lim : Limits} {n U free d : ℕ} (H : (need n U).Ok lim free d) :
    space free n≤ lim.space ∧ (word n U:ℤ)≤ lim.word ∧ d+depth n≤ lim.depth := by
  have hs:= space_bound free n
  have hd:= depth_bound n
  refine ⟨?_,H.word,?_⟩
  · have hh:= H.cells
    dsimp [need] at hh
    omega

  · have hh:= H.depth
    dsimp [need] at hh
    omega

theorem program_meets {lim : Limits} {src n params row free U d : ℕ}
    (μ : ℕ→ℤ) (p : Coloring.Parameter (width n)) (x : Fin n→ℤ)
    (hn : 0<n) (hsrc : src+n≤free) (hparams : params+19≤free) (hrow : row+6≤free)
    (H : (need n U).Ok lim free d)
    (hbits : μ params=(Scales.inputBits n:ℤ))
    (hfields : Seg μ row (ColorParameters.fields p))
    (hinput : Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i|≤(U:ℤ)) :
    Meets lim LightTernaryColorPrelude.program 27 d [src,n,params,row,free] μ (time n)
      (fun r ν=>Output μ ν free p x r) :=by
  obtain ⟨hs,hw,hd⟩:=need_ok H
  exact LightTernaryColorPrelude.program_meets μ p x hn hsrc hparams hrow H.space hs hw hd
    hbits hfields hinput hbound

theorem time_bound (n : ℕ) : time n≤ 20000*(width n+1)*(n+1) := by
  have ht:= LightColorBands.time_bound (width n) n n
  obtain ⟨_,hc,hw⟩:= one_band_bounds n
  have hlog:= clog_le_width n
  have hband : ColorBandBounds.time n n≤
      2100*(n+1)*(width n+1)+3000*(n+4)+400 := by
    unfold ColorBandBounds.time
    have h0:= Nat.mul_le_mul_left (2100*(n+1)) (Nat.add_le_add_right hlog 1)
    have h1:= Nat.mul_le_mul (Nat.mul_le_mul_left 1000 (by omega : ColorBandBounds.count n n+n+1≤ n+4))
      (Nat.add_le_add_right hw 1)
    omega
  have hW : 1≤ width n := by unfold width; omega
  unfold time
  nlinarith only [ht,hband,hW,Nat.zero_le (n*width n)]

noncomputable section

theorem time_powerBound : PowerBound time 1 := by
  have hW:= (LightColorParametersCosts.width_powerBound).add_same (PowerBound.const 1)
  have hN:= ArithmeticStageBounds.identity_powerBound.add_same
    ((PowerBound.const 1).mono_exponent (by norm_num : (0:ℝ)≤ 1))
  have hh:= (PowerBound.const 20000).mul (hW.mul hN)
  apply ArithmeticStageBounds.powerBound_mono (by simpa only [zero_add] using hh)
  exact Eventually.of_forall (fun n=>by simpa only [Nat.mul_assoc] using time_bound n)

theorem polyNeed : Light.PolyNeed need := by
  have he : PowerBound (fun n=>1000*(n+1)) 1 := by
    simpa only [zero_add] using (PowerBound.const 1000).mul
      (ArithmeticStageBounds.identity_powerBound.add_same
        ((PowerBound.const 1).mono_exponent (by norm_num : (0:ℝ)≤ 1)))
  apply PolynomialResources.polyNeed_of_envelope he 1
  · intro n U
    simpa only [need,pow_one] using word_bound n U
  · intro n U
    have hW:= width_le n
    dsimp [need]
    nlinarith only [hW,Nat.zero_le (n*U)]
  · intro n U
    have hW:= width_le n
    dsimp [need]
    nlinarith only [hW,Nat.zero_le (n*U)]

end
end ThreeSum.TernaryColorPreludeResources
