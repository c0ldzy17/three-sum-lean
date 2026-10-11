import Submission.ThreeSum.EncodedColorWantedResources
import Submission.ThreeSum.LightEncodedColorPipeline

/-! # Polynomial Need for the exact closed selected-color pipeline -/

namespace ThreeSum.EncodedColorResources

open Light Scales BandScales ArithmeticStageBounds StageBounds

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000

theorem pipeline_space_bound (free n U : ℕ) :
    LightEncodedColorPipeline.space free n U ≤ free+3000*(scale n)^5+U := by
  have hb := (scale_bounds n).1
  have hp5 : scale n ≤ (scale n)^5 := Nat.le_self_pow (by decide) _
  have hp35 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 3 ≤ 5)
  have hcover := cover_address_bound free n
  have hprime := prime_space_bound free n U
  have hstage := stage_space_bound (EncodedColorPipelineData.coverBase free n) n U
  have hsource : LightEncodedColorPipeline.sourceBound free n ≤
      EncodedColorPipelineData.coverBase free n+100*(scale n)^5 :=
    wanted_source_base_bound (EncodedColorPipelineData.coverBase free n) n
  have hfinish : LightEncodedColorPipeline.finishBound free n ≤
      LightEncodedColorPipeline.sourceBound free n+200*(scale n)^5 :=
    source_finish_bound (LightEncodedColorPipeline.sourceBound free n) n
  unfold LightEncodedColorPipeline.space
  refine max_le ?_ (max_le ?_ ?_) <;>
    nlinarith only [hb,hp5,hp35,hcover,hprime,hstage,hsource,hfinish]

theorem pipeline_word_bound (n U : ℕ) :
    LightEncodedColorPipeline.word n U ≤ 200000*(scale n)^9+9*U := by
  have hb := (scale_bounds n).1
  have hprime := prime_word_bound n U
  have hstage := stage_word_bound n U
  have hcap := incidence_cap_le n
  have hP := (scale_bounds n).2.2.2.2.1
  have hM := (dimensions n).2.2.2.2
  have hg := (dimensions n).2.2.2.1
  have hh := (local_bounds n).width
  have hJ := (dimensions n).2.1
  have hcut := (dimensions n).2.2.1
  have hS := (powers n).2.1
  have hp9 : scale n ≤ (scale n)^9 := Nat.le_self_pow (by decide) _
  have hp39 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 3 ≤ 9)
  have hp69 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 6 ≤ 9)
  have hmax : max (LightEncodedColorPrimeHost.inputWord n U)
      (EncodedColorStageCosts.word n (maxMod n) (radix n) U (EncodedColorStageCosts.incidenceCap n)) ≤
      150000*(scale n)^9+9*U := max_le (by omega) (by omega)
  unfold LightEncodedColorPipeline.word
  change max (LightEncodedColorPrimeHost.inputWord n U)
    (EncodedColorStageCosts.word n (maxMod n) (radix n) U (EncodedColorStageCosts.incidenceCap n))+
    EncodedColorStageCosts.incidenceCap n+maxMod n+radix n+bandSize n+half n+blocks n+mu n+
    LightBlockSourceCatalog.count (half n) (blocks n)+100 ≤ _
  nlinarith only [hb,hmax,hcap,hP,hM,hg,hh,hJ,hcut,hS,hp9,hp39]

theorem pipeline_depth_bound (n : ℕ) : LightEncodedColorPipeline.depth n ≤ 30*(scale n)^3 := by
  have hb := (scale_bounds n).1
  have hp := prime_depth_bound n
  have hs := stage_depth_bound n
  have hp3 : scale n ≤ (scale n)^3 := Nat.le_self_pow (by decide) _
  unfold LightEncodedColorPipeline.depth
  omega

def need (n U : ℕ) : Light.Need :=
  ⟨LightEncodedColorPipeline.word n U,3000*(scale n)^5+U,LightEncodedColorPipeline.depth n⟩

def envelope (n : ℕ) : ℕ := 1000000*(scale n)^10

theorem need_bounds (n U : ℕ) :
    (need n U).word ≤ envelope n*(U+1) ∧
    (need n U).cells ≤ envelope n*(U+1) ∧
    (need n U).depth ≤ envelope n*(U+1) := by
  have hb := (scale_bounds n).1
  have hp10 : 1 ≤ (scale n)^10 := Nat.one_le_pow _ _ (by omega)
  have hmul : (scale n)^10 ≤ (scale n)^10*(U+1) := Nat.le_mul_of_pos_right _ (by omega)
  have hU : U ≤ (scale n)^10*(U+1) := (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ hp10)
  have hp39 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 3 ≤ 10)
  have hp59 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 5 ≤ 10)
  have hp99 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 9 ≤ 10)
  have hw := pipeline_word_bound n U
  have hd := pipeline_depth_bound n
  rw [show envelope n*(U+1)=1000000*((scale n)^10*(U+1)) by unfold envelope; ring]
  change LightEncodedColorPipeline.word n U ≤ _ ∧ 3000*(scale n)^5+U ≤ _ ∧
    LightEncodedColorPipeline.depth n ≤ _
  constructor
  · omega
  · constructor <;> omega

noncomputable section

theorem envelope_powerBound : PowerBound envelope 20480 := by
  have hh := (PowerBound.const 1000000).mul (scale_powerBound.pow 10)
  convert hh using 1 <;> (first | rfl | norm_num)

theorem poly_need : Light.PolyNeed need := by
  apply PolynomialResources.polyNeed_of_envelope envelope_powerBound 1
  · intro n U; simpa only [pow_one] using (need_bounds n U).1
  · intro n U; simpa only [pow_one] using (need_bounds n U).2.1
  · intro n U; simpa only [pow_one] using (need_bounds n U).2.2

end

theorem bounds_of_ok {lim : Limits} {free n U d : ℕ} (hok : (need n U).Ok lim free d) :
    LightEncodedColorPipeline.space free n U ≤ lim.space ∧
    (LightEncodedColorPipeline.word n U : ℤ) ≤ lim.word ∧
    d+LightEncodedColorPipeline.depth n ≤ lim.depth := by
  refine ⟨?_,hok.word,hok.depth⟩
  apply (pipeline_space_bound free n U).trans
  simpa only [need,Nat.add_assoc] using hok.cells

theorem program_meets {lim : Limits} {μ : ℕ → ℤ} {src n params row free U d : ℕ}
    (color : Coloring.Parameter (inputBits n+1)) (x : Fin n → ℤ)
    (hn : 0 < n) (hR : 4 ≤ radix n)
    (hsrc : src+n ≤ free) (hparams : params+19 ≤ free) (hrow : row+6 ≤ free)
    (hok : (need n U).Ok lim free d)
    (hread : Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i| ≤ (U : ℤ))
    (hparameters : Seg μ params (LightParameterInit.values n))
    (hcolor : Seg μ row (ColorParameters.fields color)) :
    Meets lim LightEncodedColorPipeline.program 255 d [src,n,params,row,free] μ
      (LightEncodedColorPipeline.time n U)
      (fun r ν => EncodedColorPipelineData.Output ν free n color x r ∧ Kept μ ν free) := by
  obtain ⟨hs,hw,hd⟩ := bounds_of_ok hok
  exact LightEncodedColorPipeline.program_meets color x hok.space hn hR hsrc hparams hrow
    hs hw hd hread hbound hparameters hcolor

end ThreeSum.EncodedColorResources
