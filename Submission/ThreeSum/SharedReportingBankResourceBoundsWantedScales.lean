import Submission.ThreeSum.SharedReportingBankResourceBoundsWantedScalars

/-! # Polynomial relative resources for every physical wanted slot -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light Scales StageBounds GlobalEncoding LocalCoverBounds
open SharedReportingBankLayout ReportingHostWantedLayout

set_option maxHeartbeats 3200000
set_option maxRecDepth 16000

def wantedEnvelope (n : ℕ) : ℕ := 10000*(magnitude n+1)^10

def wantedNeed (n U : ℕ) : Light.Need :=
  ⟨wantedEnvelope n*(U+1),wantedEnvelope n,wantedEnvelope n⟩

theorem wanted_power_le (n e f : ℕ) (hef : e≤f) :
    (magnitude n)^e≤(magnitude n+1)^f :=
  (Nat.pow_le_pow_left (Nat.le_succ _) e).trans (Nat.pow_le_pow_right (by omega) hef)

theorem wanted_work_le {n K N NB NC : ℕ}
    (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    wantedWork (half n) (blocks n) K N NB NC≤100*(magnitude n+1)^9 := by
  have H := components n
  have hG := wanted_group_le_magnitude n
  have hJ := H.blocksBound
  have hW := H.widthBound
  have hT : 2^(width (half n) (blocks n))≤magnitude n :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans H.widthPower
  have hmass := wanted_mass_bound_le hN hB hC
  have hM7 := wanted_power_le n 7 7 le_rfl
  have h17 : 1≤(magnitude n+1)^7 := Nat.one_le_pow _ _ (by omega)
  have hmass' : massBound N NB NC (representationCap (half n) (blocks n))+1≤4*(magnitude n+1)^7 := by omega
  have hcap : capacityBound N NB NC (representationCap (half n) (blocks n)) (groupSize (half n))≤
      4*(magnitude n+1)^8 := by
    calc
      _ ≤ (4*(magnitude n+1)^7)*(magnitude n+1) :=
        Nat.mul_le_mul hmass' (hG.trans (Nat.le_succ _))
      _ = _ := by ring
  have h18 : 1≤(magnitude n+1)^8 := Nat.one_le_pow _ _ (by omega)
  have hstep : 4+2*capacityBound N NB NC (representationCap (half n) (blocks n)) (groupSize (half n))≤
      12*(magnitude n+1)^8 := by omega
  have hslot : (K+1)*(4+2*capacityBound N NB NC (representationCap (half n) (blocks n)) (groupSize (half n)))≤
      12*(magnitude n+1)^9 := by
    calc
      _ ≤ (magnitude n+1)*(12*(magnitude n+1)^8) :=
        Nat.mul_le_mul (by omega) hstep
      _ = _ := by ring
  have hM : magnitude n≤(magnitude n+1)^9 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  have h1 : 1≤(magnitude n+1)^9 := Nat.one_le_pow _ _ (by omega)
  rw [wanted_work_formula]
  dsimp only [width,localWidth,LightBlockQuery.width] at hW hT ⊢
  omega

theorem wanted_numeric_le {n K N NB NC : ℕ}
    (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    wantedNumeric (half n) (blocks n) K N NB NC≤100*(magnitude n+1)^7 := by
  have H := components n
  have hJ := H.blocksBound
  have hL := H.localWidthBound
  have hG := wanted_group_le_magnitude n
  have hR := wanted_representation_cap_le n
  have hmass := wanted_mass_bound_le hN hB hC
  have hb := hB.trans (input_le_magnitude n)
  have hc := hC.trans (input_le_magnitude n)
  have hprod : N*NB≤3*(magnitude n)^4 := by
    calc
      _ ≤ (3*(magnitude n)^3)*magnitude n := Nat.mul_le_mul hN hb
      _ = _ := by ring
  have hprod' : N*NB*NC≤3*(magnitude n)^5 := by
    calc
      _ ≤ (3*(magnitude n)^4)*magnitude n := Nat.mul_le_mul hprod hc
      _ = _ := by ring
  have hlin := linear_le_magnitude n
  have hcut := (primitive_bounds n).2.2.1
  have h2 := wanted_power_le n 2 7 (by decide)
  have h3 := wanted_power_le n 3 7 (by decide)
  have h4 := wanted_power_le n 4 7 (by decide)
  have h5 := wanted_power_le n 5 7 (by decide)
  have h7 := wanted_power_le n 7 7 le_rfl
  have hm : magnitude n≤(magnitude n+1)^7 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  unfold wantedNumeric LightBlockQuery.sourceCut
  omega

theorem wanted_scratch_le (n : ℕ) :
    wantedScratch (half n) (blocks n) (wantedDecodeV n)≤100*(magnitude n+1)^2 := by
  have H := components n
  have hT := wanted_terminal_cells_le n
  have hW := H.widthBound
  have hL := H.localWidthBound
  have hlog := wanted_decode_log_le n
  have hlin := linear_le_magnitude n
  have hquad : (width (half n) (blocks n)+1)^2≤(magnitude n)^2 := Nat.pow_le_pow_left hW 2
  have hm2 := wanted_power_le n 2 2 le_rfl
  have hm : magnitude n≤(magnitude n+1)^2 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  have h1 : 1≤(magnitude n+1)^2 := Nat.one_le_pow _ _ (by omega)
  unfold wantedScratch queryWorkSpan
  omega

theorem wanted_cells_le {n K N NB NC : ℕ}
    (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    wantedCells (half n) (blocks n) K N NB NC (wantedDecodeV n)≤wantedEnvelope n := by
  have hw := wanted_work_le hK hN hB hC
  have hn := wanted_numeric_le hK hN hB hC
  have hs := wanted_scratch_le n
  have h9 : (magnitude n+1)^9≤(magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h7 : (magnitude n+1)^7≤(magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h2 : (magnitude n+1)^2≤(magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  unfold wantedCells wantedEnvelope
  omega

theorem wanted_depth_le {n K N NB NC : ℕ}
    (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    wantedDepth (half n) (blocks n) K N NB NC≤wantedEnvelope n := by
  have H := components n
  have hJ := H.blocksBound
  have hW := H.widthBound
  have hT : 2^(width (half n) (blocks n))≤magnitude n :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans H.widthPower
  have hmass := wanted_mass_bound_le hN hB hC
  have h7 := wanted_power_le n 7 10 (by decide)
  have hm : magnitude n≤(magnitude n+1)^10 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  have h1 : 1≤(magnitude n+1)^10 := Nat.one_le_pow _ _ (by omega)
  unfold wantedDepth wantedEnvelope
  dsimp only [width,localWidth,LightBlockQuery.width] at hW hT ⊢
  omega

theorem wanted_words_le {n N : ℕ} (hN : N≤3*(magnitude n)^3) :
    LightReportingTerminal.word (half n) (blocks n)≤wantedEnvelope n ∧
    LightWantedDecode.word (wantedDecodeV n) N (half n) (blocks n)≤wantedEnvelope n ∧
    queryWord (half n) (blocks n) (BandScales.bandSize n)≤wantedEnvelope n := by
  have ht := wanted_terminal_word_le n
  have hd := wanted_decoder_word_le hN
  have hq := query_word_le n
  have h2 : (magnitude n+1)^2≤(magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h4 : (magnitude n+1)^4≤(magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h6 : (magnitude n+1)^6≤(magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  unfold wantedEnvelope queryEnvelope at *
  omega

theorem wanted_counter_le {n old mass threshold : ℕ}
    (hold : old≤threshold) (hmass : mass≤3*(magnitude n)^7) (hthreshold : threshold≤9*(magnitude n)^8) :
    old+mass+threshold+2≤wantedEnvelope n := by
  have h7 := wanted_power_le n 7 10 (by decide)
  have h8 := wanted_power_le n 8 10 (by decide)
  have h1 : 1≤(magnitude n+1)^10 := Nat.one_le_pow _ _ (by omega)
  unfold wantedEnvelope
  omega

theorem wanted_envelope_positive (n : ℕ) : 2≤wantedEnvelope n := by
  have h1 : 1≤(magnitude n+1)^10 := Nat.one_le_pow _ _ (by omega)
  unfold wantedEnvelope
  omega

noncomputable section

theorem wanted_envelope_powerBound : PowerBound wantedEnvelope 20480 := by
  have hm := magnitude_powerBound.add_same
    ((PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ)≤2048))
  have hh := (PowerBound.const 10000).mul (hm.pow 10)
  convert hh using 1 <;> (first | rfl | norm_num [wantedEnvelope])

theorem wanted_poly_need : Light.PolyNeed wantedNeed := by
  apply PolynomialResources.polyNeed_of_envelope wanted_envelope_powerBound 1
  · intro n U; simp only [wantedNeed,pow_one]; rfl
  · intro n U; simp only [wantedNeed,pow_one]; exact Nat.le_mul_of_pos_right _ (by omega)
  · intro n U; simp only [wantedNeed,pow_one]; exact Nat.le_mul_of_pos_right _ (by omega)

theorem wanted_buffers_of_ok {lim : Limits} {dst n U K N NB NC d : ℕ}
    (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hok : (wantedNeed n U).Ok lim dst d) :
    WantedBuffers lim dst (half n) (blocks n) K N NB NC (wantedDecodeV n) :=
  wanted_buffers ((Nat.add_le_add_left (wanted_cells_le hK hN hB hC) dst).trans hok.cells)

theorem wanted_envelope_word_of_ok {lim : Limits} {dst n U d : ℕ}
    (hok : (wantedNeed n U).Ok lim dst d) : (wantedEnvelope n : ℤ)≤lim.word :=
  (Int.ofNat_le.mpr (Nat.le_mul_of_pos_right _ (by omega : 0<U+1))).trans hok.word

theorem wanted_values_word_of_ok {lim : Limits} {dst n U d : ℕ}
    (hok : (wantedNeed n U).Ok lim dst d) : ((2*U : ℕ) : ℤ)≤lim.word := by
  have he := wanted_envelope_positive n
  have hb : 2*U≤wantedEnvelope n*(U+1) :=
    (Nat.mul_le_mul_left 2 (Nat.le_succ _)).trans (Nat.mul_le_mul_right _ he)
  exact (Int.ofNat_le.mpr hb).trans hok.word

theorem wanted_relative_space_of_ok {lim : Limits} {dst cover counter n U K N NB NC d : ℕ}
    (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hcover : cover+4≤dst) (hcounter : counter+3≤dst)
    (hok : (wantedNeed n U).Ok lim dst d) :
    LightReportingWantedLayout.relativeSpace dst cover counter (half n) (blocks n) K N NB NC≤lim.space := by
  have H := wanted_buffers_of_ok hK hN hB hC hok
  have hw := H.numeric
  have he := wanted_work_eq dst (half n) (blocks n) K N NB NC
  unfold wantedNumeric LightReportingWantedLayout.relativeSpace LightReportingWantedLayout.numericExtra at *
  omega

end
end ThreeSum.SharedReportingBankResourceBounds
