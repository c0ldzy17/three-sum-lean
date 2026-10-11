import Submission.ThreeSum.SharedReportingBankResourceBoundsWantedScales

/-!
# Concrete execution and query resources under the wanted reporter's Need

The actual two-procedure layout constructor runs once and stores the same
fourteen pointers. Every subsequent shared-catalog query uses those pointers
without constructing another catalog or clearing its reserved buffers.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light GlobalEncoding LocalCoverBounds ReportingHostWantedLayout

set_option maxHeartbeats 2200000
set_option maxRecDepth 13000

theorem wanted_words_of_ok {lim : Limits} {dst n U N d : ℕ}
    (hN : N≤3*(magnitude n)^3) (hok : (wantedNeed n U).Ok lim dst d) :
    (LightReportingTerminal.word (half n) (blocks n) : ℤ)≤lim.word ∧
    (LightWantedDecode.word (wantedDecodeV n) N (half n) (blocks n) : ℤ)≤lim.word ∧
    (queryWord (half n) (blocks n) (BandScales.bandSize n) : ℤ)≤lim.word := by
  obtain ⟨ht,hd,hq⟩ := wanted_words_le hN
  have hw := wanted_envelope_word_of_ok hok
  exact ⟨(Int.ofNat_le.mpr ht).trans hw,(Int.ofNat_le.mpr hd).trans hw,(Int.ofNat_le.mpr hq).trans hw⟩

theorem wanted_guard_word_of_ok {lim : Limits} {dst n U old mass threshold d : ℕ}
    (hold : old≤threshold) (hmass : mass≤3*(magnitude n)^7) (hthreshold : threshold≤9*(magnitude n)^8)
    (hok : (wantedNeed n U).Ok lim dst d) :
    ((old+mass+threshold+2 : ℕ) : ℤ)≤lim.word :=
  (Int.ofNat_le.mpr (wanted_counter_le hold hmass hthreshold)).trans (wanted_envelope_word_of_ok hok)

theorem wanted_count_word_of_ok {lim : Limits} {dst n U NB NC d : ℕ}
    (hB : NB≤n) (hC : NC≤n) (hok : (wantedNeed n U).Ok lim dst d) :
    ((NB*NC : ℕ) : ℤ)≤lim.word := by
  have hh := Nat.mul_le_mul (hB.trans (input_le_magnitude n)) (hC.trans (input_le_magnitude n))
  have hp := wanted_power_le n 2 10 (by decide)
  have he : NB*NC≤wantedEnvelope n := by
    simp only [pow_two] at hp
    unfold wantedEnvelope
    omega
  exact (Int.ofNat_le.mpr he).trans (wanted_envelope_word_of_ok hok)

theorem wanted_integer_word_of_ok {lim : Limits} {dst n U d : ℕ} {z : ℤ}
    (hz : |z|≤(U : ℤ)) (hok : (wantedNeed n U).Ok lim dst d) : |z|≤lim.word := by
  have hh := wanted_values_word_of_ok hok
  have hu : (0 : ℤ)≤(U : ℤ) := Int.natCast_nonneg _
  push_cast at hh
  omega

theorem wanted_sum_word_of_ok {lim : Limits} {dst n U d : ℕ} {a b : ℤ}
    (ha : |a|≤(U : ℤ)) (hb : |b|≤(U : ℤ))
    (hok : (wantedNeed n U).Ok lim dst d) : |a+b|≤lim.word := by
  have hh := wanted_values_word_of_ok hok
  have hs := abs_add_le a b
  push_cast at hh
  omega

theorem wanted_depth_of_ok {lim : Limits} {dst n U K N NB NC d : ℕ}
    (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hok : (wantedNeed n U).Ok lim dst d) :
    d+wantedDepth (half n) (blocks n) K N NB NC≤lim.depth :=
  (Nat.add_le_add_left (wanted_depth_le hK hN hB hC) d).trans hok.depth

theorem wanted_query_scratch_of_ok {lim : Limits} {dst n U K N NB NC report s i j k d : ℕ}
    (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hk : k≤LightSwitchDepth.depth (blocks n))
    (hok : (wantedNeed n U).Ok lim dst d) :
    ReportingHostLevelData.Scratch lim (half n) (blocks n) k
      (SharedReportingBankAccess.levelCatalog report (half n) (blocks n)
        NB NC (BandScales.bandSize n) s i j k)
      (BandRawA.finiteBandPositions NB (BandScales.bandSize n) i).card
      (BandRawA.finiteBandPositions NC (BandScales.bandSize n) j).card
      (LightReportingWantedLayout.layout dst (half n) (blocks n) K N NB NC).maskBase
      (LightReportingWantedLayout.layout dst (half n) (blocks n) K N NB NC).work := by
  have H := wanted_buffers_of_ok hK hN hB hC hok
  have hl := make_bounds (root := ReportingHostWantedLayout.root dst (blocks n))
    (K := K) (W := LightBlockQuery.width (half n) (blocks n)) (G := groupSize (half n))
    (T := 2^(LightBlockQuery.width (half n) (blocks n)))
    (cap := capacityBound N NB NC (representationCap (half n) (blocks n)) (groupSize (half n))) le_rfl
  have hmasks : (LightReportingWantedLayout.layout dst (half n) (blocks n) K N NB NC).maskBase+
      queryMaskSpan (half n) (blocks n)≤
      (LightReportingWantedLayout.layout dst (half n) (blocks n) K N NB NC).work := hl.queryMasks
  exact query_scratch hk hmasks H.query (wanted_words_of_ok hN hok).2.2

theorem wanted_layout_meets {lim : Limits} {μ : ℕ→ℤ} {dst cover counter n U K N NB NC d : ℕ}
    (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hcover : cover+4≤dst) (hcounter : counter+3≤dst)
    (hgroup : μ (cover+3)=(groupSize (half n) : ℤ))
    (hcap : μ (counter+2)=(representationCap (half n) (blocks n) : ℤ))
    (hok : (wantedNeed n U).Ok lim dst d) :
    Meets lim LightReportingWantedLayout.program 1 d
      [blocks n,half n,K,cover,counter,N,NB,NC,dst] μ
      (LightReportingWantedLayout.time (half n) (blocks n))
      (fun result ν =>
        result=((LightReportingWantedLayout.layout dst (half n) (blocks n) K N NB NC).work : ℤ) ∧
        SegN ν dst (values (LightReportingWantedLayout.layout dst (half n) (blocks n) K N NB NC)) ∧
        SameOutside μ ν dst 14) := by
  have hd := hok.depth
  have he := wanted_envelope_positive n
  change d+wantedEnvelope n≤lim.depth at hd
  exact LightReportingWantedLayout.program_meets_relative hgroup hcap hok.space (by omega)
    (wanted_relative_space_of_ok hK hN hB hC hcover hcounter hok)

end ThreeSum.SharedReportingBankResourceBounds
