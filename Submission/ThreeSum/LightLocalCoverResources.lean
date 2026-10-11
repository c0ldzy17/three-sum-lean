import Submission.ThreeSum.LightLocalCoverSetup
import Submission.ThreeSum.LightLocalCoverCost
import Submission.ThreeSum.LightLocalCoverMagnitude

/-!
# The complete local-cover program fits the uniform local-search budget

Every bound below is for the actual fixed program, including mask and
coefficient construction, counting division, histograms, matrix assembly,
the original greedy loop, and selected-row gathering.
-/

namespace ThreeSum.LightLocalCoverResources

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMagnitude

set_option maxHeartbeats 1800000

def envelope (h : ℕ) : ℕ := 2^(4000000*(h+1)^2)

theorem setup_time_polynomial {h B : ℕ} (H : Bounds h B) :
    LightLocalCoverSetup.time h ≤ 11000*B^5 := by
  have hbuild := LightLocalCoverCost.build_time_bound H.positive H.width H.vertices H.prime H.candidates H.rounds
  have hp2 : cols h ≤ B^2 := by
    have hp := Nat.pow_le_pow_left H.prime 2
    unfold cols
    nlinarith
  have hlog := Nat.log_le_self 2 (cols h)
  have hB : 1 ≤ B := H.positive
  have hL := H.width
  have hpow15 := Nat.le_self_pow (by decide : 5 ≠ 0) B
  have hpow25 := Nat.pow_le_pow_right hB (by decide : 2 ≤ 5)
  have hB5 : 1 ≤ B^5 := Nat.pow_pos (by omega)
  unfold LightLocalCoverSetup.time LightNatPower.time log2Time
  omega

theorem word_polynomial {h B : ℕ} (H : Bounds h B) :
    LightLocalCoverSetup.word h ≤ 2000*B^2 := by
  have hB := H.positive
  have hL := H.width
  have hn := H.vertices
  have hp := H.prime
  have hcap := H.cap
  have hN := H.candidates
  have hT := H.rounds
  have hP := H.decodePower
  have hmask := H.maskPower
  have hB2 : B ≤ B^2 := Nat.le_self_pow (by decide) B
  have hB2' : 1 ≤ B^2 := Nat.pow_pos (by omega)
  have hn2 : vertices h*vertices h ≤ B^2 := by
    have hh := Nat.pow_le_pow_left hn 2
    nlinarith
  have hp2 : localPrime h*localPrime h ≤ B^2 := by
    have hh := Nat.pow_le_pow_left hp 2
    nlinarith
  have hLp : (512*h+1)*localPrime h ≤ B^2 := by
    calc
      _ ≤ B*B := Nat.mul_le_mul hL (by omega)
      _ = _ := by ring
  have hdecode : LightWeightDecode.word (512*h) (localPrime h) (rows h) ≤ 20*B := by
    unfold LightWeightDecode.word LightWeightRow.word
    omega
  have hhash : LightHashHistogram.word (512*h) (localPrime h) (localPrime h) ≤ 22*B^2 := by
    unfold LightHashHistogram.word LightOneHot.word
    ring_nf at hLp hmask ⊢
    omega
  have hpair : LightPairFlags.word (512*h) (vertices h) (localPrime h) (localBucketCap h) ≤ 700*B^2 := by
    unfold LightPairFlags.word
    omega
  have hcandidate : LightLocalCoverCandidate.word (512*h) (vertices h)
      (localPrime h) (localBucketCap h) (rows h) ≤ 742*B^2 := by
    unfold LightLocalCoverCandidate.word
    omega
  have hgather : LightWeightGather.word (rows h) (scheduleSize h) (2*(512*h)) ≤ 5*B := by
    unfold LightWeightGather.word
    omega
  have hhost : LightLocalCoverHost.word h ≤ 747*B^2 := by
    unfold LightLocalCoverHost.word
    change LightLocalCoverCandidate.word (512*h) (vertices h)
      (localPrime h) (localBucketCap h) (rows h)+
      LightWeightGather.word (rows h) (scheduleSize h) (2*(512*h)) ≤ _
    omega
  have hbuild : LightLocalCoverBuild.word h ≤ 748*B^2 := by
    unfold LightLocalCoverBuild.word
    omega
  unfold LightLocalCoverSetup.word cols
  omega

theorem space_polynomial {h B : ℕ} (H : Bounds h B) (base : ℕ) :
    space base h ≤ base+20*B^3 := by
  have hB := H.positive
  have hL := H.width
  have hn := H.vertices
  have hp := H.prime
  have hN := H.candidates
  have hT := H.rounds
  have hB13 : B ≤ B^3 := Nat.le_self_pow (by decide) B
  have hB12 : B ≤ B^2 := Nat.le_self_pow (by decide) B
  have hB23 := Nat.pow_le_pow_right hB (by decide : 2 ≤ 3)
  have hB2 : 1 ≤ B^2 := Nat.pow_pos (by omega)
  have hvL : vertices h*(512*h) ≤ B^2 := by
    calc
      _ ≤ B*B := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hNL : rows h*(2*(512*h)) ≤ 2*B^2 := by
    calc
      _ ≤ B*(2*B) := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hNp : rows h*localPrime h ≤ B^2 := by
    calc
      _ ≤ B*B := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hp2 : cols h ≤ B^2 := by
    have hh := Nat.pow_le_pow_left hp 2
    unfold cols
    nlinarith
  have hn2 : vertices h*vertices h ≤ B^2 := by
    have hh := Nat.pow_le_pow_left hn 2
    nlinarith
  have hNp2 : rows h*cols h ≤ B^3 := by
    calc
      _ ≤ B*(B^2) := Nat.mul_le_mul (by omega) hp2
      _ = _ := by ring
  have hT2L : scheduleSize h*(2*(512*h)) ≤ 2*B^2 := by
    calc
      _ ≤ B*(2*B) := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hwork : work 0 h ≤ 11*B^3 := by
    unfold work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr
    omega
  have hLp : 512*h*localPrime h ≤ B^2 := by
    calc
      _ ≤ B*B := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hlog := Nat.log_le_self 2 (512*h*localPrime h+1)
  have hmax : max (512*h+1) (Nat.log 2 (512*h*localPrime h+1)+2) ≤ 4*B^2 := by omega
  have hscratch : LightLocalCoverCandidate.space (work 0 h) (512*h) (vertices h) (localPrime h) ≤ 20*B^3 := by
    unfold LightLocalCoverCandidate.space
    omega
  have hout : scheduleMaps 0 h+scheduleSize h*(2*(512*h)) ≤ 20*B^3 := by
    unfold scheduleMaps LightCoverGreedy.total
    omega
  rw [space_shift]
  exact Nat.add_le_add_left (max_le hscratch hout) base

theorem time_bound (h : ℕ) : LightLocalCoverSetup.time h ≤ envelope h := by
  have hs : 1 ≤ (h+1)^2 := Nat.pow_pos (by omega)
  calc
    _ ≤ 11000*(magnitude h)^5 := setup_time_polynomial (bounds h)
    _ ≤ 2^14*(magnitude h)^5 := Nat.mul_le_mul_right _ (by decide)
    _ = 2^(14+600000*(h+1)^2*5) := by rw [magnitude,← pow_mul,← pow_add]
    _ ≤ envelope h := Nat.pow_le_pow_right (by decide) (by omega)

theorem word_bound (h : ℕ) : LightLocalCoverSetup.word h ≤ envelope h := by
  have hs : 1 ≤ (h+1)^2 := Nat.pow_pos (by omega)
  calc
    _ ≤ 2000*(magnitude h)^2 := word_polynomial (bounds h)
    _ ≤ 2^11*(magnitude h)^2 := Nat.mul_le_mul_right _ (by decide)
    _ = 2^(11+600000*(h+1)^2*2) := by rw [magnitude,← pow_mul,← pow_add]
    _ ≤ envelope h := Nat.pow_le_pow_right (by decide) (by omega)

theorem space_bound (base h : ℕ) : space base h ≤ base+envelope h := by
  have hs : 1 ≤ (h+1)^2 := Nat.pow_pos (by omega)
  apply (space_polynomial (bounds h) base).trans
  apply Nat.add_le_add_left
  calc
    20*(magnitude h)^3 ≤ 2^5*(magnitude h)^3 := Nat.mul_le_mul_right _ (by decide)
    _ = 2^(5+600000*(h+1)^2*3) := by rw [magnitude,← pow_mul,← pow_add]
    _ ≤ envelope h := Nat.pow_le_pow_right (by decide) (by omega)

theorem depth_bound (h : ℕ) : 512*h+8 ≤ envelope h := by
  have ht : 512*h+8 ≤ LightLocalCoverSetup.time h := by
    unfold LightLocalCoverSetup.time LightNatPower.time
    omega
  exact ht.trans (time_bound h)

theorem envelope_le_search {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    envelope (Scales.microHalf (Scales.inputBits n)) ≤ Scales.localSearch 4000000 n := by
  unfold envelope Scales.localSearch
  rw [Scales.muZero_eq_twice_half]
  apply Nat.pow_le_pow_right (by decide)
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  omega

theorem time_le_search {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    LightLocalCoverSetup.time (Scales.microHalf (Scales.inputBits n)) ≤ Scales.localSearch 4000000 n :=
  (time_bound _).trans (envelope_le_search hh)

theorem word_le_search {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    LightLocalCoverSetup.word (Scales.microHalf (Scales.inputBits n)) ≤ Scales.localSearch 4000000 n :=
  (word_bound _).trans (envelope_le_search hh)

theorem space_le_search {n base : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    space base (Scales.microHalf (Scales.inputBits n)) ≤ base+Scales.localSearch 4000000 n :=
  (space_bound _ _).trans (Nat.add_le_add_left (envelope_le_search hh) base)

theorem depth_le_search {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    512*Scales.microHalf (Scales.inputBits n)+8 ≤ Scales.localSearch 4000000 n :=
  (depth_bound _).trans (envelope_le_search hh)


/-- The fully constructed exact local cover under one uniform search budget. -/
theorem meets_search {lim : Limits} {P : Program} {d pMain n base : ℕ}
    {μ : ℕ → ℤ} (S : LightLocalCoverSetup.Procs P pMain)
    (hh : 1 ≤ Scales.microHalf (Scales.inputBits n))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d+Scales.localSearch 4000000 n ≤ lim.depth)
    (hspace : base+Scales.localSearch 4000000 n ≤ lim.space)
    (hword : (Scales.localSearch 4000000 n : ℤ) ≤ lim.word) :
    let h := Scales.microHalf (Scales.inputBits n)
    Meets lim P pMain d [h,localPrime h,vertices h,localBucketCap h,base]
      μ (Scales.localSearch 4000000 n)
      (fun r ν => r = (scheduleMaps base h : ℤ) ∧
        Data ν h (maps base h) (hist0 base h) (hist1 base h) (matrixPtr base h) ∧
        ScheduleRows ν h (scheduleMaps base h) ∧
        (∀ s : Occurrence h, ν (candidates base h+s.val) = (candidateAt h s : ℤ)) ∧
        Kept μ ν base) := by
  have hd' := depth_le_search hh
  exact (S.meets hw (by omega) ((space_le_search hh).trans hspace)
    ((Int.ofNat_le.mpr (word_le_search hh)).trans hword)).mono_time (time_le_search hh)

end ThreeSum.LightLocalCoverResources
