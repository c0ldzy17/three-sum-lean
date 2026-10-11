import Submission.ThreeSum.LightGuardedWanted
import Submission.ThreeSum.LightBandRawAColor
import Submission.ThreeSum.SourceBandFinite

/-! # Concrete source inputs from the retained normalization and wanted outputs -/

namespace ThreeSum.SourceFiniteInputs

open Light GlobalEncoding LocalCoverBounds LightLocalCoverLayout LightLocalCoverSchedule

def maps (free h : ℕ) : ℕ := scheduleMaps (LightLocalCoverInit.base free) h
def candidates (free h : ℕ) : ℕ := LightLocalCoverLayout.candidates (LightLocalCoverInit.base free) h
def leftCounts (free h : ℕ) : ℕ := hist0 (LightLocalCoverInit.base free) h
def rightCounts (free h : ℕ) : ℕ := hist1 (LightLocalCoverInit.base free) h

theorem cover_input {μ : ℕ → ℤ} {free h J : ℕ} (H : LightCoverKeyData.Stored μ free h J) :
    BlockSourceCoverInput.Input μ h (maps free h) (candidates free h) (leftCounts free h) (rightCounts free h) :=
  BlockSourceCoverInput.of_cover H.data H.rows H.indices

theorem cover_ends (free h J : ℕ) :
    maps free h+2*(512*h)*scheduleSize h ≤ LightCoverKeyData.keyEnd free h J ∧
    candidates free h+scheduleSize h ≤ LightCoverKeyData.keyEnd free h J ∧
    leftCounts free h+rows h*localPrime h ≤ LightCoverKeyData.keyEnd free h J ∧
    rightCounts free h+rows h*localPrime h ≤ LightCoverKeyData.keyEnd free h J := by
  have hh := LightCoverKeyData.afterCover_le_keyEnd free h J
  obtain ⟨_,hl,hr,_,hc⟩ := LightLocalCoverRetention.table_ends_le (LightLocalCoverInit.base free) h
  have hm : maps free h+2*(512*h)*scheduleSize h=LightCoverKeys.afterCover free h := by
    unfold maps LightCoverKeys.afterCover LightLocalCoverMetadata.nextFree
    rw [Nat.mul_comm (2*(512*h)) (scheduleSize h)]
  exact ⟨hm.le.trans hh,hc.trans hh,hl.trans hh,hr.trans hh⟩

theorem prepared_read {μ : ℕ → ℤ} {values endpoints g : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (H : LightBandPreprocessing.Represents μ values endpoints g hg original L hs) :
    ∀ j < L.length, μ (values+j)=L.getD j 0 := fun j hj => H.1.getD hj 0

theorem prepared_headers {μ : ℕ → ℤ} {values endpoints g : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (H : LightBandPreprocessing.Represents μ values endpoints g hg original L hs) :
    μ endpoints=(L.length : ℤ) ∧ μ (endpoints+1)=(BandPartition.size L.length g : ℤ) :=
  ⟨H.2.2.2.1,H.2.2.2.2.1⟩

theorem prepared_bound {μ : ℕ → ℤ} {values endpoints g U : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (H : LightBandPreprocessing.Represents μ values endpoints g hg original L hs)
    (hb : ∀ z ∈ original, |z| ≤ (U : ℤ)) :
    ∀ j < L.length, |L.getD j 0| ≤ (U : ℤ) := by
  intro j hj
  rw [List.getD_eq_getElem _ _ hj]
  exact hb _ ((H.2.2.1 _).mp (List.getElem_mem hj))

theorem selected_lt (M P h J : ℕ) [NeZero M] (xs : List ℤ) :
    RawAKeyLists.selected M P xs h J < M := by
  rw [← LightGuardedWanted.selected_eq]
  exact LightOriginalOffset.selected_lt ..

theorem selected_abs_le (M P h J : ℕ) [NeZero M] (xs : List ℤ) :
    |(RawAKeyLists.selected M P xs h J : ℤ)| ≤ (M : ℤ) := by
  simpa only [abs_of_nonneg (Int.natCast_nonneg _)] using
    (Int.ofNat_le.mpr (selected_lt M P h J xs).le)

theorem wanted_shift_read {μ : ℕ → ℤ} {free M P h J : ℕ} [NeZero M] {xs : List ℤ}
    (H : LightWantedSetup.Output μ (LightGuardedWanted.wantedFree free h J xs.length) M
      (LightGuardedWanted.left P xs) (LightGuardedWanted.right h J)
      (3*xs.length) (LightGuardedWanted.totalKeys h J) (RawAKeyLists.selected M P xs h J)) :
    μ (LightGuardedWanted.wantedFree free h J xs.length+3)=(RawAKeyLists.selected M P xs h J : ℤ) :=
  H.2.2.2.1

end ThreeSum.SourceFiniteInputs
