import Submission.ThreeSum.LightEncodedColorWantedSources

/-! # Numeric envelopes for the actually balanced wanted records -/

namespace ThreeSum.EncodedColorWantedCosts

open Light WantedResidueKeys

set_option maxHeartbeats 1800000

def time (P M h J U len : ℕ) : ℕ :=
  LightCoverKeys.time h J+LightRawAKeys.time len U+
    LightOriginalOffset.time M (3*len) (LightGuardedWanted.totalKeys h J)
      (LightGuardedWanted.keyBound P h J)+
    2000*(3*len+LightGuardedWanted.totalKeys h J+M+
      3*len*LightGuardedWanted.totalKeys h J/M+1)*
      (Nat.log 2 (LightGuardedWanted.keyBound P h J+1)+Nat.log 2 (M+M+1)+1)+400

def sourceBase (free M h J len : ℕ) : ℕ :=
  LightWantedSetup.pairBase (LightGuardedWanted.wantedFree free h J len)
    (3*len) (LightGuardedWanted.totalKeys h J) M+
    2*(3*len*LightGuardedWanted.totalKeys h J/M)

def space (free P M h J U len : ℕ) : ℕ :=
  max (LightCoverKeys.space free h J)
    (max (LightRawAKeys.space (LightCoverKeyData.keyEnd free h J) len U)
      (max (LightOriginalOffset.space (LightGuardedWanted.wantedFree free h J len)
        M (3*len+LightGuardedWanted.totalKeys h J) (LightGuardedWanted.keyBound P h J))
        (max (LightSourceResidues.space
          (LightWantedSetup.pairBase (LightGuardedWanted.wantedFree free h J len)
            (3*len) (LightGuardedWanted.totalKeys h J) M)
          M (LightGuardedWanted.keyBound P h J) M)
          (sourceBase free M h J len))))

theorem time_le (P M h J U : ℕ) [NeZero M] (xs : List ℤ) :
    LightGuardedWanted.time P M h J U xs ≤ time P M h J U xs.length := by
  have h := LightBalancedWanted.time_bound M (LightGuardedWanted.left P xs)
    (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J)
    (LightGuardedWanted.keyBound P h J)
  unfold LightGuardedWanted.time time
  omega

theorem sourceBase_eq (free M h J len : ℕ) :
    sourceBase free M h J len=LightCoverKeyData.keyEnd free h J+
      6*len+2*LightGuardedWanted.totalKeys h J+3*M+5+
      2*(3*len*LightGuardedWanted.totalKeys h J/M) := by
  unfold sourceBase LightWantedSetup.pairBase LightSourceBucketSetup.next LightWantedSetup.bucketBase
    LightWantedSetup.rightCodes LightWantedSetup.leftCodes LightGuardedWanted.wantedFree
  omega

theorem sourceBase_le (free P M h J : ℕ) [NeZero M] (xs : List ℤ) :
    EncodedColorWantedData.nextFree (LightGuardedWanted.wantedFree free h J xs.length) M
      (LightGuardedWanted.left P xs) (LightGuardedWanted.right h J)
      (3*xs.length) (LightGuardedWanted.totalKeys h J) (RawAKeyLists.selected M P xs h J) ≤
        sourceBase free M h J xs.length := by
  have h := LightBalancedWanted.total_le_div M (LightGuardedWanted.left P xs)
    (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J)
  rw [LightGuardedWanted.selected_eq] at h
  unfold EncodedColorWantedData.nextFree sourceBase
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 h) _

theorem space_le (free P M h J U : ℕ) [NeZero M] (xs : List ℤ) :
    LightGuardedWanted.space free P M h J U xs ≤ space free P M h J U xs.length := by
  have h := sourceBase_le free P M h J xs
  unfold LightGuardedWanted.space LightBalancedWanted.space LightWantedSetup.space space
  rw [LightGuardedWanted.selected_eq]
  exact max_le_max le_rfl (max_le_max le_rfl (max_le_max le_rfl (max_le_max le_rfl h)))

theorem keyBound_mono {P P' h J : ℕ} (hP : P ≤ P') :
    LightGuardedWanted.keyBound P h J ≤ LightGuardedWanted.keyBound P' h J := by
  unfold LightGuardedWanted.keyBound
  omega

theorem sourceBase_mono {free M h J len len' : ℕ} (hlen : len ≤ len') :
    sourceBase free M h J len ≤ sourceBase free M h J len' := by
  rw [sourceBase_eq,sourceBase_eq]
  gcongr

theorem time_mono {P P' M h J U len len' : ℕ} (hP : P ≤ P') (hlen : len ≤ len') :
    time P M h J U len ≤ time P' M h J U len' := by
  have hkey := keyBound_mono (h := h) (J := J) hP
  unfold time LightRawAKeys.time LightOriginalOffset.time LightResidueHistogram.time
    LightResidues.residuesTime LightResidues.residueBudget LightHistogram.histogramTime
    LightHistogram.countTime LightReportingAffine.time
  gcongr

theorem space_mono {free P P' M h J U len len' : ℕ} (hP : P ≤ P') (hlen : len ≤ len') :
    space free P M h J U len ≤ space free P' M h J U len' := by
  have hkey := keyBound_mono (h := h) (J := J) hP
  have hbase := sourceBase_mono (free := free) (M := M) (h := h) (J := J) hlen
  unfold space LightRawAKeys.space LightOriginalOffset.space LightSourceResidues.space
    LightWantedSetup.pairBase LightSourceBucketSetup.next LightWantedSetup.bucketBase
    LightWantedSetup.rightCodes LightWantedSetup.leftCodes LightGuardedWanted.wantedFree
  gcongr

theorem word_mono {P P' M h J U len len' : ℕ} (hP : P ≤ P') (hlen : len ≤ len') :
    LightGuardedWanted.word P M h J U len ≤ LightGuardedWanted.word P' M h J U len' := by
  have hkey := keyBound_mono (h := h) (J := J) hP
  unfold LightGuardedWanted.word LightRawAKeys.word LightBalancedWanted.word
    LightOriginalOffset.word LightKaratsuba.wordBound LightSourceResidues.word
  gcongr

end ThreeSum.EncodedColorWantedCosts
