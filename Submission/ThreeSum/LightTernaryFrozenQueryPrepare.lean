import Submission.ThreeSum.LightTernaryFrozenQueryBranches

/-! Actual coordinate preparation and recursive branch composition. -/
namespace ThreeSum.LightTernaryFrozenQuery
open Light ThreeSum.LightSubsetAddress
set_option maxHeartbeats 3000000

variable {lim : Limits} {P : Program}

def prepTime (N : ℕ) : ℕ :=
  LightTernaryCodes.digitTime (2*N)+LightTernaryCodes.zeroTime (2*N)+LightMaskErase.time (2*N)+300

theorem step_meets {pMain pSelf pLookup pDigit pZero pErase d branchTime : ℕ}
    (hmain : P[pMain]? = some (body pSelf pLookup pDigit pZero pErase))
    (hdigit : P[pDigit]? = some (LightTernaryCodes.digitBody pErase))
    (hzero : P[pZero]? = some (LightTernaryCodes.zeroBody pErase))
    (herase : P[pErase]? = some (LightMaskErase.body pErase))
    (N K rank cut m bankCodes bankCount bankValues nearCodes nearCount nearValues powers L : ℕ)
    (q : Fin 3) (value : ℤ) (μ : ℕ → ℤ)
    (hK : K < N) (hbank : cut < rank)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(2*N+1) ≤ lim.space)
    (hword : ((2^(2*N+1) : ℕ) : ℤ) ≤ lim.word)
    (hNword : 2*(N : ℤ)+3 ≤ lim.word)
    (hcutWord : (cut : ℤ)+1 ≤ lim.word)
    (hpowers : Powers μ powers (2*N)) (hm : m < 2^(2*N))
    (hargs : ∀ x ∈ inputs N (K+1) rank cut m bankCodes bankCount bankValues
      nearCodes nearCount nearValues powers L, |x| ≤ lim.word)
    (hq : LightTernaryCodes.digit (2*N) (2*(N-(K+1))) (2*(N-(K+1))+1) m=q.val)
    (hd : d+2*N+2 ≤ lim.depth)
    (hbranch : Ends lim P d (branches pSelf)
      ⟨frame (preparedInputs N K rank cut m bankCodes bankCount bankValues
        nearCodes nearCount nearValues powers L q
        (LightTernaryCodes.zeroCode (2*N) (2*(N-(K+1))) (2*(N-(K+1))+1) m)
        (LightTernaryCodes.oneCode (2*N) (2*(N-(K+1))+1) m)),μ⟩ branchTime
      (fun σ => σ.loc 0=value ∧ σ.mem=μ)) :
    Meets lim P pMain d (inputs N (K+1) rank cut m bankCodes bankCount bankValues
      nearCodes nearCount nearValues powers L) μ (prepTime N+branchTime)
      (fun v μ' => v=value ∧ μ'=μ) := by
  have ha (x : ℤ) (hx : x ∈ inputs N (K+1) rank cut m bankCodes bankCount bankValues
      nearCodes nearCount nearValues powers L) := abs_le.mp (hargs x hx)
  have hR := ha rank (by simp [inputs])
  have hT := ha cut (by simp [inputs])
  have hM := ha m (by simp [inputs])
  have hP := ha powers (by simp [inputs])
  have hkw := ha (K+1) (by simp [inputs])
  have hsub : (N : ℤ)-((K+1 : ℕ) : ℤ)=((N-(K+1) : ℕ) : ℤ) := by omega
  have hlow : 2*(N-(K+1))≤2*N := by omega
  have hhigh : 2*(N-(K+1))+1≤2*N := by omega
  have hdi := LightTernaryCodes.digit_meets (d := d+1) hdigit herase μ hw hspace hword
    hpowers hlow hhigh hm (by omega) (by omega)
  have hze := LightTernaryCodes.zero_meets (d := d+1) hzero herase μ hw hspace hword
    hpowers hlow hhigh hm (by omega)
  have her := LightMaskErase.meets herase μ hw hspace hword hpowers
    (2*N) (2*(N-(K+1))+1) m le_rfl hhigh hm (d+1) (by omega)
  apply Meets.of_body hmain
  unfold body inputs prepTime
  light_if he hn : (rank : ℤ) ≤ (cut : ℤ)
  · exfalso; omega
  · light_if he hn : ((K+1 : ℕ) : ℤ)=0
    · exfalso; omega
    · light_set (K : ℕ)
      light_call hdi using hsub,LightTernaryCodes.digitTime,LightTernaryCodes.zeroTime,LightMaskErase.time
        with vd μd ⟨hvd,hmd⟩
      subst μd
      light_call hze using hsub,LightTernaryCodes.digitTime,LightTernaryCodes.zeroTime,LightMaskErase.time
        with vz μz ⟨hvz,hmz⟩
      subst μz
      light_call her using hsub,LightTernaryCodes.digitTime,LightTernaryCodes.zeroTime,LightMaskErase.time
        with vo μo ⟨hvo,hmo⟩
      subst μo
      subst vd vz vo
      refine Ends.seq branchTime 0 ?_ (by
        simp only [LightTernaryCodes.digitTime,LightTernaryCodes.zeroTime,LightMaskErase.time]
        light_time)
      simpa [branches,preparedInputs,inputs,LightTernaryCodes.oneCode,hq,setLocal] using
        (hbranch.mono le_rfl (fun σ hs => Ends.skip hs))

end ThreeSum.LightTernaryFrozenQuery
