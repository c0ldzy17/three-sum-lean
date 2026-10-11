import Submission.ThreeSum.LightSourceTrim

/-!
# Constructing independent endpoint flags directly from a global mask

The fixed program creates its own powers and Boolean coordinate row, then
performs the actual selected-block trimming scan. There is no Boolean-bit or
trim-flag oracle in the contract.
-/

namespace ThreeSum.LightSourceMaskFlags

open Light SourceFlagProduct

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

/-- Arguments: block count, width, row size, local modulus, cap, occurrence
indices, schedule coefficients, occurrence-to-candidate indices, both
candidate histograms, global mask, output, bit scratch, row scratch,
and reusable arithmetic scratch. -/
def body (pBits pTrim : ℕ) : Stmt :=
  .call pBits [v 0 *' v 1,v 10,v 12,v 14] 15 ;;
  .call pTrim [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 12,v 13,v 14,v 11] 15

def time (J L U : ℕ) : ℕ := LightMaskBits.time (J*L)+LightSourceTrim.time J L U+100

def word (J L p U V cap : ℕ) : ℕ := 2^(J*L+1)+LightSourceRowFlag.word L p U V cap

def space (work J L U : ℕ) : ℕ :=
  work+max (J*L+1) (3+(Nat.log 2 (L*U+1)+2))

structure Procs (P : Program) (pMain : ℕ) where
  pBits : ℕ
  pPowers : ℕ
  pErase : ℕ
  pTrim : ℕ
  bits : P[pBits]? = some (LightMaskBits.body pPowers pErase)
  powers : P[pPowers]? = some powTableBody
  erase : P[pErase]? = some (LightMaskErase.body pErase)
  trim : LightSourceTrim.Procs P pTrim
  main : P[pMain]? = some (body pBits pTrim)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {J L h p cap occ maps candidates histL histR mask dst bitBase rowOut work U V M K : ℕ}
    (sel candidate : ℕ → ℕ) (w0 w1 leftCount rightCount : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*L+3 ≤ lim.depth)
    (hp : 0 < p) (hh : h ≤ L)
    (hocc : occ+J ≤ bitBase) (hmaps : maps+2*L*M ≤ bitBase)
    (hcandidates : candidates+M ≤ bitBase)
    (hleft : histL+K*p ≤ bitBase) (hright : histR+K*p ≤ bitBase)
    (hdst : dst+2 ≤ bitBase) (hbits : bitBase+J*L ≤ rowOut) (hrowOut : rowOut+2 ≤ work)
    (hspace : space work J L U ≤ lim.space)
    (hword : (word J L p U V cap : ℤ) ≤ lim.word) (hmask : mask < 2^(J*L))
    (hsel : ∀ j < J, sel j < M) (hcandidate : ∀ s < M, candidate s < K)
    (hoccRead : ∀ j < J, μ (occ+j) = (sel j : ℤ))
    (hcandidateRead : ∀ s < M, μ (candidates+s) = (candidate s : ℤ))
    (hread0 : ∀ s < M, ∀ a < L, μ (maps+2*L*s+a) = (w0 s a : ℤ))
    (hread1 : ∀ s < M, ∀ a < L, μ (maps+2*L*s+L+a) = (w1 s a : ℤ))
    (hbound0 : ∀ s < M, ∀ a < L, w0 s a ≤ U)
    (hbound1 : ∀ s < M, ∀ a < L, w1 s a ≤ U)
    (hcountL : ∀ k < K, ∀ r < p, μ (histL+k*p+r) = (leftCount k r : ℤ))
    (hcountR : ∀ k < K, ∀ r < p, μ (histR+k*p+r) = (rightCount k r : ℤ))
    (hcountBoundL : ∀ k < K, ∀ r < p, leftCount k r ≤ V)
    (hcountBoundR : ∀ k < K, ∀ r < p, rightCount k r ≤ V) :
    Meets lim P pMain d
      [J,L,h,p,cap,occ,maps,candidates,histL,histR,mask,dst,bitBase,rowOut,work]
      μ (time J L U) (fun _ ν =>
        ν dst = (product (LightSourceTrim.rowFlag L h p cap sel candidate
          (LightMaskBits.bit (J*L) mask) w0 w1 leftCount) J : ℤ) ∧
        ν (dst+1) = (product (LightSourceTrim.rowFlag L h p cap sel candidate
          (LightMaskBits.bit (J*L) mask) w1 w0 rightCount) J : ℤ) ∧
        KeptBut μ ν bitBase dst 2) := by
  have hspaceBits : work+(J*L+1) ≤ lim.space :=
    (Nat.add_le_add_left (le_max_left _ _) work).trans hspace
  have hspaceTrim : LightSourceRowFlag.space work L U ≤ lim.space := by
    have hh := (Nat.add_le_add_left (le_max_right (J*L+1) (3+(Nat.log 2 (L*U+1)+2))) work).trans hspace
    simpa only [LightSourceRowFlag.space,Nat.add_assoc] using hh
  have hwordBits : ((2^(J*L+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : 2^(J*L+1) ≤ word J L p U V cap := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwordTrim : (LightSourceRowFlag.word L p U V cap : ℤ) ≤ lim.word := by
    have hh : LightSourceRowFlag.word L p U V cap ≤ word J L p U V cap := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwidth : (J : ℤ)*(L : ℤ) ≤ lim.word := by
    exact (by exact_mod_cast (show J*L ≤ lim.space by omega) :
      (J : ℤ)*(L : ℤ) ≤ lim.space).trans hw
  apply Meets.of_body S.main
  unfold body time
  have hb := LightMaskBits.meets (d := d+1) (μ := μ) (L := J*L) (m := mask)
    (dst := bitBase) (work := work) S.bits S.powers S.erase hw (by omega) hspaceBits
    (by omega) hwordBits hmask
  light_call hb using LightMaskBits.time,LightMaskErase.time,LightSourceTrim.time,
    LightSourceRowFlag.time,LightSourceRowScan.time,LightResidues.residueBudget,LightSourceFlagTest.time
    with r ν₁ ⟨bitsRead,_,kept₁⟩
  have hkeep : Kept μ ν₁ bitBase := by
    intro a ha
    exact kept₁ a ⟨by omega,Or.inl ha⟩
  have hoccRead₁ : ∀ j < J, ν₁ (occ+j) = (sel j : ℤ) := by
    intro j hj
    exact (hkeep _ (by omega)).trans (hoccRead j hj)
  have hcandRead₁ : ∀ s < M, ν₁ (candidates+s) = (candidate s : ℤ) := by
    intro s hs
    exact (hkeep _ (by omega)).trans (hcandidateRead s hs)
  have hread0₁ : ∀ s < M, ∀ a < L, ν₁ (maps+2*L*s+a) = (w0 s a : ℤ) := by
    intro s hs a ha
    have he := Nat.mul_le_mul_left (2*L) (show s+1 ≤ M by omega)
    exact (hkeep _ (by nlinarith)).trans (hread0 s hs a ha)
  have hread1₁ : ∀ s < M, ∀ a < L, ν₁ (maps+2*L*s+L+a) = (w1 s a : ℤ) := by
    intro s hs a ha
    have he := Nat.mul_le_mul_left (2*L) (show s+1 ≤ M by omega)
    exact (hkeep _ (by nlinarith)).trans (hread1 s hs a ha)
  have hcountL₁ : ∀ k < K, ∀ r < p, ν₁ (histL+k*p+r) = (leftCount k r : ℤ) := by
    intro k hk r hr
    have he := Nat.mul_le_mul_right p (show k+1 ≤ K by omega)
    exact (hkeep _ (by nlinarith)).trans (hcountL k hk r hr)
  have hcountR₁ : ∀ k < K, ∀ r < p, ν₁ (histR+k*p+r) = (rightCount k r : ℤ) := by
    intro k hk r hr
    have he := Nat.mul_le_mul_right p (show k+1 ≤ K by omega)
    exact (hkeep _ (by nlinarith)).trans (hcountR k hk r hr)
  have ht := S.trim.meets (d := d+1) (μ := ν₁) (J := J) (L := L) (h := h)
    (p := p) (cap := cap) (occ := occ) (maps := maps) (candidates := candidates)
    (histL := histL) (histR := histR) (bitBase := bitBase) (rowOut := rowOut)
    (work := work) (dst := dst) (U := U) (V := V) (M := M) (K := K)
    sel candidate (LightMaskBits.bit (J*L) mask) w0 w1 leftCount rightCount
    hw (by omega) hp hh (by omega) (by omega) (by omega) (by omega) (by omega)
    hbits hrowOut (by omega) hspaceTrim hwordTrim hsel hcandidate hoccRead₁ hcandRead₁
    bitsRead (fun i _ => LightMaskBits.bit_le _ _ i) hread0₁ hread1₁ hbound0 hbound1
    hcountL₁ hcountR₁ hcountBoundL hcountBoundR
  light_call ht using LightMaskBits.time,LightMaskErase.time,LightSourceTrim.time,
    LightSourceRowFlag.time,LightSourceRowScan.time,LightResidues.residueBudget,LightSourceFlagTest.time
    with r ν₂ ⟨left,right,kept₂⟩
  refine ⟨left,right,?_⟩
  intro a ⟨ha,hout⟩
  exact (kept₂ a ⟨by omega,hout⟩).trans (hkeep a ha)

def program : Program :=
  [body 1 4,LightMaskBits.body 2 3,powTableBody,LightMaskErase.body 3,
    LightSourceTrim.body 5,LightSourceRowFlag.body 6 7 8,LightSourceRowScan.body,
    emodBody,LightSourceFlagTest.body]

def programProcs : Procs program 0 :=
  ⟨1,2,3,4,rfl,rfl,rfl,⟨5,6,7,8,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩

theorem time_bound (J L U : ℕ) :
    time J L U ≤ 300*(J*L+1)^2+
      J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+200 := by
  have hb := LightMaskBits.time_bound (J*L)
  have ht := LightSourceTrim.time_bound J L U
  unfold time
  omega

end ThreeSum.LightSourceMaskFlags
