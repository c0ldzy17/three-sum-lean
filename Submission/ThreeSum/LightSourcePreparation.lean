import Submission.ThreeSum.LightBlockSourceHashes
import Submission.ThreeSum.LightSourceFlagArray

/-!
# Actual endpoint and independent-flag preparation from stored selected maps

The host constructs radix coefficient rows, both raw endpoint arrays, and
both independent trim-flag arrays. All four arrays are retained for the
original-input histogram/source-stage constructors.
-/

namespace ThreeSum.LightSourcePreparation

open Light BlockCoefficientRows

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

/-- Arguments: J, L, required row size, local prime, cap; occurrence/maps/
candidate/table pointers; mask array/count; coefficient rows, raw arrays,
paired flag arrays, and reusable scratch. -/
def body (pHashes pFlags : ℕ) : Stmt :=
  .call pHashes [v 0,v 1,v 3,v 5,v 6,v 12,v 13,v 10,v 14,v 15,v 11,v 19] 20 ;;
  .call pFlags [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 16,v 17,v 18,v 19] 20

def time (n J L U : ℕ) : ℕ :=
  LightBlockSourceHashes.time J L n+LightSourceFlagArray.time n J L U+200

def word (J L p U V cap : ℕ) : ℕ :=
  LightBlockSourceHashes.word J L p U+LightSourceMaskFlags.word J L p U V cap

def space (work J L U : ℕ) : ℕ :=
  max (LightBlockSourceHashes.space work J L) (LightSourceMaskFlags.space work J L U)

structure Procs (P : Program) (pMain : ℕ) where
  pHashes : ℕ
  pFlags : ℕ
  hashes : LightBlockSourceHashes.Procs P pHashes
  flags : LightSourceFlagArray.Procs P pFlags
  main : P[pMain]? = some (body pHashes pFlags)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {J L h p cap occ maps candidates histL histR masks n coeff0 coeff1 rawLeft rawRight flags
      bitBase rowOut work U V M K : ℕ}
    (sel candidate mask : ℕ → ℕ) (w0 w1 leftCount rightCount : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*L+5 ≤ lim.depth)
    (hp : 0 < p) (hh : h ≤ L)
    (hocc : occ+J ≤ coeff0) (hmaps : maps+2*L*M ≤ coeff0)
    (hcandidates : candidates+M ≤ coeff0)
    (hleft : histL+K*p ≤ coeff0) (hright : histR+K*p ≤ coeff0)
    (hmasks : masks+n ≤ coeff0) (hc0 : coeff0+J*L ≤ coeff1)
    (hc1 : coeff1+J*L ≤ rawLeft) (hrawLeft : rawLeft+n ≤ rawRight)
    (hrawRight : rawRight+n ≤ flags) (hflags : flags+2*n+2 ≤ bitBase)
    (hbits : bitBase+J*L ≤ rowOut) (hrowOut : rowOut+2 ≤ work)
    (hspace : space work J L U ≤ lim.space)
    (hword : (word J L p U V cap : ℤ) ≤ lim.word)
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
    (hcountBoundR : ∀ k < K, ∀ r < p, rightCount k r ≤ V)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskBound : ∀ i < n, mask i < 2^(J*L)) :
    Meets lim P pMain d
      [J,L,h,p,cap,occ,maps,candidates,histL,histR,masks,n,coeff0,coeff1,rawLeft,rawRight,
        flags,bitBase,rowOut,work]
      μ (time n J L U) (fun _ ν =>
        (∀ i < n, ν (rawLeft+i) =
          (OneHotMask.eval (flat J L p sel w0) (flat J L p sel w1) (J*L) (mask i) : ℤ)) ∧
        (∀ i < n, ν (rawRight+i) =
          (OneHotMask.eval (flat J L p sel w1) (flat J L p sel w0) (J*L) (mask i) : ℤ)) ∧
        (∀ i < n, ν (flags+i) =
          (LightSourceFlagArray.flag J L h p cap sel candidate w0 w1 leftCount (mask i) : ℤ)) ∧
        (∀ i < n, ν (flags+n+i) =
          (LightSourceFlagArray.flag J L h p cap sel candidate w1 w0 rightCount (mask i) : ℤ)) ∧
        Kept μ ν coeff0) := by
  have hsHash : LightBlockSourceHashes.space work J L ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hsFlag : LightSourceMaskFlags.space work J L U ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hwHash : (LightBlockSourceHashes.word J L p U : ℤ) ≤ lim.word := by
    have hh : LightBlockSourceHashes.word J L p U ≤ word J L p U V cap := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwFlag : (LightSourceMaskFlags.word J L p U V cap : ℤ) ≤ lim.word := by
    have hh : LightSourceMaskFlags.word J L p U V cap ≤ word J L p U V cap := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  apply Meets.of_body C.main
  unfold body time
  have hhash := C.hashes.meets (d := d+1) (μ := μ) (J := J) (L := L) (p := p)
    (occ := occ) (maps := maps) (coeff0 := coeff0) (coeff1 := coeff1) (masks := masks)
    (rawLeft := rawLeft) (rawRight := rawRight) (n := n) (work := work) (U := U) (M := M)
    sel mask w0 w1 hw hp (by omega) hsHash hocc hmaps hmasks hc0 hc1 hrawLeft (by omega)
    hwHash hsel hoccRead hread0 hread1 hbound0 hbound1 hmaskRead hmaskBound
  light_call hhash using LightBlockSourceHashes.time,LightBlockCoefficients.time,
    LightBlockCoefficients.roundTime,LightMaskHashes.time,LightOneHot.time,LightScaleArray.time,
    LightSourceFlagArray.time,LightSourceMaskFlags.time,LightMaskBits.time,
    LightSourceTrim.time,LightSourceRowFlag.time with r ν₁ ⟨rawL,rawR,rows,kept₁⟩
  have hocc' : ∀ j < J, ν₁ (occ+j) = (sel j : ℤ) := by
    intro j hj
    exact (kept₁ _ (by omega)).trans (hoccRead j hj)
  have hcan' : ∀ s < M, ν₁ (candidates+s) = (candidate s : ℤ) := by
    intro s hs
    exact (kept₁ _ (by omega)).trans (hcandidateRead s hs)
  have hread0' : ∀ s < M, ∀ a < L, ν₁ (maps+2*L*s+a) = (w0 s a : ℤ) := by
    intro s hs a ha
    have he := Nat.mul_le_mul_left (2*L) (show s+1 ≤ M by omega)
    exact (kept₁ _ (by nlinarith)).trans (hread0 s hs a ha)
  have hread1' : ∀ s < M, ∀ a < L, ν₁ (maps+2*L*s+L+a) = (w1 s a : ℤ) := by
    intro s hs a ha
    have he := Nat.mul_le_mul_left (2*L) (show s+1 ≤ M by omega)
    exact (kept₁ _ (by nlinarith)).trans (hread1 s hs a ha)
  have hcountL' : ∀ k < K, ∀ r < p, ν₁ (histL+k*p+r) = (leftCount k r : ℤ) := by
    intro k hk r hr
    have he := Nat.mul_le_mul_right p (show k+1 ≤ K by omega)
    exact (kept₁ _ (by nlinarith)).trans (hcountL k hk r hr)
  have hcountR' : ∀ k < K, ∀ r < p, ν₁ (histR+k*p+r) = (rightCount k r : ℤ) := by
    intro k hk r hr
    have he := Nat.mul_le_mul_right p (show k+1 ≤ K by omega)
    exact (kept₁ _ (by nlinarith)).trans (hcountR k hk r hr)
  have hmask' : ∀ i < n, ν₁ (masks+i) = (mask i : ℤ) := by
    intro i hi
    exact (kept₁ _ (by omega)).trans (hmaskRead i hi)
  have hf := C.flags.meets (d := d+1) (μ := ν₁) (J := J) (L := L) (h := h) (p := p)
    (cap := cap) (occ := occ) (maps := maps) (candidates := candidates)
    (histL := histL) (histR := histR) (masks := masks) (n := n) (dst := flags)
    (bitBase := bitBase) (rowOut := rowOut) (work := work) (U := U) (V := V) (M := M) (K := K)
    sel candidate mask w0 w1 leftCount rightCount hw (by omega) hp hh
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    hflags hbits hrowOut hsFlag hwFlag hsel hcandidate hocc' hcan' hread0' hread1'
    hbound0 hbound1 hcountL' hcountR' hcountBoundL hcountBoundR hmask' hmaskBound
  light_call hf using LightBlockSourceHashes.time,LightBlockCoefficients.time,
    LightBlockCoefficients.roundTime,LightMaskHashes.time,LightOneHot.time,LightScaleArray.time,
    LightSourceFlagArray.time,LightSourceMaskFlags.time,LightMaskBits.time,
    LightSourceTrim.time,LightSourceRowFlag.time with r ν₂ ⟨leftFlags,rightFlags,kept₂⟩
  refine ⟨?_,?_,leftFlags,rightFlags,?_⟩
  · intro i hi
    exact (kept₂ _ ⟨by omega,Or.inl (by omega)⟩).trans (rawL i hi)
  · intro i hi
    exact (kept₂ _ ⟨by omega,Or.inl (by omega)⟩).trans (rawR i hi)
  · intro a ha
    exact (kept₂ a ⟨by omega,Or.inl (by omega)⟩).trans (kept₁ a ha)

def program : Program :=
  [body 1 7,LightBlockSourceHashes.body 2 5,LightBlockCoefficients.body 3 4,
    powTableBody,LightScaleArray.body,LightMaskHashes.body 3 6,LightOneHot.body 6,
    LightSourceFlagArray.body 8,LightSourceMaskFlags.body 9 12,
    LightMaskBits.body 10 11,powTableBody,LightMaskErase.body 11,
    LightSourceTrim.body 13,LightSourceRowFlag.body 14 15 16,LightSourceRowScan.body,
    emodBody,LightSourceFlagTest.body]

def programProcs : Procs program 0 :=
  ⟨1,7,⟨2,3,4,5,6,rfl,rfl,rfl,rfl,rfl,rfl⟩,
    ⟨8,⟨9,10,11,12,rfl,rfl,rfl,⟨13,14,15,16,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩

theorem time_bound (n J L U : ℕ) :
    time n J L U ≤ 300*(J+1)*(L+1)+600*(J*L+1)*(n+1)+
      n*(300*(J*L+1)^2+J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+400)+410 := by
  have hh := LightBlockSourceHashes.time_bound J L n
  have hf := LightSourceFlagArray.time_bound n J L U
  unfold time
  omega

end ThreeSum.LightSourcePreparation
