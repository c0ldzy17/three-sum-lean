import Submission.ThreeSum.LightSourceMaskFlags

/-!
# Constructing contiguous arrays of independent source flags

The actual loop reads the already enumerated global masks. For each one it
constructs both independent flags from selected maps and retained bucket
counts, then writes the two orientations in separate adjacent arrays. Powers,
Boolean coordinates and local arithmetic scratch are reused across masks.
-/

namespace ThreeSum.LightSourceFlagArray

open Light SourceFlagProduct

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000

def flag (J L h p cap : ℕ) (sel candidate : ℕ → ℕ)
    (w0 w1 counts : ℕ → ℕ → ℕ) (mask : ℕ) : ℕ :=
  product (LightSourceTrim.rowFlag L h p cap sel candidate
    (LightMaskBits.bit (J*L) mask) w0 w1 counts) J

theorem flag_le (J L h p cap : ℕ) (sel candidate : ℕ → ℕ)
    (w0 w1 counts : ℕ → ℕ → ℕ) (mask : ℕ) :
    flag J L h p cap sel candidate w0 w1 counts mask ≤ 1 :=
  product_le _ (fun _ _ => LightSourceTrim.rowFlag_le ..) le_rfl

/-- Arguments: the same map/table inputs as the single-mask program, followed
by mask array, mask count, paired-array output, and three scratch pointers. -/
def body (pFlag : ℕ) : Stmt :=
  .for 16 (v 11) (
    .call pFlag [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,
      M (v 10 +' v 16),v 12 +' k 2 *' v 11,v 13,v 14,v 15] 17 ;;
    .store (v 12 +' v 16) (M (v 12 +' k 2 *' v 11)) ;;
    .store (v 12 +' v 11 +' v 16) (M (v 12 +' k 2 *' v 11 +' k 1)))

def time (n J L U : ℕ) : ℕ := n*(LightSourceMaskFlags.time J L U+200)+10

structure Procs (P : Program) (pMain : ℕ) where
  pFlag : ℕ
  flagProcs : LightSourceMaskFlags.Procs P pFlag
  main : P[pMain]? = some (body pFlag)

def Inv (μ : ℕ → ℤ) (J L h p cap occ maps candidates histL histR masks n dst bitBase rowOut work : ℕ)
    (sel candidate mask : ℕ → ℕ) (w0 w1 leftCount rightCount : ℕ → ℕ → ℕ)
    (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [J,L,h,p,cap,occ,maps,candidates,histL,histR,masks,n,dst,bitBase,rowOut,work,i,r],ν⟩ ∧
    (∀ j < i, ν (dst+j) = (flag J L h p cap sel candidate w0 w1 leftCount (mask j) : ℤ)) ∧
    (∀ j < i, ν (dst+n+j) = (flag J L h p cap sel candidate w1 w0 rightCount (mask j) : ℤ)) ∧
    KeptBut μ ν bitBase dst (2*n+2)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {J L h p cap occ maps candidates histL histR masks n dst bitBase rowOut work U V M K : ℕ}
    (sel candidate mask : ℕ → ℕ) (w0 w1 leftCount rightCount : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*L+4 ≤ lim.depth)
    (hp : 0 < p) (hh : h ≤ L)
    (hocc : occ+J ≤ dst) (hmaps : maps+2*L*M ≤ dst)
    (hcandidates : candidates+M ≤ dst)
    (hleft : histL+K*p ≤ dst) (hright : histR+K*p ≤ dst)
    (hmasks : masks+n ≤ dst) (hdst : dst+2*n+2 ≤ bitBase)
    (hbits : bitBase+J*L ≤ rowOut) (hrowOut : rowOut+2 ≤ work)
    (hspace : LightSourceMaskFlags.space work J L U ≤ lim.space)
    (hword : (LightSourceMaskFlags.word J L p U V cap : ℤ) ≤ lim.word)
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
      [J,L,h,p,cap,occ,maps,candidates,histL,histR,masks,n,dst,bitBase,rowOut,work]
      μ (time n J L U) (fun _ ν =>
        (∀ i < n, ν (dst+i) = (flag J L h p cap sel candidate w0 w1 leftCount (mask i) : ℤ)) ∧
        (∀ i < n, ν (dst+n+i) = (flag J L h p cap sel candidate w1 w0 rightCount (mask i) : ℤ)) ∧
        KeptBut μ ν bitBase dst (2*n+2)) := by
  have hspace' : work ≤ lim.space := by
    unfold LightSourceMaskFlags.space at hspace
    omega
  have hone : (1 : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (show 1 ≤ lim.space by omega)).trans hw
  apply Meets.of_body S.main
  unfold body time
  refine Ends.for (Inv μ J L h p cap occ maps candidates histL histR masks n dst bitBase rowOut work
    sel candidate mask w0 w1 leftCount rightCount) n
    (LightSourceMaskFlags.time J L U+192) ?start ?round ?done ?bound
  case start =>
    refine ⟨0,μ,?_,?_,?_,fun _ _ => rfl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : State))
        ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro j hj; omega
    · intro j hj; omega
  case round =>
    rintro i _ hi _ ⟨r,ν,rfl,leftWritten,rightWritten,kept⟩
    have hkeep : Kept μ ν dst := by
      intro a ha
      exact kept a ⟨by omega,Or.inl ha⟩
    have hocc' : ∀ j < J, ν (occ+j) = (sel j : ℤ) := by
      intro j hj
      exact (hkeep _ (by omega)).trans (hoccRead j hj)
    have hcan' : ∀ s < M, ν (candidates+s) = (candidate s : ℤ) := by
      intro s hs
      exact (hkeep _ (by omega)).trans (hcandidateRead s hs)
    have hread0' : ∀ s < M, ∀ a < L, ν (maps+2*L*s+a) = (w0 s a : ℤ) := by
      intro s hs a ha
      have he := Nat.mul_le_mul_left (2*L) (show s+1 ≤ M by omega)
      exact (hkeep _ (by nlinarith)).trans (hread0 s hs a ha)
    have hread1' : ∀ s < M, ∀ a < L, ν (maps+2*L*s+L+a) = (w1 s a : ℤ) := by
      intro s hs a ha
      have he := Nat.mul_le_mul_left (2*L) (show s+1 ≤ M by omega)
      exact (hkeep _ (by nlinarith)).trans (hread1 s hs a ha)
    have hcountL' : ∀ k < K, ∀ r < p, ν (histL+k*p+r) = (leftCount k r : ℤ) := by
      intro k hk r hr
      have he := Nat.mul_le_mul_right p (show k+1 ≤ K by omega)
      exact (hkeep _ (by nlinarith)).trans (hcountL k hk r hr)
    have hcountR' : ∀ k < K, ∀ r < p, ν (histR+k*p+r) = (rightCount k r : ℤ) := by
      intro k hk r hr
      have he := Nat.mul_le_mul_right p (show k+1 ≤ K by omega)
      exact (hkeep _ (by nlinarith)).trans (hcountR k hk r hr)
    have hmask : ν (masks+i) = (mask i : ℤ) :=
      (hkeep _ (by omega)).trans (hmaskRead i hi)
    have hrun := S.flagProcs.meets (d := d+1) (μ := ν)
      (J := J) (L := L) (h := h) (p := p) (cap := cap) (occ := occ) (maps := maps)
      (candidates := candidates) (histL := histL) (histR := histR) (mask := mask i)
      (dst := dst+2*n) (bitBase := bitBase) (rowOut := rowOut) (work := work)
      (U := U) (V := V) (M := M) (K := K)
      sel candidate w0 w1 leftCount rightCount hw (by omega) hp hh
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hbits hrowOut hspace hword
      (hmaskBound i hi) hsel hcandidate hocc' hcan' hread0' hread1' hbound0 hbound1
      hcountL' hcountR' hcountBoundL hcountBoundR
    light_call hrun using hmask,LightSourceMaskFlags.time,LightMaskBits.time,
      LightMaskErase.time,LightSourceTrim.time,LightSourceRowFlag.time,LightSourceRowScan.time,
      LightResidues.residueBudget,LightSourceFlagTest.time
      with q ν₁ ⟨left,right,kept₁⟩
    have hl : ν₁ (dst+2*n) = (flag J L h p cap sel candidate w0 w1 leftCount (mask i) : ℤ) := left
    have hr : ν₁ (dst+2*n+1) = (flag J L h p cap sel candidate w1 w0 rightCount (mask i) : ℤ) := right
    have hlB := flag_le J L h p cap sel candidate w0 w1 leftCount (mask i)
    have hrB := flag_le J L h p cap sel candidate w1 w0 rightCount (mask i)
    have haddr : ((dst : ℤ)+2*(n : ℤ)).toNat = dst+2*n := by
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using Int.toNat_natCast (dst+2*n)
    have haddrR : ((dst : ℤ)+2*(n : ℤ)+1).toNat = dst+2*n+1 := by
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using Int.toNat_natCast (dst+2*n+1)
    light_store (dst+i) (flag J L h p cap sel candidate w0 w1 leftCount (mask i) : ℕ)
      using hl,haddr,LightSourceMaskFlags.time,LightMaskBits.time,LightMaskErase.time,LightSourceTrim.time,
      LightSourceRowFlag.time,LightSourceRowScan.time,LightResidues.residueBudget,LightSourceFlagTest.time
    have hr' : Function.update ν₁ (dst+i)
        (flag J L h p cap sel candidate w0 w1 leftCount (mask i) : ℤ) (dst+2*n+1) =
        (flag J L h p cap sel candidate w1 w0 rightCount (mask i) : ℤ) := by
      rw [Function.update_of_ne (by omega)]
      exact hr
    light_store (dst+n+i) (flag J L h p cap sel candidate w1 w0 rightCount (mask i) : ℕ)
      using hr',haddrR,LightSourceMaskFlags.time,LightMaskBits.time,LightMaskErase.time,LightSourceTrim.time,
      LightSourceRowFlag.time,LightSourceRowScan.time,LightResidues.residueBudget,LightSourceFlagTest.time
    refine ⟨by simp,q,Function.update
      (Function.update ν₁ (dst+i) (flag J L h p cap sel candidate w0 w1 leftCount (mask i) : ℤ))
      (dst+n+i) (flag J L h p cap sel candidate w1 w0 rightCount (mask i) : ℤ),
      by simp [update_frame_setLocal],?_,?_,?_⟩
    · intro j hj
      rw [Function.update_of_ne (by omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega)]
        exact (kept₁ _ ⟨by omega,Or.inl (by omega)⟩).trans (leftWritten j hj)
      · simp
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
        exact (kept₁ _ ⟨by omega,Or.inl (by omega)⟩).trans (rightWritten j hj)
      · simp
    · intro a ⟨ha,hout⟩
      rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
      exact (kept₁ a ⟨ha,by omega⟩).trans (kept a ⟨ha,hout⟩)
  case done =>
    rintro _ _ ⟨r,ν,rfl,left,right,kept⟩
    exact ⟨left,right,kept⟩
  case bound =>
    rintro i _ _ _ ⟨r,ν,rfl,_,_,_⟩
    simp

def program : Program :=
  [body 1,LightSourceMaskFlags.body 2 5,LightMaskBits.body 3 4,powTableBody,LightMaskErase.body 4,
    LightSourceTrim.body 6,LightSourceRowFlag.body 7 8 9,LightSourceRowScan.body,
    emodBody,LightSourceFlagTest.body]

def programProcs : Procs program 0 :=
  ⟨1,⟨2,3,4,5,rfl,rfl,rfl,⟨6,7,8,9,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩

theorem time_bound (n J L U : ℕ) :
    time n J L U ≤ n*(300*(J*L+1)^2+
      J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+400)+10 := by
  have hh := LightSourceMaskFlags.time_bound J L U
  unfold time
  exact Nat.add_le_add_right (Nat.mul_le_mul_left n (by omega)) 10

end ThreeSum.LightSourceFlagArray
