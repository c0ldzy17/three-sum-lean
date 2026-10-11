import Submission.ThreeSum.SourceFiniteData

/-! # Actual source construction from the retained prepared outputs -/

namespace ThreeSum.LightSourceFinitePrepared

open Light GlobalEncoding LocalCoverBounds BlockSourceEncoding SourceFiniteInputs

def args (free base bv be cv ce g p h J cut len : ℕ) : List ℤ :=
  [J,512*h,h,localPrime h,localBucketCap h,cut,modulus h J,
    maps free h,candidates free h,leftCounts free h,rightCounts free h,
    bv,be,cv,ce,g,p,LightGuardedWanted.wantedFree free h J len+3,base,scheduleSize h]

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain : ℕ} (R : LightSourceControlsHost.Procs P pMain)
    {μ : ℕ → ℤ} {free base bv be cv ce g p h J cut U M : ℕ} [NeZero M]
    {hg : 0 < g} {originalB originalC B C xs : List ℤ}
    {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+16 ≤ lim.depth)
    (hp : 0 < p) (hcut : cut ≤ J*(512*h))
    (hbv : bv+originalB.length ≤ base) (hcv : cv+originalC.length ≤ base)
    (hbe : be+2 ≤ base) (hce : ce+2 ≤ base)
    (hshiftCell : LightGuardedWanted.wantedFree free h J xs.length+3 < base)
    (hspace : LightSourceControlsHost.space base B.length C.length g p h J cut U M ≤ lim.space)
    (hword : (LightSourceControlsHost.word B.length C.length g p h J cut U M : ℤ) ≤ lim.word)
    (hB : LightBandPreprocessing.Represents μ bv be g hg originalB B hsB)
    (hC : LightBandPreprocessing.Represents μ cv ce g hg originalC C hsC)
    (hboundB : ∀ z ∈ originalB, |z| ≤ (U : ℤ)) (hboundC : ∀ z ∈ originalC, |z| ≤ (U : ℤ))
    (hcover : LightCoverKeyData.Stored μ free h J)
    (hwanted : LightWantedSetup.Output μ (LightGuardedWanted.wantedFree free h J xs.length) M
      (LightGuardedWanted.left p xs) (LightGuardedWanted.right h J)
      (3*xs.length) (LightGuardedWanted.totalKeys h J) (RawAKeyLists.selected M p xs h J)) :
    Meets lim P pMain d (args free base bv be cv ce g p h J cut xs.length) μ
      (LightSourceControlsHost.time B.length C.length g p h J cut U M)
      (fun r ν => SourceFiniteData.Stored ν base g p h J cut B C
        (RawAKeyLists.selected M p xs h J : ℤ) r ∧ LightCoverKeyData.Stored ν free h J ∧ Kept μ ν base) := by
  have hkey : LightCoverKeyData.keyEnd free h J ≤ base := by
    unfold LightGuardedWanted.wantedFree at hshiftCell
    omega
  obtain ⟨hmaps,hcandidates,hleft,hright⟩ := cover_ends free h J
  obtain ⟨hlenB,hcountB⟩ := prepared_headers hB
  obtain ⟨hlenC,hcountC⟩ := prepared_headers hC
  have H := R.meets (μ := μ) (srcL := bv) (headL := be) (srcR := cv) (headR := ce)
    (shiftCell := LightGuardedWanted.wantedFree free h J xs.length+3) (base := base)
    (NL := B.length) (NR := C.length) (g := g) (p := p) (h := h) (J := J) (cut := cut) (U := U) (D := M)
    (maps := maps free h) (candidates := candidates free h) (histL := leftCounts free h) (histR := rightCounts free h)
    (shift := (RawAKeyLists.selected M p xs h J : ℤ)) (fun j => B.getD j 0) (fun j => C.getD j 0)
    hw hd hg hp hcut (by have hl := hB.2.1; omega) (by have hl := hC.2.1; omega)
    hbe hce hshiftCell (hmaps.trans hkey) (hcandidates.trans hkey) (hleft.trans hkey) (hright.trans hkey)
    hspace hword (selected_abs_le M p h J xs) hlenB hlenC hcountB hcountC
    (wanted_shift_read hwanted) (prepared_read hB) (prepared_read hC)
    (prepared_bound hB hboundB) (prepared_bound hC hboundC) (cover_input hcover)
  apply H.mono le_rfl
  intro r ν ⟨hr,hcontrols,hbuckets,hbanks,hkeep⟩
  exact ⟨⟨hr,hcontrols,hbuckets,hbanks⟩,hcover.of_kept (fun a ha => hkeep a (ha.trans_le hkey)),hkeep⟩

end ThreeSum.LightSourceFinitePrepared
