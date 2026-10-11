import Submission.ThreeSum.LightReportingWantedInitialize

/-!
# The wanted initializer with a retained counter before decoded rows

This is the same actual 42-procedure program. The dense counter and its
threshold precede the per-wanted decoded and packed rows, so the existing
decoder's prefix frame preserves the running state. The postcondition tracks
the exact counter update and preserves every other cell before packed rows.
-/

namespace ThreeSum.LightReportingWantedInitializeSeparated

open Light Finset ThreeSum.SubsetAddress
open BlockRows BlockIndex BlockMaskLayout BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostLevelData ReportingHostFrontierLayout LightReportingWantedInitialize

set_option maxHeartbeats 3800000
set_option maxRecDepth 14000
set_option linter.unusedSectionVars false

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem program_meets {μ : ℕ→ℤ}
    {h J baseL baseR catalogs cover rawRows rows counter root maskBase work old threshold d : ℕ} {D : Catalog}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ) (w : Wanted h J α)
    (hkey : w.1∈A ∧ globalModulus h J ∣ (a w.1%pMod+lift w.2.1*pMod+shift)-globalKey w.2.2)
    (hw : (lim.space : ℤ)≤lim.word)
    (HS : Sources μ pMod shift B C b c w.2.2 baseL baseR)
    (HC : Stored μ D (Nat.zero_le J) pMod shift B C b c w.2.2)
    (HB : Bounds h J 0 D baseL baseR rows)
    (HW : Scratch lim h J 0 D B.card C.card maskBase work)
    (hmeta : SegN μ catalogs (D.record h 0)) (hmetaEnd : catalogs+5≤rows)
    (hgroup : μ (cover+3)=(groupSize h : ℤ)) (hcoverEnd : cover+4≤rows)
    (hraw : rawRows+J≤rows) (hrows : rows+J≤root) (hcounter : counter+2≤rawRows)
    (hout : slot root (capacity (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w) 1≤maskBase)
    (hpackSpace : work+(512*h+1)≤lim.space)
    (hword : ((old+rootMass (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w+threshold+2 : ℕ) : ℤ)≤lim.word)
    (hreadRaw : SegN μ rawRows (rawMasks (outputRows w.2.2)))
    (hcounterRead : μ counter=(old : ℤ)) (hthreshold : μ (counter+1)=(threshold : ℤ))
    (hd : d+2*width h J+16≤lim.depth) :
    Meets lim program 41 d
      [width h J,sourceCut h J,J,512*h,baseL,baseR,catalogs,rawRows,rows,cover,counter,root,maskBase,work]
      μ (time h J D.t)
      (fun result ν =>
        let I := rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c
        result=(if threshold<old+rootMass I w then 1 else 0 : ℤ) ∧
        ν counter=((old+rootMass I w : ℕ) : ℤ) ∧
        At ν I w root (capacity I w) 0 ∧
        ν (root+2)=(rootMass I w : ℤ) ∧ ν (root+3)=(capacity I w : ℤ) ∧
        SegN ν rows (packedMasks (outputRows w.2.2)) ∧ KeptBut μ ν rows counter 1) := by
  let I := rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c
  have hwork := HW.masks
  have hspace := HW.space
  have hout' : root+4+2*capacity I w≤maskBase := by simpa [slot,Nat.add_assoc] using hout
  have hpackWord : ((2^(J*(512*h)+1) : ℕ) : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (Nat.le_mul_of_pos_left _ (by omega))).trans HW.word
  have hthresholdZ : μ (((counter : ℤ)+1).toNat)=(threshold : ℤ) := by
    rw [show ((counter : ℤ)+1).toNat=counter+1 by omega]
    exact hthreshold
  apply Meets.of_body (p := 41) (by rfl : program[41]?=some (body 0 39 40))
  unfold body time
  light_set (threshold : ℕ) using hthreshold,hthresholdZ,LightBlockMasks.time,LightReportingInitializeStored.time,LightDenseGuard.time
  have hpack := (LightBlockMasks.program_meets (μ := μ) (d := d+1) (src := rawRows) (dst := rows) (work := work)
    (outputRows w.2.2) hw (by omega) (by omega) (Or.inl hraw) hpackSpace hpackWord hreadRaw (by omega)).append
      (LightReportingInitializeStored.program.map (ReportingHostRelocation.relocate 2) ++
        LightDenseGuard.program.map (ReportingHostRelocation.relocate 40) ++ [body 0 39 40])
  change Meets lim program 0 (d+1) _ μ (LightBlockMasks.time J (512*h)) _ at hpack
  light_call hpack using LightBlockMasks.time,LightReportingInitializeStored.time,LightDenseGuard.time
    with qmask ν₁ ⟨hQ,hpacked,hkeepPack⟩
  have hkeepPackRows : Kept μ ν₁ rows := by
    intro i hi
    exact hkeepPack i ⟨by omega,Or.inl hi⟩
  have HS₁ := HS.of_kept HB hkeepPackRows
  have HC₁ := HC.of_kept HB hkeepPackRows
  have hmeta₁ : SegN ν₁ catalogs (D.record h 0) := by
    intro i hi
    have hi' : i<5 := by simpa only [Catalog.record,List.length_map,List.length_cons,List.length_nil] using hi
    exact (hkeepPackRows _ (by omega)).trans (hmeta i hi)
  have hgroup₁ : ν₁ (cover+3)=(groupSize h : ℤ) :=
    (hkeepPackRows _ (by omega)).trans hgroup
  have hinit := LightReportingInitializeStored.program_meets (μ := ν₁) (depth := d+1)
    pMod shift A B C a b c w hkey hw HS₁ HC₁ (HB.mono (by omega)) HW
    hmeta₁ (by omega) hgroup₁ (by omega) hout (by omega)
  have hinitRun := (ReportingHostRelocation.meets hinit LightBlockMasks.program).append
    (LightDenseGuard.program.map (ReportingHostRelocation.relocate 40) ++ [body 0 39 40])
  change Meets lim program 39 (d+1) _ ν₁ (LightReportingInitializeStored.time h J D.t) _ at hinitRun
  have hQzero : subsetMask (querySet 0 (outputRows w.2.2))=
      subsetMask (indexSet (flat (outputRows w.2.2))) := by rw [query_zero]
  light_call hinitRun using hQ,hQzero,LightBlockMasks.time,LightReportingInitializeStored.time,LightDenseGuard.time
    with unused ν₂ ⟨_,hfrontier,hmass,hcap,hkeepInit⟩
  change At ν₂ I w root (capacity I w) 0 at hfrontier
  change ν₂ (root+2)=(rootMass I w : ℤ) at hmass
  change ν₂ (root+3)=(capacity I w : ℤ) at hcap
  have hcounter₂ : ν₂ counter=(old : ℤ) := by
    refine (hkeepInit _ (by omega)).trans ?_
    exact (hkeepPackRows _ (by omega)).trans hcounterRead
  have hguard := LightDenseGuard.program_meets (μ := ν₂) (d := d+1)
    hw (by omega) (by omega) hword hcounter₂ hmass
  have hguardRun := (ReportingHostRelocation.meets hguard initialLibraries).append [body 0 39 40]
  change Meets lim program 40 (d+1) _ ν₂ LightDenseGuard.time _ at hguardRun
  light_call hguardRun using LightBlockMasks.time,LightReportingInitializeStored.time,LightDenseGuard.time
    with result ν₃ ⟨hresult,hcounter₃,hkeepGuard⟩
  have hkeepAbove : ∀ i, root ≤ i → ν₃ i=ν₂ i := fun i hi => hkeepGuard i (Or.inr (by omega))
  refine ⟨hresult,hcounter₃,frontier_of_above hfrontier hkeepAbove,
    (hkeepAbove _ (by omega)).trans hmass,(hkeepAbove _ (by omega)).trans hcap,?_,?_⟩
  · intro i hi
    have hi' : i<J := by simpa only [List.length_map,packedMasks_length] using hi
    exact (hkeepGuard _ (Or.inr (by omega))).trans ((hkeepInit _ (by omega)).trans (hpacked i hi))
  · intro i hi
    exact (hkeepGuard _ hi.2).trans
      ((hkeepInit _ (by omega)).trans (hkeepPackRows i hi.1))


end ThreeSum.LightReportingWantedInitializeSeparated
