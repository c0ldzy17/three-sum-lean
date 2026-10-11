import Submission.ThreeSum.LightBlockSourceRetainedStages
import Submission.ThreeSum.LightBlockSourcePreparation
import Submission.ThreeSum.LightDownsetEnumerationSetup
import Submission.ThreeSum.BlockSourceCoverInput

/-!
# Per-occurrence source construction with shared band histograms

For a fixed band pair, modulus, and common offset, this host constructs its
own compact masks, coefficient rows, endpoint arrays, and independent flags.
It then gathers from the retained band histograms and constructs both exact
original suffix-stage families. Histogram scans belong outside this loop.
-/

namespace ThreeSum.LightBlockSourceRetainedHost

open Light BlockEncoding GlobalEncoding BlockIndex BlockCoefficientRows
open SubsetAddress LightSubsetAddress LightPascal LocalCoverBounds BlockSourceFlags
open BlockSourceEncoding LightBlockSourceBuild

set_option maxHeartbeats 4000000
set_option maxRecDepth 14000

def body (pEnum pPrepare pStages : ℕ) : Stmt :=
  .call pEnum [v 0 *' v 1,v 5,v 14,v 25] 26 ;;
  .call pPrepare [v 0,v 1,v 2,v 3,v 4,v 7,v 8,v 9,v 10,v 11,v 14,v 26,
    v 15,v 16,v 17,v 18,v 19,v 23,v 24,v 25] 27 ;;
  .call pStages [v 17,v 19,v 12,v 20,v 6,v 25,v 0 *' v 1,v 5,v 22,v 26] 27 ;;
  .call pStages [v 18,v 19 +' v 26,v 13,v 21,v 6,v 25,v 0 *' v 1,v 5,v 22,v 26] 27

def time (h J cut : ℕ) : ℕ :=
  LightDownsetEnumerationSetup.time (J*(512*h)) cut+
  LightSourcePreparation.time (downsetCap (J*(512*h)) cut) J (512*h) (localPrime h)+
  LightSourceRetainedStages.time (J*(512*h)) cut (endpointBound h J)+
  LightSourceRetainedStages.time (J*(512*h)) cut (endpointBound h J)+500

def space (work h J : ℕ) : ℕ :=
  max (work+(J*(512*h)+1))
    (max (LightSourcePreparation.space work J (512*h) (localPrime h))
      (LightSourceRetainedStages.space work (J*(512*h)) (endpointBound h J)))

def word (NL NR h J : ℕ) : ℕ :=
  2^(J*(512*h)+1)+
  LightSourcePreparation.word J (512*h) (localPrime h) (localPrime h)
    ((512*h).choose h) (localBucketCap h)+
  LightSourceRetainedStages.word (J*(512*h)) (modulus h J) (endpointBound h J) NL+
  LightSourceRetainedStages.word (J*(512*h)) (modulus h J) (endpointBound h J) NR

structure Procs (P : Program) (pMain : ℕ) where
  pEnum : ℕ
  pPowers : ℕ
  pDownset : ℕ
  pLayer : ℕ
  pPrepare : ℕ
  pStages : ℕ
  enumMain : P[pEnum]? = some (LightDownsetEnumerationSetup.body pPowers pDownset)
  powers : P[pPowers]? = some powTableBody
  downset : P[pDownset]? = some (LightDownsetEnumeration.body pLayer)
  layer : P[pLayer]? = some (LightSubsetEnumeration.body pLayer)
  prepare : LightSourcePreparation.Procs P pPrepare
  stages : LightSourceRetainedStages.Procs P pStages
  main : P[pMain]? = some (body pEnum pPrepare pStages)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {h J cut p NL NR occ maps candidates histL histR sourceHistL sourceHistR
      masks coeff0 coeff1 rawLeft rawRight flags baseL baseR maskBase bitBase rowOut work : ℕ}
    {shift : ℤ} (B : Finset β) (b : β → ℤ) (A : Finset γ) (a : γ → ℤ)
    (q : GlobalOutput h J) (vL vR : ℕ → ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ A)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+9 ≤ lim.depth)
    (hcut : cut ≤ J*(512*h))
    (hocc : occ+J ≤ masks) (hmaps : maps+2*(512*h)*scheduleSize h ≤ masks)
    (hcandidates : candidates+scheduleSize h ≤ masks)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h ≤ masks)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h ≤ masks)
    (hsourceHistL : sourceHistL+modulus h J ≤ masks)
    (hsourceHistR : sourceHistR+modulus h J ≤ masks)
    (hmasks : masks+downsetCap (J*(512*h)) cut ≤ coeff0)
    (hc0 : coeff0+J*(512*h) ≤ coeff1) (hc1 : coeff1+J*(512*h) ≤ rawLeft)
    (hrawLeft : rawLeft+downsetCap (J*(512*h)) cut ≤ rawRight)
    (hrawRight : rawRight+downsetCap (J*(512*h)) cut ≤ flags)
    (hflags : flags+2*downsetCap (J*(512*h)) cut+2 ≤ baseL)
    (hbaseL : baseL+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ baseR)
    (hbaseR : baseR+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ maskBase)
    (hmaskBase : maskBase+downsetCap (J*(512*h)) cut ≤ bitBase)
    (hbits : bitBase+J*(512*h) ≤ rowOut) (hrowOut : rowOut+2 ≤ work)
    (hspace : space work h J ≤ lim.space)
    (hword : (word NL NR h J : ℤ) ≤ lim.word)
    (hinputL : ∀ i : Fin NL, vL i.val = b (eL i))
    (hinputR : ∀ i : Fin NR, vR i.val = a (eR i))
    (hhistReadL : ∀ r < modulus h J,
      μ (sourceHistL+r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) 0 vL NL r : ℤ))
    (hhistReadR : ∀ r < modulus h J,
      μ (sourceHistR+r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) shift vR NR r : ℤ))
    (hoccRead : ∀ j < J, μ (occ+j) = (occurrenceIndices (outputOccurrences q) j : ℤ))
    (hcover : BlockSourceCoverInput.Input μ h maps candidates histL histR) :
    Meets lim P pMain d
      [J,512*h,h,localPrime h,localBucketCap h,cut,modulus h J,occ,maps,candidates,
        histL,histR,sourceHistL,sourceHistR,masks,coeff0,coeff1,rawLeft,rawRight,flags,
        baseL,baseR,maskBase,bitBase,rowOut,work]
      μ (time h J cut) (fun _ ν =>
        LightZetaStages.StoredThrough ν baseL cut (BlockIndexedQuery.leftSource (p : ℤ) B b q) (J*(512*h)) ∧
        LightZetaStages.StoredThrough ν baseR cut (BlockIndexedQuery.rightSource (p : ℤ) shift A a q) (J*(512*h)) ∧
        Kept μ ν masks) := by
  have hsEnum : work+(J*(512*h)+1) ≤ lim.space := (le_max_left _ _).trans hspace
  have hsRest := (le_max_right _ _).trans hspace
  have hsPrep : LightSourcePreparation.space work J (512*h) (localPrime h) ≤ lim.space :=
    (le_max_left _ _).trans hsRest
  have hsStages : LightSourceRetainedStages.space work (J*(512*h)) (endpointBound h J) ≤ lim.space :=
    (le_max_right _ _).trans hsRest
  have hwEnum : ((2^(J*(512*h)+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : 2^(J*(512*h)+1) ≤ word NL NR h J :=
      (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwPrep : (LightSourcePreparation.word J (512*h) (localPrime h) (localPrime h)
      ((512*h).choose h) (localBucketCap h) : ℤ) ≤ lim.word := by
    have hh : LightSourcePreparation.word J (512*h) (localPrime h) (localPrime h)
        ((512*h).choose h) (localBucketCap h) ≤ word NL NR h J :=
      (Nat.le_add_left _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwLeft : (LightSourceRetainedStages.word (J*(512*h)) (modulus h J) (endpointBound h J) NL : ℤ) ≤ lim.word := by
    have hh : LightSourceRetainedStages.word (J*(512*h)) (modulus h J) (endpointBound h J) NL ≤
        word NL NR h J := (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwRight : (LightSourceRetainedStages.word (J*(512*h)) (modulus h J) (endpointBound h J) NR : ℤ) ≤ lim.word := by
    have hh : LightSourceRetainedStages.word (J*(512*h)) (modulus h J) (endpointBound h J) NR ≤
        word NL NR h J := Nat.le_add_left _ _
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwidth : (J : ℤ)*(512*(h : ℤ)) ≤ lim.word := by
    exact (by exact_mod_cast (show J*(512*h) ≤ lim.space by omega) :
      (J : ℤ)*(512*(h : ℤ)) ≤ lim.space).trans hw
  have hwidthNonneg : (0 : ℤ) ≤ (J : ℤ)*(512*(h : ℤ)) := by positivity
  apply Meets.of_body C.main
  unfold body time
  have he := LightDownsetEnumerationSetup.meets (d := d+1) (μ := μ) (L := J*(512*h))
    (cut := cut) (dst := masks) (work := work) C.enumMain C.powers C.downset C.layer
    hw hsEnum hwEnum hcut (by omega) (by omega)
  light_call he using LightDownsetEnumerationSetup.time,LightDownsetEnumeration.time,
    LightSourcePreparation.time,LightSourceRetainedStages.time with count ν₁ ⟨hcount,hseg,_,kept₁⟩
  subst count
  have keptEnum : Kept μ ν₁ masks := by
    intro x hx
    exact kept₁ x ⟨by omega,Or.inl hx⟩
  have hcover' := hcover.of_kept keptEnum hmaps hcandidates hleft hright
  have hocc' : ∀ j < J, ν₁ (occ+j) = (occurrenceIndices (outputOccurrences q) j : ℤ) := by
    intro j hj
    exact (keptEnum _ (by omega)).trans (hoccRead j hj)
  have hmaskRead : ∀ i < downsetCap (J*(512*h)) cut,
      ν₁ (masks+i) = (subsetMask (indexSet (BlockSourceTableLayout.sets h J cut i)) : ℤ) := by
    intro i hi
    rw [BlockSourceTableLayout.mask_sets hi,SourceTableLayout.maskAt,
      List.getD_eq_getElem _ _ (by simpa only [enumerateDownset_length] using hi)]
    exact hseg.getElem (by simpa only [enumerateDownset_length] using hi)
  have hpRun := LightBlockSourcePreparation.meets (d := d+1) (μ := ν₁) C.prepare
    (occ := occ) (maps := maps) (candidates := candidates) (histL := histL) (histR := histR)
    (masks := masks) (n := downsetCap (J*(512*h)) cut) (coeff0 := coeff0) (coeff1 := coeff1)
    (rawLeft := rawLeft) (rawRight := rawRight) (flags := flags) (bitBase := bitBase)
    (rowOut := rowOut) (work := work) (outputOccurrences q) (BlockSourceTableLayout.sets h J cut)
    hw (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hmasks hc0 hc1
    hrawLeft hrawRight (by omega) hbits hrowOut hsPrep hwPrep hocc'
    hcover'.candidates hcover'.leftRows hcover'.rightRows hcover'.leftCounts hcover'.rightCounts hmaskRead
  light_call hpRun using LightDownsetEnumerationSetup.time,LightDownsetEnumeration.time,
    LightSourcePreparation.time,LightSourceRetainedStages.time with r ν₂ ⟨rawL,rawR,flagL,flagR,kept₂⟩
  have keptPrep : Kept μ ν₂ masks := by
    intro x hx
    exact (kept₂ x (by omega)).trans (keptEnum x hx)
  have hhL : ∀ r < modulus h J,
      ν₂ (sourceHistL+r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) 0 vL NL r : ℤ) := by
    intro r hr
    exact (keptPrep _ (by omega)).trans (hhistReadL r hr)
  have hlRun := LightBlockSourceRetainedStages.meets_left (d := d+1) (μ := ν₂) C.stages
    (N := NL) (raw := rawLeft) (flags := flags) (p := p) (table := sourceHistL)
    (base := baseL) (work := work) (cut := cut) (maskBase := maskBase)
    B b q vL eL hw (by omega) hcut (by omega) (by omega) (by omega) (by omega)
    (by omega) hsStages hwLeft hinputL hhL rawL flagL
  light_call hlRun using LightDownsetEnumerationSetup.time,LightDownsetEnumeration.time,
    LightSourcePreparation.time,LightSourceRetainedStages.time with r ν₃ ⟨storedL,kept₃⟩
  have keptLeft : Kept μ ν₃ masks := by
    intro x hx
    exact (kept₃ x (by omega)).trans (keptPrep x hx)
  have hhR : ∀ r < modulus h J,
      ν₃ (sourceHistR+r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) shift vR NR r : ℤ) := by
    intro r hr
    exact (keptLeft _ (by omega)).trans (hhistReadR r hr)
  have rawR' : ∀ i < downsetCap (J*(512*h)) cut,
      ν₃ (rawRight+i) = endpointRight (outputOccurrences q) (BlockSourceTableLayout.sets h J cut i) := by
    intro i hi
    exact (kept₃ _ (by omega)).trans (rawR i hi)
  have flagR' : ∀ i < downsetCap (J*(512*h)) cut,
      ν₃ (flags+downsetCap (J*(512*h)) cut+i) =
        (if RightAllowed (outputOccurrences q) (BlockSourceTableLayout.sets h J cut i) then 1 else 0 : ℕ) := by
    intro i hi
    exact (kept₃ _ (by omega)).trans (flagR i hi)
  have hrRun := LightBlockSourceRetainedStages.meets_right (d := d+1) (μ := ν₃) C.stages
    (N := NR) (raw := rawRight) (flags := flags+downsetCap (J*(512*h)) cut) (p := p)
    (table := sourceHistR) (base := baseR) (work := work) (cut := cut) (maskBase := maskBase)
    A a q vR eR hw (by omega) hcut (by omega) (by omega) (by omega) hbaseR
    (by omega) hsStages hwRight hinputR hhR rawR' flagR'
  light_call hrRun using LightDownsetEnumerationSetup.time,LightDownsetEnumeration.time,
    LightSourcePreparation.time,LightSourceRetainedStages.time with r ν₄ ⟨storedR,kept₄⟩
  refine ⟨?_,storedR,?_⟩
  · intro j hj S hS
    have hr := subsetRank_lt hS
    have hmul := Nat.mul_le_mul_right (downsetCap (J*(512*h)) cut) (Nat.succ_le_succ hj)
    have haddr : LightZetaStages.stageBase baseL (downsetCap (J*(512*h)) cut) j+subsetRank S < baseR := by
      calc
        LightZetaStages.stageBase baseL (downsetCap (J*(512*h)) cut) j+subsetRank S
            < baseL+j*downsetCap (J*(512*h)) cut+downsetCap (J*(512*h)) cut :=
          Nat.add_lt_add_left hr _
        _ = baseL+(j+1)*downsetCap (J*(512*h)) cut := by ring
        _ ≤ baseL+(J*(512*h)+1)*downsetCap (J*(512*h)) cut := Nat.add_le_add_left hmul _
        _ ≤ baseR := hbaseL
    exact (kept₄ _ haddr).trans (storedL j hj S hS)
  · intro x hx
    exact (kept₄ x (by omega)).trans (keptLeft x hx)

end ThreeSum.LightBlockSourceRetainedHost
