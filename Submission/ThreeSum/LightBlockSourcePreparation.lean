import Submission.ThreeSum.LightSourcePreparation
import Submission.ThreeSum.BlockSourceFlags

/-!
# All original raw endpoints and independent flags from the actual selected maps

This semantic specialization composes the verified coefficient, endpoint,
row-scan, remainder, bucket lookup, and all-block flag constructions.
-/

namespace ThreeSum.LightBlockSourcePreparation

open Light BlockRows BlockIndex BlockEncoding BlockCoefficientRows BlockSourceFlags
open LocalCoverBounds GlobalEncoding

set_option maxHeartbeats 1700000

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain : ℕ} (C : LightSourcePreparation.Procs P pMain)
    {μ : ℕ → ℤ} {h J occ maps candidates histL histR masks n coeff0 coeff1 rawLeft rawRight flags
      bitBase rowOut work : ℕ}
    (o : Occurrences h J) (sets : ℕ → Finset (Coord J (512*h)))
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+5 ≤ lim.depth)
    (hocc : occ+J ≤ coeff0) (hmaps : maps+2*(512*h)*scheduleSize h ≤ coeff0)
    (hcandidates : candidates+scheduleSize h ≤ coeff0)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h ≤ coeff0)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h ≤ coeff0)
    (hmasks : masks+n ≤ coeff0) (hc0 : coeff0+J*(512*h) ≤ coeff1)
    (hc1 : coeff1+J*(512*h) ≤ rawLeft) (hrawLeft : rawLeft+n ≤ rawRight)
    (hrawRight : rawRight+n ≤ flags) (hflags : flags+2*n+2 ≤ bitBase)
    (hbits : bitBase+J*(512*h) ≤ rowOut) (hrowOut : rowOut+2 ≤ work)
    (hspace : LightSourcePreparation.space work J (512*h) (localPrime h) ≤ lim.space)
    (hword : (LightSourcePreparation.word J (512*h) (localPrime h) (localPrime h)
      ((512*h).choose h) (localBucketCap h) : ℤ) ≤ lim.word)
    (hoccRead : ∀ j < J, μ (occ+j) = (occurrenceIndices o j : ℤ))
    (hcandidateRead : ∀ s : Occurrence h,
      μ (candidates+s.val) = (LightLocalCoverSchedule.candidateAt h s : ℤ))
    (hread0 : ∀ s < scheduleSize h, ∀ a < 512*h,
      μ (maps+2*(512*h)*s+a) = (mapRow h false s a : ℤ))
    (hread1 : ∀ s < scheduleSize h, ∀ a < 512*h,
      μ (maps+2*(512*h)*s+512*h+a) = (mapRow h true s a : ℤ))
    (hcountL : ∀ k < LightLocalCoverSchedule.rows h, ∀ r < localPrime h,
      μ (histL+k*localPrime h+r) = (leftCount h k r : ℤ))
    (hcountR : ∀ k < LightLocalCoverSchedule.rows h, ∀ r < localPrime h,
      μ (histR+k*localPrime h+r) = (rightCount h k r : ℤ))
    (hmaskRead : ∀ i < n,
      μ (masks+i) = (SubsetAddress.subsetMask (indexSet (sets i)) : ℤ)) :
    Meets lim P pMain d
      [J,512*h,h,localPrime h,localBucketCap h,occ,maps,candidates,histL,histR,masks,n,
        coeff0,coeff1,rawLeft,rawRight,flags,bitBase,rowOut,work]
      μ (LightSourcePreparation.time n J (512*h) (localPrime h)) (fun _ ν =>
        (∀ i < n, ν (rawLeft+i) = endpointLeft o (sets i)) ∧
        (∀ i < n, ν (rawRight+i) = endpointRight o (sets i)) ∧
        (∀ i < n, ν (flags+i) = (if LeftAllowed o (sets i) then 1 else 0 : ℕ)) ∧
        (∀ i < n, ν (flags+n+i) = (if RightAllowed o (sets i) then 1 else 0 : ℕ)) ∧
        Kept μ ν coeff0) := by
  have hcandidates' : ∀ s < scheduleSize h, μ (candidates+s) = (candidateIndices h s : ℤ) := by
    intro s hs
    exact hcandidateRead ⟨s,hs⟩
  have hboundL : ∀ k < LightLocalCoverSchedule.rows h, ∀ r < localPrime h,
      leftCount h k r ≤ (512*h).choose h := by
    intro k hk r hr
    exact LightHistogram.count_le _ _ _
  have hboundR : ∀ k < LightLocalCoverSchedule.rows h, ∀ r < localPrime h,
      rightCount h k r ≤ (512*h).choose h := by
    intro k hk r hr
    exact LightHistogram.count_le _ _ _
  have run := C.meets (d := d) (μ := μ) (J := J) (L := 512*h) (h := h)
    (p := localPrime h) (cap := localBucketCap h) (occ := occ) (maps := maps)
    (candidates := candidates) (histL := histL) (histR := histR) (masks := masks) (n := n)
    (coeff0 := coeff0) (coeff1 := coeff1) (rawLeft := rawLeft) (rawRight := rawRight)
    (flags := flags) (bitBase := bitBase) (rowOut := rowOut) (work := work)
    (U := localPrime h) (V := (512*h).choose h) (M := scheduleSize h)
    (K := LightLocalCoverSchedule.rows h)
    (occurrenceIndices o) (candidateIndices h) (fun i => SubsetAddress.subsetMask (indexSet (sets i)))
    (mapRow h false) (mapRow h true) (leftCount h) (rightCount h)
    hw hd (localPrime_pos h) (by omega) hocc hmaps hcandidates hleft hright hmasks hc0 hc1 hrawLeft
    hrawRight hflags hbits hrowOut hspace hword (fun _ hj => occurrenceIndices_lt o hj)
    (fun _ hs => candidateIndices_lt hs) hoccRead hcandidates' hread0 hread1
    (fun _ hs _ ha => mapRow_le false hs ha) (fun _ hs _ ha => mapRow_le true hs ha)
    hcountL hcountR hboundL hboundR hmaskRead
    (fun i _ => (SubsetAddress.subsetMask_isMask (indexSet (sets i))).1)
  refine run.mono le_rfl ?_
  rintro r ν ⟨rawL,rawR,left,right,kept⟩
  exact ⟨fun i hi => (rawL i hi).trans (eval_left o (sets i)),
    fun i hi => (rawR i hi).trans (eval_right o (sets i)),
    fun i hi => (left i hi).trans (congrArg (fun n : ℕ => (n : ℤ)) (left_product o (sets i))),
    fun i hi => (right i hi).trans (congrArg (fun n : ℕ => (n : ℤ)) (right_product o (sets i))),kept⟩

end ThreeSum.LightBlockSourcePreparation
