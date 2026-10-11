import Submission.ThreeSum.LightSourceBuild
import Submission.ThreeSum.LightBlockSourceHashes

/-!
# Original block-source multiplicities from the costed constructor

These contracts specialize the actual histogram-and-gather program to the
unchanged block encoding. Endpoint bounds follow from the constructed
coefficient rows; they are not extra semantic assumptions about the encoder.
The original input enumeration explicitly retains individual incidences.
-/

namespace ThreeSum.LightBlockSourceBuild

open Light BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds

set_option maxHeartbeats 1500000

def endpointBound (h J : ℕ) : ℕ := J*(512*h)*(localPrime h^J*localPrime h)

theorem flat_bound {h J : ℕ} (o : Occurrences h J) (b : Bool) {i : ℕ}
    (hi : i < J*(512*h)) :
    flat J (512*h) (localPrime h) (occurrenceIndices o) (mapRow h b) i ≤
      localPrime h^J*localPrime h := by
  exact flat_le (localPrime_pos h) (fun _ hj => occurrenceIndices_lt o hj)
    (fun _ hs _ hk => mapRow_le b hs hk) hi

theorem endpointLeft_abs_le {h J : ℕ} (o : Occurrences h J)
    (S : Finset (BlockRows.Coord J (512*h))) :
    |endpointLeft o S| ≤ (endpointBound h J : ℤ) := by
  rw [← eval_left o S,Int.abs_natCast]
  exact Int.ofNat_le.mpr (OneHotMask.eval_le
    (fun _ hi => flat_bound o false hi) (fun _ hi => flat_bound o true hi))

theorem endpointRight_abs_le {h J : ℕ} (o : Occurrences h J)
    (S : Finset (BlockRows.Coord J (512*h))) :
    |endpointRight o S| ≤ (endpointBound h J : ℤ) := by
  rw [← eval_right o S,Int.abs_natCast]
  exact Int.ofNat_le.mpr (OneHotMask.eval_le
    (fun _ hi => flat_bound o true hi) (fun _ hi => flat_bound o false hi))

theorem left_value {β : Type*} [DecidableEq β] {h J N : ℕ}
    (o : Occurrences h J) (p : ℕ) (B : Finset β) (b : β → ℤ)
    (sets : ℕ → Finset (BlockRows.Coord J (512*h))) (values : ℕ → ℤ)
    (e : Fin N ≃ B) (hvalues : ∀ i : Fin N, values i.val = b (e i)) (i : ℕ) :
    LightSourceGather.value (modulus h J) (fun i => endpointLeft o (sets i))
      (fun i => if LeftAllowed o (sets i) then 1 else 0)
      (fun r => LightHistogram.count
        (fun j => LightSourceResidues.key p (modulus h J) 0 (values j)) r N) i =
      leftWeights o (p : ℤ) B b (sets i) := by
  rw [leftWeights_eq_histogram o p B b (sets i) values e hvalues]
  unfold LightSourceGather.value
  by_cases ha : LeftAllowed o (sets i) <;> simp [ha]

theorem right_value {β : Type*} [DecidableEq β] {h J N : ℕ}
    (o : Occurrences h J) (p : ℕ) (shift : ℤ) (C : Finset β) (c : β → ℤ)
    (sets : ℕ → Finset (BlockRows.Coord J (512*h))) (values : ℕ → ℤ)
    (e : Fin N ≃ C) (hvalues : ∀ i : Fin N, values i.val = c (e i)) (i : ℕ) :
    LightSourceGather.value (modulus h J) (fun i => endpointRight o (sets i))
      (fun i => if RightAllowed o (sets i) then 1 else 0)
      (fun r => LightHistogram.count
        (fun j => LightSourceResidues.key p (modulus h J) shift (values j)) r N) i =
      rightWeights o (p : ℤ) shift C c (sets i) := by
  rw [rightWeights_eq_histogram o p shift C c (sets i) values e hvalues]
  unfold LightSourceGather.value
  by_cases ha : RightAllowed o (sets i) <;> simp [ha]

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets_left {β : Type*} [DecidableEq β] {pMain : ℕ}
    (S : LightSourceBuild.Procs P pMain)
    {μ : ℕ → ℤ} {h J src N raw flags n p hist dst codes work U : ℕ}
    (o : Occurrences h J) (B : Finset β) (b : β → ℤ)
    (sets : ℕ → Finset (BlockRows.Coord J (512*h))) (e : Fin N ≃ B)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth) (hp : 0 < p)
    (hsrc : src+N ≤ hist) (hraw : raw+n ≤ hist) (hflags : flags+n ≤ hist)
    (hhist : hist+modulus h J ≤ dst) (hdst : dst+n ≤ codes) (hcodes : codes+N ≤ work)
    (hspace : LightSourceBuild.space work p U 0 (endpointBound h J) ≤ lim.space)
    (hword : (LightSourceBuild.word p (modulus h J) U 0 (endpointBound h J) : ℤ) ≤ lim.word)
    (hvalues : ∀ i < N, |μ (src+i)| ≤ (U : ℤ))
    (hinput : ∀ i : Fin N, μ (src+i.val) = b (e i))
    (hrawRead : ∀ i < n, μ (raw+i) = endpointLeft o (sets i))
    (hflagRead : ∀ i < n, μ (flags+i) = (if LeftAllowed o (sets i) then 1 else 0 : ℕ)) :
    Meets lim P pMain d [src,N,raw,flags,n,p,modulus h J,hist,dst,codes,work,0]
      μ (LightSourceBuild.time N n p (modulus h J) U 0 (endpointBound h J))
      (fun _ ν => (∀ i < n, ν (dst+i) = (leftWeights o (p : ℤ) B b (sets i) : ℤ)) ∧
        Kept μ ν hist) := by
  have run := S.meets (d := d) (μ := μ) (src := src) (N := N) (raw := raw)
    (flags := flags) (n := n) (p := p) (m := modulus h J) (hist := hist) (dst := dst)
    (codes := codes) (work := work) (U := U) (D := 0) (E := endpointBound h J) (shift := 0)
    (fun i => endpointLeft o (sets i)) (fun i => if LeftAllowed o (sets i) then 1 else 0)
    hw hd hp (modulus_pos h J) hsrc hraw hflags hhist hdst hcodes hspace (by simp)
    hword hvalues hrawRead (fun i _ => endpointLeft_abs_le o (sets i)) hflagRead
    (fun i _ => by split <;> omega)
  refine run.mono le_rfl ?_
  rintro r ν ⟨out,_,kept⟩
  refine ⟨?_,kept⟩
  intro i hi
  rw [out i hi,left_value o p B b sets (fun j => μ (src+j)) e hinput i]

theorem meets_right {β : Type*} [DecidableEq β] {pMain : ℕ}
    (S : LightSourceBuild.Procs P pMain)
    {μ : ℕ → ℤ} {h J src N raw flags n p hist dst codes work U D : ℕ} {shift : ℤ}
    (o : Occurrences h J) (C : Finset β) (c : β → ℤ)
    (sets : ℕ → Finset (BlockRows.Coord J (512*h))) (e : Fin N ≃ C)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth) (hp : 0 < p)
    (hsrc : src+N ≤ hist) (hraw : raw+n ≤ hist) (hflags : flags+n ≤ hist)
    (hhist : hist+modulus h J ≤ dst) (hdst : dst+n ≤ codes) (hcodes : codes+N ≤ work)
    (hspace : LightSourceBuild.space work p U D (endpointBound h J) ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ))
    (hword : (LightSourceBuild.word p (modulus h J) U D (endpointBound h J) : ℤ) ≤ lim.word)
    (hvalues : ∀ i < N, |μ (src+i)| ≤ (U : ℤ))
    (hinput : ∀ i : Fin N, μ (src+i.val) = c (e i))
    (hrawRead : ∀ i < n, μ (raw+i) = endpointRight o (sets i))
    (hflagRead : ∀ i < n, μ (flags+i) = (if RightAllowed o (sets i) then 1 else 0 : ℕ)) :
    Meets lim P pMain d [src,N,raw,flags,n,p,modulus h J,hist,dst,codes,work,shift]
      μ (LightSourceBuild.time N n p (modulus h J) U D (endpointBound h J))
      (fun _ ν => (∀ i < n, ν (dst+i) = (rightWeights o (p : ℤ) shift C c (sets i) : ℤ)) ∧
        Kept μ ν hist) := by
  have run := S.meets (d := d) (μ := μ) (src := src) (N := N) (raw := raw)
    (flags := flags) (n := n) (p := p) (m := modulus h J) (hist := hist) (dst := dst)
    (codes := codes) (work := work) (U := U) (D := D) (E := endpointBound h J) (shift := shift)
    (fun i => endpointRight o (sets i)) (fun i => if RightAllowed o (sets i) then 1 else 0)
    hw hd hp (modulus_pos h J) hsrc hraw hflags hhist hdst hcodes hspace hshift
    hword hvalues hrawRead (fun i _ => endpointRight_abs_le o (sets i)) hflagRead
    (fun i _ => by split <;> omega)
  refine run.mono le_rfl ?_
  rintro r ν ⟨out,_,kept⟩
  refine ⟨?_,kept⟩
  intro i hi
  rw [out i hi,right_value o p shift C c sets (fun j => μ (src+j)) e hinput i]

end ThreeSum.LightBlockSourceBuild
