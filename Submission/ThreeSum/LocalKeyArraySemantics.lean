import Submission.ThreeSum.OutputKeyMasks
import Submission.ThreeSum.LightLocalKeys

/-!
# Exact local-output array semantics

The physical occurrence-major rows are the same list of original records
used by the verified global radix product constructor.
-/

namespace ThreeSum.LocalKeyArraySemantics

open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open Light

set_option maxHeartbeats 1800000

theorem seg_flatMap_rows {α : Type*} {μ : ℕ → ℤ} (xs : List α)
    (f : α → List ℤ) (n dst : ℕ)
    (hlen : ∀ x ∈ xs, (f x).length=n)
    (hread : ∀ (j : ℕ) (hj : j < xs.length) (i : ℕ) (hi : i < n),
      μ (dst+j*n+i)=(f xs[j])[i]'(by rw [hlen _ (List.getElem_mem hj)]; exact hi)) :
    Seg μ dst (xs.flatMap f) := by
  induction xs generalizing dst with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons]
    apply seg_append.mpr
    constructor
    · intro i hi
      have hin : i < n := by rw [hlen x (by simp)] at hi; exact hi
      have hh := hread 0 (by simp) i hin
      change μ (dst+0*n+i)=(f x)[i] at hh
      simpa only [Nat.zero_mul,Nat.add_zero] using hh
    · rw [hlen x (by simp)]
      apply ih (dst+n) (fun a ha => hlen a (by simp [ha]))
      intro j hj i hi
      have hh := hread (j+1) (by simpa using hj) i hi
      simpa only [List.getElem_cons_succ,show dst+(j+1)*n+i=dst+n+j*n+i by ring] using hh

theorem localKeys_eq_flatMap (h : ℕ) :
    localKeys h = (List.finRange (scheduleSize h)).flatMap
      (fun o => List.ofFn (fun i => blockKey (o,layerRecord h i))) := by
  simp only [localKeys,localRecords,List.product,List.map_flatMap,List.map_map,
    layers,List.map_ofFn,Function.comp_def]

theorem seg_localKeys {h dst : ℕ} {μ : ℕ → ℤ}
    (hout : ∀ j < scheduleSize h, ∀ i < outputCount (512*h) h,
      μ (dst+j*outputCount (512*h) h+i)=
        (OneHotMask.eval (BlockCoefficientRows.mapRow h true j) (fun _ => 0) (512*h)
          (LocalMaskGraph.maskAt (512*h) (2*h) i) : ℤ)-
        (OneHotMask.eval (BlockCoefficientRows.mapRow h false j) (fun _ => 0) (512*h)
          (LocalMaskGraph.maskAt (512*h) (2*h) i) : ℤ)) :
    Seg μ dst (localKeys h) := by
  rw [localKeys_eq_flatMap]
  apply seg_flatMap_rows _ _ (outputCount (512*h) h) dst (by simp [outputCount])
  intro j hj i hi
  have hj' : j < scheduleSize h := by simpa only [List.length_finRange] using hj
  rw [hout j hj' i hi]
  have he := OutputKeyMasks.indexed_blockKey ⟨j,hj'⟩ ⟨i,hi⟩
  have ho : (List.finRange (scheduleSize h))[j]=⟨j,hj'⟩ := by
    apply Fin.ext
    simp
  simpa only [List.getElem_ofFn,ho] using he

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets_original {pMain h masks maps dst free : ℕ} {μ : ℕ → ℤ}
    (S : LightLocalKeys.Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+3 ≤ lim.depth)
    (hspace : LightLocalKeyRow.space free (512*h) (outputCount (512*h) h) ≤ lim.space)
    (hmasks : masks+outputCount (512*h) h ≤ dst)
    (hmaps : maps+scheduleSize h*(2*(512*h)) ≤ dst)
    (hdst : dst+scheduleSize h*outputCount (512*h) h ≤ free)
    (hword : (LightLocalKeys.word (512*h) (localPrime h) (scheduleSize h) : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < outputCount (512*h) h,
      μ (masks+i)=(LocalMaskGraph.maskAt (512*h) (2*h) i : ℤ))
    (hreadFalse : ∀ j < scheduleSize h, ∀ i < 512*h,
      μ (maps+j*(2*(512*h))+i)=(BlockCoefficientRows.mapRow h false j i : ℤ))
    (hreadTrue : ∀ j < scheduleSize h, ∀ i < 512*h,
      μ (maps+j*(2*(512*h))+512*h+i)=(BlockCoefficientRows.mapRow h true j i : ℤ)) :
    Meets lim P pMain d [512*h,masks,outputCount (512*h) h,maps,scheduleSize h,dst,free] μ
      (LightLocalKeys.time (512*h) (outputCount (512*h) h) (scheduleSize h))
      (fun _ ν => Seg ν dst (localKeys h) ∧ Kept μ ν dst) := by
  apply (S.meets (U := localPrime h) (LocalMaskGraph.maskAt (512*h) (2*h))
    (BlockCoefficientRows.mapRow h false) (BlockCoefficientRows.mapRow h true)
    hw hd hspace hmasks hmaps hdst hword hmaskRead
    (fun i hi => (LocalMaskGraph.maskAt_spec hi).1) hreadFalse hreadTrue
    (fun j hj i hi => BlockCoefficientRows.mapRow_le false hj hi)
    (fun j hj i hi => BlockCoefficientRows.mapRow_le true hj hi)).mono le_rfl
  intro r ν ⟨hout,hkeep⟩
  exact ⟨seg_localKeys hout,hkeep⟩

end ThreeSum.LocalKeyArraySemantics
