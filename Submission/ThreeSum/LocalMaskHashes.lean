import Submission.ThreeSum.LocalMaskGraph
import Submission.ThreeSum.LightHashHistogram
import Submission.ThreeSum.LightResidueHistogram

/-!
# Exact hash codes and bucket counts for enumerated local vertices

The finite graph used in the moment proof is identified with the literal
mask list consumed by the machine.  In particular, the machine histogram
counts exactly the graph's endpoint buckets, including multiplicities.
-/

namespace ThreeSum.LocalMaskHashes

open Finset LocalMaskGraph LocalHashMoments LocalCoverBounds

variable {h L k : ℕ}

def coeff (b : Bool) (w : Weight L (LocalField h)) : ℕ → ℕ :=
  OneHotMask.extend (fun i => (w (i,b)).val)

theorem coeff_lt (b : Bool) (w : Weight L (LocalField h)) {i : ℕ} (hi : i < L) :
    coeff b w i < localPrime h := by
  simp only [coeff,OneHotMask.extend,hi, dite_true]
  exact ZMod.val_lt _

def leftCode (w : Weight L (LocalField h)) (k i : ℕ) : ℕ :=
  LightHashHistogram.code L (localPrime h) (maskAt L k) (coeff false w) (coeff true w) i

def rightCode (w : Weight L (LocalField h)) (k i : ℕ) : ℕ :=
  LightHashHistogram.code L (localPrime h) (maskAt L k) (coeff true w) (coeff false w) i

theorem leftCode_lt (w : Weight L (LocalField h)) (k i : ℕ) :
    leftCode w k i < localPrime h := by
  unfold leftCode LightHashHistogram.code
  exact LightResidues.residue_lt (localPrime_pos h) 1 _

theorem rightCode_lt (w : Weight L (LocalField h)) (k i : ℕ) :
    rightCode w k i < localPrime h := by
  unfold rightCode LightHashHistogram.code
  exact LightResidues.residue_lt (localPrime_pos h) 1 _

theorem leftCode_cast (w : Weight L (LocalField h)) {i : ℕ}
    (hi : i < LocalMaskGraph.vertexCount L k) :
    (leftCode w k i : LocalField h) =
      HashFamily.hashValue w (LocalGraph.leftWord (setAt L k i)) := by
  unfold leftCode LightHashHistogram.code coeff
  rw [LightResidueHistogram.residue_zmod (localPrime_pos h),one_mul,
    ← subsetMask_setAt hi,OneHotMask.eval_rawLeft,GlobalEncoding.rawHash_cast]

theorem rightCode_cast (w : Weight L (LocalField h)) {i : ℕ}
    (hi : i < LocalMaskGraph.vertexCount L k) :
    (rightCode w k i : LocalField h) =
      HashFamily.hashValue w (LocalGraph.rightWord (setAt L k i)) := by
  unfold rightCode LightHashHistogram.code coeff
  rw [LightResidueHistogram.residue_zmod (localPrime_pos h),one_mul,
    ← subsetMask_setAt hi,OneHotMask.eval_rawRight,GlobalEncoding.rawHash_cast]

theorem leftCode_val (w : Weight L (LocalField h)) {i : ℕ}
    (hi : i < LocalMaskGraph.vertexCount L k) :
    leftCode w k i = (HashFamily.hashValue w (LocalGraph.leftWord (setAt L k i))).val := by
  have he := congrArg ZMod.val (leftCode_cast w hi)
  simpa only [ZMod.val_natCast_of_lt (leftCode_lt w k i)] using he

theorem rightCode_val (w : Weight L (LocalField h)) {i : ℕ}
    (hi : i < LocalMaskGraph.vertexCount L k) :
    rightCode w k i = (HashFamily.hashValue w (LocalGraph.rightWord (setAt L k i))).val := by
  have he := congrArg ZMod.val (rightCode_cast w hi)
  simpa only [ZMod.val_natCast_of_lt (rightCode_lt w k i)] using he

theorem indexed_bucket_count (w : Weight L (LocalField h))
    (shape : Finset (Fin L) → (Fin L → Bool)) (hinj : Function.Injective shape)
    (code : ℕ → ℕ)
    (hcodeLt : ∀ i < LocalMaskGraph.vertexCount L k, code i < localPrime h)
    (hcode : ∀ i < LocalMaskGraph.vertexCount L k,
      (code i : LocalField h) = HashFamily.hashValue w (shape (setAt L k i)))
    {r : ℕ} (hr : r < localPrime h) :
    LightHistogram.count code r (LocalMaskGraph.vertexCount L k) =
      HashFamily.bucketSize ((LayerCounts.vertices L k).image shape) w (r : LocalField h) := by
  unfold LightHistogram.count HashFamily.bucketSize
  apply card_bij (fun i _ => shape (setAt L k i))
  · intro i hi
    obtain ⟨hi,hci⟩ := mem_filter.mp hi
    have hi' := mem_range.mp hi
    refine mem_filter.mpr ⟨mem_image.mpr ⟨setAt L k i,
      LayerCounts.mem_vertices.mpr (setAt_card hi'),rfl⟩,?_⟩
    rw [← hcode i hi',hci]
  · intro i hi j hj he
    exact setAt_injective (mem_range.mp (mem_filter.mp hi).1)
      (mem_range.mp (mem_filter.mp hj).1) (hinj he)
  · intro s hs
    obtain ⟨hs,hhash⟩ := mem_filter.mp hs
    obtain ⟨S,hS,rfl⟩ := mem_image.mp hs
    obtain ⟨i,hi,he⟩ := setAt_complete S (LayerCounts.mem_vertices.mp hS)
    have hcast : (code i : LocalField h) = (r : LocalField h) := by
      rw [hcode i hi,he]
      exact hhash
    have hci : code i = r := by
      have hv := congrArg ZMod.val hcast
      simpa only [ZMod.val_natCast_of_lt (hcodeLt i hi),ZMod.val_natCast_of_lt hr] using hv
    exact ⟨i,mem_filter.mpr ⟨mem_range.mpr hi,hci⟩,congrArg shape he⟩

theorem left_count (w : Weight L (LocalField h)) {r : ℕ} (hr : r < localPrime h) :
    LightHistogram.count (leftCode w k) r (LocalMaskGraph.vertexCount L k) =
      HashFamily.bucketSize (LocalGraph.leftVertices L k) w (r : LocalField h) :=
  indexed_bucket_count w LocalGraph.leftWord LocalGraph.leftWord_injective
    (leftCode w k) (fun i _ => leftCode_lt w k i) (fun _ hi => leftCode_cast w hi) hr

theorem right_count (w : Weight L (LocalField h)) {r : ℕ} (hr : r < localPrime h) :
    LightHistogram.count (rightCode w k) r (LocalMaskGraph.vertexCount L k) =
      HashFamily.bucketSize (LocalGraph.rightVertices L k) w (r : LocalField h) :=
  indexed_bucket_count w LocalGraph.rightWord LocalGraph.rightWord_injective
    (rightCode w k) (fun i _ => rightCode_lt w k i) (fun _ hi => rightCode_cast w hi) hr

end ThreeSum.LocalMaskHashes
