import Submission.ThreeSum.LocalMaskHashes
import Submission.ThreeSum.LightPairFlags
import Submission.ThreeSum.LightSupportMark

/-!
# The literal cover-matrix entry is the retained-edge predicate

This identifies the actual all-pairs, histogram-trimmed support table with
the same `Covers` relation used by the finite moment and greedy proof.
-/

namespace ThreeSum.LocalCoverMatrix

open Finset LocalHashMoments LocalCoverBounds LocalMaskGraph LocalMaskHashes

variable {h L k : ℕ}

def bits (L k i : ℕ) : ℕ → ℕ := LightMaskBits.bit L (maskAt L k i)
def leftCount (w : Weight L (LocalField h)) (k : ℕ) : ℕ → ℕ :=
  fun r => LightHistogram.count (leftCode w k) r (LocalMaskGraph.vertexCount L k)
def rightCount (w : Weight L (LocalField h)) (k : ℕ) : ℕ → ℕ :=
  fun r => LightHistogram.count (rightCode w k) r (LocalMaskGraph.vertexCount L k)
def key (w : Weight L (LocalField h)) (k : ℕ) : ℕ → ℕ :=
  LightPairFlags.pairKey (LocalMaskGraph.vertexCount L k) (localPrime h)
    (leftCode w k) (rightCode w k)
def valid (w : Weight L (LocalField h)) (k B : ℕ) : ℕ → ℕ :=
  LightPairFlags.pairFlag L (LocalMaskGraph.vertexCount L k) B (bits L k)
    (leftCode w k) (rightCode w k) (leftCount w k) (rightCount w k)
def entry (w : Weight L (LocalField h)) (k B r : ℕ) : ℕ :=
  LightSupportMark.bit (key w k) (valid w k B) r
    (LocalMaskGraph.vertexCount L k*LocalMaskGraph.vertexCount L k)

theorem entry_le (w : Weight L (LocalField h)) (k B r : ℕ) : entry w k B r ≤ 1 := by
  unfold entry LightSupportMark.bit
  split <;> omega

theorem radix_div {p a b : ℕ} (hb : b < p) : (a*p+b)/p=a := by
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by omega),Nat.div_eq_of_lt hb]
  omega

theorem radix_mod {p a b : ℕ} (hb : b < p) : (a*p+b)%p=b := by
  rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hb]

theorem radix_injective {p a b c e : ℕ} (hb : b < p) (he : e < p)
    (hh : a*p+b=c*p+e) : a=c ∧ b=e := by
  exact ⟨by simpa only [radix_div hb,radix_div he] using congrArg (fun j => j/p) hh,
    by simpa only [radix_mod hb,radix_mod he] using congrArg (fun j => j%p) hh⟩

theorem covers_iff_edge (w : Weight L (LocalField h)) (k B : ℕ)
    (a b : LocalField h) :
    Covers L k B w (a,b) ↔ ∃ e : LocalGraph.Edge L k,
      HashFamily.hashValue w (LocalGraph.left e)=a ∧
      HashFamily.hashValue w (LocalGraph.right e)=b ∧
      HashFamily.bucketSize (LocalGraph.leftVertices L k) w a ≤ B ∧
      HashFamily.bucketSize (LocalGraph.rightVertices L k) w b ≤ B := by
  constructor
  · exact cover_has_edge
  · rintro ⟨e,ha,hb,hleft,hright⟩
    apply Nat.ne_of_gt
    apply Finset.card_pos.mpr
    refine ⟨e,?_⟩
    simp only [HashFamily.trimmedPairEvent,
      HashFamily.pairEvent,mem_filter,mem_univ,true_and]
    exact ⟨⟨ha,hb⟩,hleft,hright⟩

theorem valid_iff (w : Weight L (LocalField h)) {B i : ℕ}
    (hi : i < LocalMaskGraph.vertexCount L k*LocalMaskGraph.vertexCount L k) :
    valid w k B i=1 ↔
      Disjoint (setAt L k (i/LocalMaskGraph.vertexCount L k))
        (setAt L k (i%LocalMaskGraph.vertexCount L k)) ∧
      leftCount w k (leftCode w k (i/LocalMaskGraph.vertexCount L k)) ≤ B ∧
      rightCount w k (rightCode w k (i%LocalMaskGraph.vertexCount L k)) ≤ B := by
  have hn : 0 < LocalMaskGraph.vertexCount L k := by nlinarith
  have hq : i/LocalMaskGraph.vertexCount L k < LocalMaskGraph.vertexCount L k :=
    (Nat.div_lt_iff_lt_mul hn).mpr hi
  have hr := Nat.mod_lt i hn
  unfold valid LightPairFlags.pairFlag bits
  rw [LightTrimTest.flag_eq_one,indexed_dot_zero_iff hq hr]

theorem entry_eq_one_iff (w : Weight L (LocalField h)) {B a b : ℕ}
    (ha : a < localPrime h) (hb : b < localPrime h) :
    entry w k B (a*localPrime h+b)=1 ↔
      Covers L k B w ((a : LocalField h),(b : LocalField h)) := by
  have hbit : entry w k B (a*localPrime h+b)=1 ↔
      LightSupportMark.Hit (key w k) (valid w k B) (a*localPrime h+b)
        (LocalMaskGraph.vertexCount L k*LocalMaskGraph.vertexCount L k) := by
    unfold entry LightSupportMark.bit
    split <;> simp_all
  rw [hbit,covers_iff_edge]
  constructor
  · rintro ⟨i,hi,hvalid,hkey⟩
    have hi' := mem_range.mp hi
    have hn : 0 < LocalMaskGraph.vertexCount L k := by nlinarith
    have hq : i/LocalMaskGraph.vertexCount L k < LocalMaskGraph.vertexCount L k :=
      (Nat.div_lt_iff_lt_mul hn).mpr hi'
    have hr := Nat.mod_lt i hn
    obtain ⟨hdisj,hleft,hright⟩ := (valid_iff w hi').mp hvalid
    obtain ⟨hca,hcb⟩ := radix_injective (rightCode_lt w k _) hb hkey
    let e : LocalGraph.Edge L k :=
      ⟨(setAt L k (i/LocalMaskGraph.vertexCount L k),
        setAt L k (i%LocalMaskGraph.vertexCount L k)),
        LayerCounts.mem_edgeSet.mpr ⟨setAt_card hq,setAt_card hr,hdisj⟩⟩
    refine ⟨e,?_,?_,?_,?_⟩
    · exact (leftCode_cast w hq).symm.trans (congrArg (fun n : ℕ => (n : LocalField h)) hca)
    · exact (rightCode_cast w hr).symm.trans (congrArg (fun n : ℕ => (n : LocalField h)) hcb)
    · change LightHistogram.count _ _ _ ≤ B at hleft
      rw [hca,left_count w ha] at hleft
      exact hleft
    · change LightHistogram.count _ _ _ ≤ B at hright
      rw [hcb,right_count w hb] at hright
      exact hright
  · rintro ⟨e,hleftHash,hrightHash,hleft,hright⟩
    obtain ⟨i,hi,hei⟩ := setAt_complete e.val.1 (LocalGraph.edge_data e).1
    obtain ⟨j,hj,hej⟩ := setAt_complete e.val.2 (LocalGraph.edge_data e).2.1
    have hn : 0 < LocalMaskGraph.vertexCount L k := by omega
    have hidx : i*LocalMaskGraph.vertexCount L k+j <
        LocalMaskGraph.vertexCount L k*LocalMaskGraph.vertexCount L k := by nlinarith
    have hq := radix_div hj (a := i)
    have hr := radix_mod hj (a := i)
    have hca : leftCode w k i=a := by
      rw [leftCode_val w hi,hei]
      change (HashFamily.hashValue w (LocalGraph.left e)).val=a
      rw [hleftHash,ZMod.val_natCast_of_lt ha]
    have hcb : rightCode w k j=b := by
      rw [rightCode_val w hj,hej]
      change (HashFamily.hashValue w (LocalGraph.right e)).val=b
      rw [hrightHash,ZMod.val_natCast_of_lt hb]
    refine ⟨i*LocalMaskGraph.vertexCount L k+j,mem_range.mpr hidx,?_,?_⟩
    · rw [valid_iff w hidx,hq,hr,hei,hej,hca,hcb]
      refine ⟨(LocalGraph.edge_data e).2.2,?_,?_⟩
      · simpa only [leftCount,left_count w ha] using hleft
      · simpa only [rightCount,right_count w hb] using hright
    · unfold key LightPairFlags.pairKey
      rw [hq,hr,hca,hcb]

end ThreeSum.LocalCoverMatrix
