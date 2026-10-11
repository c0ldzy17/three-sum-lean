import Submission.ThreeSum.LightLocalCoverTransport
import Submission.ThreeSum.LocalCoverMatrix
import Submission.ThreeSum.WeightEnumeration
import Submission.ThreeSum.LightCoverGreedy

/-!
# Exact local schedule occurrence indices

The machine's Boolean matrix uses radix-indexed candidate rows and ordered
residue-pair columns. These changes of representation preserve the entire
original local schedule, including ties and repeated selected maps.
-/

namespace ThreeSum.LightLocalCoverSchedule

open Finset LocalHashMoments LocalCoverBounds GlobalEncoding

def rows (h : ℕ) : ℕ := (localPrime h)^(2*(512*h))
def cols (h : ℕ) : ℕ := localPrime h*localPrime h
def candidate (h i : ℕ) : Weight (512*h) (LocalField h) :=
  WeightEnumeration.decodedWeight (512*h) (localPrime h) i
def target (h r : ℕ) : LocalField h × LocalField h :=
  (((r/localPrime h : ℕ) : LocalField h),((r%localPrime h : ℕ) : LocalField h))
def matrix (h i r : ℕ) : ℕ :=
  LocalCoverMatrix.entry (candidate h i) h (localBucketCap h) r
def indices (h : ℕ) : List ℕ :=
  BooleanGreedy.choices (matrix h) (rows h) (cols h) (scheduleSize h)

theorem rows_pos (h : ℕ) : 0 < rows h := Nat.pow_pos (localPrime_pos h)

theorem target_injective (h : ℕ) : Set.InjOn (target h) (range (cols h)) := by
  intro x hx y hy he
  have hx' : x < localPrime h*localPrime h := mem_range.mp hx
  have hy' : y < localPrime h*localPrime h := mem_range.mp hy
  have hxq := (Nat.div_lt_iff_lt_mul (localPrime_pos h)).mpr hx'
  have hyq := (Nat.div_lt_iff_lt_mul (localPrime_pos h)).mpr hy'
  have hxr := Nat.mod_lt x (localPrime_pos h)
  have hyr := Nat.mod_lt y (localPrime_pos h)
  have hq := congrArg (fun z : LocalField h × LocalField h => z.1.val) he
  have hr := congrArg (fun z : LocalField h × LocalField h => z.2.val) he
  simp only [target,ZMod.val_natCast_of_lt hxq,ZMod.val_natCast_of_lt hyq] at hq
  simp only [target,ZMod.val_natCast_of_lt hxr,ZMod.val_natCast_of_lt hyr] at hr
  have hxsum := Nat.mod_add_div x (localPrime h)
  have hysum := Nat.mod_add_div y (localPrime h)
  rw [hq,hr] at hxsum
  exact hxsum.symm.trans hysum

theorem target_surjective (h : ℕ) (u : LocalField h × LocalField h) :
    ∃ r < cols h, target h r = u := by
  obtain ⟨a,b⟩ := u
  have ha := a.val_lt
  have hb := b.val_lt
  refine ⟨a.val*localPrime h+b.val,?_,?_⟩
  · unfold cols
    nlinarith
  · unfold target
    rw [LocalCoverMatrix.radix_div hb,LocalCoverMatrix.radix_mod hb]
    simp only [ZMod.natCast_zmod_val]

theorem target_image (h : ℕ) : (range (cols h)).image (target h) = univ := by
  ext u
  simp only [mem_univ,iff_true]
  obtain ⟨r,hr,he⟩ := target_surjective h u
  exact mem_image.mpr ⟨r,mem_range.mpr hr,he⟩

theorem matrix_covers (h i : ℕ) {r : ℕ} (hr : r < cols h) :
    BooleanGreedy.covers (matrix h) i r ↔
      Covers (512*h) h (localBucketCap h) (candidate h i) (target h r) := by
  have hq := (Nat.div_lt_iff_lt_mul (localPrime_pos h)).mpr hr
  have hm := Nat.mod_lt r (localPrime_pos h)
  have he := LocalCoverMatrix.entry_eq_one_iff (candidate h i) (k := h) (B := localBucketCap h) hq hm
  have hidx : r/localPrime h*localPrime h+r%localPrime h=r := by
    simpa only [Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div r (localPrime h)
  rw [hidx] at he
  exact he

theorem indices_map (h : ℕ) : (indices h).map (candidate h) = localSchedule h := by
  have hc : candidate h = WeightEnumeration.decodedWeight (K := LocalField h) (512*h) (localPrime h) := by
    funext i
    rfl
  have ht := LightLocalCoverTransport.choices_map (matrix h) (candidate h) (target h)
    (Covers (512*h) h (localBucketCap h)) (rows := rows h) (cols := cols h)
    (rows_pos h) (target_injective h) (fun i _ hr => matrix_covers h i hr) (scheduleSize h)
  rw [target_image] at ht
  rw [hc] at ht ⊢
  rw [WeightEnumeration.localSchedule_eq_radix]
  dsimp only [localBucketCap,bucketBound] at ht ⊢
  simp only [indices,rows,scheduleSize,ZMod.card] at ht ⊢
  convert ht using 1
  congr 1

theorem indices_length (h : ℕ) : (indices h).length = scheduleSize h :=
  BooleanGreedy.choices_length ..

theorem indices_lt (h : ℕ) {i : ℕ} (hi : i ∈ indices h) : i < rows h := by
  have hchoices : ∀ t, ∀ j ∈ BooleanGreedy.choices (matrix h) (rows h) (cols h) t, j < rows h := by
    intro t
    induction t with
    | zero => intro j hj; simp [BooleanGreedy.choices,Cover.greedyChoices] at hj
    | succ t ih =>
      intro j hj
      rw [BooleanGreedy.choices_succ,List.mem_append,List.mem_singleton] at hj
      rcases hj with hj | rfl
      · exact ih j hj
      · exact BooleanGreedy.choice_lt (rows_pos h) t
  exact hchoices _ i hi

def candidateAt (h : ℕ) (s : Occurrence h) : ℕ := (indices h).getD s.val 0

theorem candidateAt_lt (h : ℕ) (s : Occurrence h) : candidateAt h s < rows h := by
  have hs : s.val < (indices h).length := by rw [indices_length]; exact s.isLt
  unfold candidateAt
  rw [List.getD_eq_getElem _ _ hs]
  exact indices_lt h (List.getElem_mem hs)

theorem candidateAt_mapAt (h : ℕ) (s : Occurrence h) :
    candidate h (candidateAt h s) = mapAt h s := by
  have hs : s.val < (indices h).length := by rw [indices_length]; exact s.isLt
  have hs' : s.val < (localSchedule h).length := by
    rw [← scheduleSize_eq_length]
    exact s.isLt
  have he := congrArg (fun xs : List (Weight (512*h) (LocalField h)) => xs.getD s.val default) (indices_map h)
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hs),List.getElem_map,
    List.getD_eq_getElem _ _ hs'] at he
  unfold candidateAt mapAt
  rw [List.getD_eq_getElem _ _ hs]
  exact he

theorem leftCount_candidateAt (h : ℕ) (s : Occurrence h) {r : ℕ} (hr : r < localPrime h) :
    LocalCoverMatrix.leftCount (candidate h (candidateAt h s)) h r =
      HashFamily.bucketSize (LocalGraph.leftVertices (512*h) h) (mapAt h s) (r : LocalField h) := by
  unfold LocalCoverMatrix.leftCount
  rw [LocalMaskHashes.left_count _ hr,candidateAt_mapAt]

theorem rightCount_candidateAt (h : ℕ) (s : Occurrence h) {r : ℕ} (hr : r < localPrime h) :
    LocalCoverMatrix.rightCount (candidate h (candidateAt h s)) h r =
      HashFamily.bucketSize (LocalGraph.rightVertices (512*h) h) (mapAt h s) (r : LocalField h) := by
  unfold LocalCoverMatrix.rightCount
  rw [LocalMaskHashes.right_count _ hr,candidateAt_mapAt]

theorem program_meets {lim : Light.Limits} {d : ℕ}
    {μ : ℕ → ℤ} {h src activePtr : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hsrc : src+rows h*cols h ≤ activePtr)
    (hspace : activePtr+LightCoverGreedy.total (rows h) (cols h) (scheduleSize h) ≤ lim.space)
    (hread : ∀ i < rows h, ∀ r < cols h, μ (src+i*cols h+r) = (matrix h i r : ℤ))
    (hword : (1 : ℤ) ≤ lim.word) :
    Light.Meets lim LightCoverGreedy.program 0 d [src,activePtr,rows h,cols h,scheduleSize h] μ
      (LightCoverGreedy.time (rows h) (cols h) (scheduleSize h))
      (fun r μ' => r = (LightCoverGreedy.out activePtr (rows h) (cols h) : ℤ) ∧
        (∀ s : Occurrence h,
          μ' (LightCoverGreedy.out activePtr (rows h) (cols h)+s.val) = (candidateAt h s : ℤ)) ∧
        Light.SameOutside μ μ' activePtr (LightCoverGreedy.total (rows h) (cols h) (scheduleSize h))) := by
  apply (LightCoverGreedy.program_meets (matrix h) hw hd (rows_pos h) hsrc hspace hread
    (fun _ _ _ _ => LocalCoverMatrix.entry_le ..) hword).mono le_rfl
  intro r μ' ⟨hresult,hsegment,_,hkept⟩
  refine ⟨hresult,?_,hkept⟩
  intro s
  have hs : s.val < (indices h).length := by rw [indices_length]; exact s.isLt
  have he := hsegment s.val (by simpa only [List.length_map,indices] using hs)
  unfold candidateAt
  rw [List.getD_eq_getElem _ _ hs]
  simpa only [List.getElem_map,indices] using he

end ThreeSum.LightLocalCoverSchedule
