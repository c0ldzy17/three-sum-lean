import Submission.ThreeSum.LightWantedRow
import Submission.ThreeSum.WantedPairs

/-!
# A literal output-sensitive join of original-position residue arrays

The host reads each left code and visits only its matching retained right
fiber. Recursion gives a sum of actual row costs; it never charges or scans
the full left/right Cartesian product. The output contains every matching
original-position pair exactly once.
-/

namespace ThreeSum.LightWantedJoin

open Light SourceBuckets WantedPairs

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

/-- Left codes, right offsets, right indices, left/right lengths, modulus,
and first output address. -/
def body (pSelf pRow : ℕ) : Stmt :=
  .ite (k 0 <' v 3)
    (.call pSelf [v 0,v 1,v 2,v 3 -' k 1,v 4,v 5,v 6] 7 ;;
      .set 8 (v 3 -' k 1) ;;
      .set 9 (M (v 0 +' v 8)) ;;
      .set 10 (M (v 1 +' v 9)) ;;
      .set 11 (M (v 1 +' v 9 +' k 1) -' v 10) ;;
      .call pRow [v 8,v 2,v 10,v 11,v 6,v 7] 12 ;;
      .set 0 (v 7 +' v 11))
    (.set 0 (k 0))

def time (left right : ℕ → ℕ) (NR : ℕ) : ℕ → ℕ
  | 0 => 50
  | n+1 => time left right NR n+LightWantedRow.time (LightHistogram.count right (left n) NR)+250

theorem time_bound (left right : ℕ → ℕ) (NR n : ℕ) :
    time left right NR n ≤ 400*(n+count left right NR n+1) := by
  induction n with
  | zero => simp [time]
  | succ n ih => rw [time,count_succ]; unfold LightWantedRow.time; omega

variable {lim : Limits} {P : Program}

theorem meets {pMain pRow keys offsets flat NR M dst : ℕ}
    (hmain : P[pMain]? = some (body pMain pRow))
    (hrow : P[pRow]? = some LightWantedRow.body)
    (left right : ℕ → ℕ) (hright : ∀ j < NR, right j < M) :
    ∀ n d : ℕ, ∀ μ : ℕ → ℤ,
      (lim.space : ℤ) ≤ lim.word → keys+n ≤ dst → offsets+M+1 ≤ dst → flat+NR ≤ dst →
      dst+2*count left right NR n ≤ lim.space → d+n+2 ≤ lim.depth →
      (∀ i < n, left i < M) → (∀ i < n, μ (keys+i)=(left i : ℤ)) →
      Stored μ right NR M offsets flat →
      Meets lim P pMain d [keys,offsets,flat,n,NR,M,dst] μ (time left right NR n)
        (fun r ν => r=(count left right NR n : ℤ) ∧
          Seg ν dst (cells (pairs μ offsets flat left n)) ∧ Kept μ ν dst) := by
  intro n
  induction n with
  | zero =>
    intro d μ hw hkeys hoffsets hflat hspace hd hleft hread H
    apply Meets.of_body hmain
    unfold body time
    refine Ends.iteLast (fun h => False.elim (by simpa using h)) (fun _ => ?_)
    light_set (0 : ℕ)
    exact ⟨rfl,by simp [cells],fun _ _ => rfl⟩
  | succ n ih =>
    intro d μ hw hkeys hoffsets hflat hspace hd hleft hread H
    let previous := count left right NR n
    let size := LightHistogram.count right (left n) NR
    let start := offset right NR (left n)
    have htotal : count left right NR (n+1)=previous+size := count_succ left right NR n
    have hspace' : dst+2*(previous+size) ≤ lim.space := by rwa [htotal] at hspace
    have hcode := hleft n (by omega)
    have hstart : start ≤ NR := offset_le hright (by omega)
    have hend : start+size ≤ NR := by
      have hh := offset_le hright (show left n+1 ≤ M by omega)
      rw [offset_succ] at hh
      exact hh
    have hprevious : previous ≤ count left right NR (n+1) := count_mono left right NR (by omega)
    have hpreviousWord : (previous : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (show previous ≤ lim.space by omega)).trans hw
    have hsizeWord : (size : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (show size ≤ lim.space by omega)).trans hw
    apply Meets.of_body hmain
    unfold body time
    refine Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simp at h))
    have hprev := ih (d+1) μ hw (by omega) hoffsets hflat (by omega) (by omega)
      (fun i hi => hleft i (by omega)) (fun i hi => hread i (by omega)) H
    light_call hprev using LightWantedRow.time with prev μ₁ ⟨hprev,hstored,hkeep₁⟩
    have hreadCode : μ₁ (keys+n)=(left n : ℤ) :=
      (hkeep₁ _ (by omega)).trans (hread n (by omega))
    have hreadCodeZ : μ₁ (((keys : ℤ)+(n : ℤ)).toNat)=(left n : ℤ) := by
      rw [show ((keys : ℤ)+(n : ℤ)).toNat=keys+n by omega]
      exact hreadCode
    have hreadStart : μ₁ (offsets+left n)=(start : ℤ) :=
      (hkeep₁ _ (by omega)).trans (H.offsets (left n) (by omega))
    have hreadStartZ : μ₁ (((offsets : ℤ)+(left n : ℤ)).toNat)=(start : ℤ) := by
      rw [show ((offsets : ℤ)+(left n : ℤ)).toNat=offsets+left n by omega]
      exact hreadStart
    have hreadStop : μ₁ (offsets+left n+1)=((start+size : ℕ) : ℤ) := by
      rw [hkeep₁ _ (by omega),Nat.add_assoc,H.offsets (left n+1) (by omega),offset_succ]
    have hreadStopZ : μ₁ (((offsets : ℤ)+(left n : ℤ)+1).toNat)=((start+size : ℕ) : ℤ) := by
      rw [show ((offsets : ℤ)+(left n : ℤ)+1).toNat=offsets+left n+1 by omega]
      exact hreadStop
    light_set (n : ℕ) using LightWantedRow.time
    light_set (left n : ℕ) using hreadCodeZ,LightWantedRow.time
    light_set (start : ℕ) using hreadStartZ,LightWantedRow.time
    light_set (size : ℕ) using hreadStopZ,LightWantedRow.time
    have hflatRead (t : ℕ) (ht : t < size) : μ₁ (flat+start+t)=μ (flat+start+t) :=
      hkeep₁ _ (by omega)
    have hrowValues (t : ℕ) (ht : t < size) : |μ₁ (flat+start+t)| ≤ lim.word := by
      obtain ⟨j,hj,_,_,hjRead⟩ := H.read_bucket hright hcode ht
      rw [hflatRead t ht,hjRead,Int.abs_natCast]
      exact (Int.ofNat_le.mpr (show j ≤ lim.space by omega)).trans hw
    have hc := LightWantedRow.meets (d := d+1) (μ := μ₁) (left := n) (src := flat)
      (start := start) (n := size) (dst := dst) (previous := previous)
      hrow hw (by omega) hspace'
      ((Int.ofNat_le.mpr (show n ≤ lim.space by omega)).trans hw) hrowValues
    light_call hc using hprev,previous,size,LightWantedRow.time
      with unused μ₂ ⟨hout,hkeep₂⟩
    have hnew : Seg μ₂ (dst+2*previous) (cells (row μ offsets flat left n)) := by
      apply row_segment H hright hcode
      intro t ht
      exact ⟨(hout t ht).1,(hout t ht).2.trans (hflatRead t ht)⟩
    have holdLen : (cells (pairs μ offsets flat left n)).length=2*previous := by
      rw [cells_length,pairs_length H n (fun i hi => hleft i (by omega))]
    have hold : Seg μ₂ dst (cells (pairs μ offsets flat left n)) :=
      hstored.of_sameOutside hkeep₂ (Or.inl (by rw [holdLen]))
    light_set (count left right NR (n+1) : ℕ) using htotal,hprev,previous,size,LightWantedRow.time
    refine ⟨rfl,?_,?_⟩
    · rw [pairs_succ,cells_append]
      apply seg_append.mpr
      exact ⟨hold,by simpa only [holdLen] using hnew⟩
    · intro a ha
      change μ₂ a=μ a
      exact (hkeep₂ a (Or.inl (by omega))).trans (hkeep₁ a ha)

def program : Program := [body 0 1,LightWantedRow.body]

theorem program_meets {keys offsets flat NR M dst n d : ℕ} {μ : ℕ → ℤ}
    (left right : ℕ → ℕ) (hright : ∀ j < NR, right j < M)
    (hw : (lim.space : ℤ) ≤ lim.word) (hkeys : keys+n ≤ dst)
    (hoffsets : offsets+M+1 ≤ dst) (hflat : flat+NR ≤ dst)
    (hspace : dst+2*count left right NR n ≤ lim.space) (hd : d+n+2 ≤ lim.depth)
    (hleft : ∀ i < n, left i < M) (hread : ∀ i < n, μ (keys+i)=(left i : ℤ))
    (H : Stored μ right NR M offsets flat) :
    Meets lim program 0 d [keys,offsets,flat,n,NR,M,dst] μ (time left right NR n)
      (fun r ν => r=(count left right NR n : ℤ) ∧
        Seg ν dst (cells (pairs μ offsets flat left n)) ∧ Kept μ ν dst) :=
  meets rfl rfl left right hright n d μ hw hkeys hoffsets hflat hspace hd hleft hread H

end ThreeSum.LightWantedJoin
