import Submission.ThreeSumApsp.Lang.Lib.MergeSort
import Mathlib.Data.List.Dedup

/-!
# Sorting and deduplicating a single already separated color class

The merge-sort implementation and proof are reused unchanged from the
attached upstream `ThreeSumApsp/Lang/Lib/Merge{,Sort}.lean` sources. The new
linear procedure removes adjacent repeats from the sorted output. The
original membership equivalence is retained, which is the witness needed
by the three-color reduction. Duplicates are removed only inside a class.
-/

namespace ThreeSum.LightNormalize

open Light

variable {lim : Limits} {P : Program}

def emitBody (pSelf : ℕ) : Stmt :=
  .store (v 2) (M (v 0)) ;;
  .call pSelf [v 0 +' k 1,v 1 -' k 1,v 2 +' k 1] 3 ;;
  .set 0 (v 3 +' k 1)

/-- Arguments: sorted source, length, output. The last occurrence of each
value is retained, matching `List.dedup`. -/
def dedupBody (pSelf : ℕ) : Stmt :=
  .ite (k 0 <' v 1)
    (.ite (k 1 <' v 1)
      (.ite (M (v 0) =' M (v 0 +' k 1))
        (.call pSelf [v 0 +' k 1,v 1 -' k 1,v 2] 0)
        (emitBody pSelf))
      (emitBody pSelf))
    (.set 0 (k 0))

def dedupTime (n : ℕ) : ℕ := 200*n+30

theorem sorted_head_not_mem {x y : ℤ} {zs : List ℤ}
    (hs : (x::y::zs).Pairwise (· ≤ ·)) (hne : x ≠ y) : x ∉ y::zs := by
  simp only [List.pairwise_cons] at hs
  intro hx
  rcases List.mem_cons.mp hx with hxy | hx
  · exact hne hxy
  · exact hne (le_antisymm (hs.1 y (by simp)) (hs.2.1 x hx))

theorem dedup_strict {L : List ℤ} (hs : L.Pairwise (· ≤ ·)) :
    L.dedup.Pairwise (· < ·) := by
  have hle := hs.sublist (List.dedup_sublist L)
  have hne := List.nodup_dedup L
  exact (List.pairwise_and_iff.mpr ⟨hle,hne⟩).imp (fun h => lt_of_le_of_ne h.1 h.2)

theorem dedup_meets {pDedup : ℕ}
    (hprog : P[pDedup]? = some (dedupBody pDedup))
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word) :
    ∀ (L : List ℤ) (μ : ℕ → ℤ) (src dst d : ℕ),
      L.Pairwise (· ≤ ·) → Seg μ src L → src+L.length ≤ dst →
      dst+L.length ≤ lim.space → d+L.length ≤ lim.depth →
      Meets lim P pDedup d [src,L.length,dst] μ (dedupTime L.length)
        (fun r μ' => r = (L.dedup.length : ℤ) ∧ Seg μ' dst L.dedup ∧
          SameOutside μ μ' dst L.length) := by
  intro L
  induction L with
  | nil =>
      intro μ src dst d hs hseg hsep hspace hd
      apply Meets.of_body hprog
      unfold dedupBody dedupTime
      refine Ends.iteLast (fun h => False.elim (by simp at h)) (fun _ => ?_)
      light_set (0 : ℕ)
      exact ⟨rfl,Seg.nil,SameOutside.refl⟩
  | cons x zs ih =>
      intro μ src dst d hs hseg hsep hspace hd
      have hlen : (x::zs).length = zs.length+1 := rfl
      have hzs := hs.tail
      have hsource := (seg_cons.mp hseg).1
      have htail := (seg_cons.mp hseg).2
      have hsmall := (List.dedup_sublist zs).length_le
      have hemit :
          Ends lim P d (emitBody pDedup) ⟨frame [src,zs.length+1,dst],μ⟩
            (200*zs.length+180)
            (fun σ => σ.loc 0 = ((x::zs.dedup).length : ℤ) ∧
              Seg σ.mem dst (x::zs.dedup) ∧ SameOutside μ σ.mem dst (zs.length+1)) := by
        unfold emitBody
        light_store dst x using hsource,dedupTime
        have htail' : Seg (Function.update μ dst x) (src+1) zs := by
          intro i hi
          rw [Function.update_of_ne (by omega)]
          exact htail i hi
        light_call (ih (Function.update μ dst x) (src+1) (dst+1) (d+1)
          hzs htail' (by omega) (by omega) (by omega))
          using dedupTime with count μ' ⟨hcount,hout,hkeep⟩
        light_set (zs.dedup.length+1 : ℕ) using hcount,dedupTime
        refine ⟨by simp,?_,?_⟩
        · rw [seg_cons]
          refine ⟨?_,hout⟩
          change μ' dst = x
          rw [hkeep dst (Or.inl (by omega)),Function.update_self]
        · intro a ha
          change μ' a = μ a
          rw [hkeep a (by omega),Function.update_of_ne (by omega)]
      apply Meets.of_body hprog
      unfold dedupBody dedupTime
      refine Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simp at h))
      cases zs with
      | nil =>
          refine Ends.iteLast (fun h => False.elim (by simp at h)) (fun _ => ?_)
          simpa using hemit.mono (by light_time) (fun _ h => h)
      | cons y ys =>
          have hysLen : (y::ys).length = ys.length+1 := rfl
          have hnext : μ (src+1) = y := (seg_cons.mp htail).1
          refine Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simp at h))
          light_if hxy hxy : x = y using hsource,hnext,dedupTime
          · have hdedup : (x::y::ys).dedup = (y::ys).dedup :=
              List.dedup_cons_of_mem (by simp [hxy])
            light_call (ih μ (src+1) dst (d+1) hzs htail
              (by omega) (by omega) (by omega))
              using dedupTime with count μ' ⟨hcount,hout,hkeep⟩
            refine ⟨by simpa [hdedup] using hcount,by simpa [hdedup] using hout,?_⟩
            exact hkeep.mono le_rfl (by simp)
          · have hdedup : (x::y::ys).dedup = x::(y::ys).dedup :=
              List.dedup_cons_of_notMem (sorted_head_not_mem hs hxy)
            light_piece hemit with σ h
            light_skip
            exact ⟨by simpa [hdedup] using h.1,by simpa [hdedup] using h.2.1,h.2.2⟩

/-- Arguments: class source, class length, normalized output, merge scratch. -/
def body (pSort pDedup : ℕ) : Stmt :=
  .call pSort [v 1,v 0,v 3] 4 ;;
  .call pDedup [v 0,v 1,v 2] 0

def time (n : ℕ) : ℕ := sortTime n+dedupTime n+80
def space (work n : ℕ) : ℕ := work+n

structure Procs (P : Program) (pMain : ℕ) where
  pSort : ℕ
  pHalf : ℕ
  pMerge : ℕ
  pCopy : ℕ
  pDedup : ℕ
  sort : MergeSort.Procs P pSort pHalf pMerge pCopy
  dedup : P[pDedup]? = some (dedupBody pDedup)
  main : P[pMain]? = some (body pSort pDedup)

theorem Procs.meets {pMain src dst work d : ℕ} {L : List ℤ} {μ : ℕ → ℤ}
    (C : Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word)
    (hseg : Seg μ src L) (hsep : src+L.length ≤ dst)
    (hwork : dst+L.length ≤ work) (hspace : space work L.length ≤ lim.space)
    (hd : d+L.length+Nat.clog 2 L.length+2 ≤ lim.depth) :
    Meets lim P pMain d [src,L.length,dst,work] μ (time L.length)
      (fun r μ' => ∃ out : List ℤ,
        r = (out.length : ℤ) ∧ Seg μ' dst out ∧ out.Pairwise (· < ·) ∧
        out.length ≤ L.length ∧ (∀ z, z ∈ out ↔ z ∈ L) ∧
        ∀ a, a < work → (a < src ∨ src+L.length ≤ a) →
          (a < dst ∨ dst+L.length ≤ a) → μ' a = μ a) := by
  apply Meets.of_body C.main
  unfold body time
  light_call (sort_meets (d := d+1) (a := src) (fr := work) C.sort hw h1 hseg (by omega)
    (by exact hspace) (by omega)) using sortTime,dedupTime,space with unused μ₁ ⟨⟨sorted,hsortedSeg,hperm,hsorted⟩,hkeep₁⟩
  have hlen := hperm.length_eq
  light_call (dedup_meets C.dedup hw h1 sorted μ₁ src dst (d+1)
    hsorted hsortedSeg (by omega) (by unfold space at hspace; omega) (by omega))
    using hlen,sortTime,dedupTime with count μ₂ ⟨hcount,hout,hkeep₂⟩
  refine ⟨sorted.dedup,hcount,hout,dedup_strict hsorted,?_,?_,?_⟩
  · exact (List.dedup_sublist sorted).length_le.trans hlen.le
  · intro z
    exact List.mem_dedup.trans hperm.mem_iff
  · intro a ha hsrc hdst
    change μ₂ a = μ a
    rw [hkeep₂ a (by simpa [hlen] using hdst)]
    exact hkeep₁ a ⟨ha,hsrc⟩

def program : Program :=
  [body 1 5,sortBody 1 2 3 4,halfBody,mergeBody,copyBody,dedupBody 5]

def program_procs : Procs program 0 := ⟨1,2,3,4,5,⟨rfl,rfl,rfl,rfl⟩,rfl,rfl⟩

theorem program_meets {src dst work d : ℕ} {L : List ℤ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word)
    (hseg : Seg μ src L) (hsep : src+L.length ≤ dst)
    (hwork : dst+L.length ≤ work) (hspace : space work L.length ≤ lim.space)
    (hd : d+L.length+Nat.clog 2 L.length+2 ≤ lim.depth) :
    Meets lim program 0 d [src,L.length,dst,work] μ (time L.length)
      (fun r μ' => ∃ out : List ℤ,
        r = (out.length : ℤ) ∧ Seg μ' dst out ∧ out.Pairwise (· < ·) ∧
        out.length ≤ L.length ∧ (∀ z, z ∈ out ↔ z ∈ L) ∧
        ∀ a, a < work → (a < src ∨ src+L.length ≤ a) →
          (a < dst ∨ dst+L.length ≤ a) → μ' a = μ a) :=
  program_procs.meets hw h1 hseg hsep hwork hspace hd

theorem time_bound (n : ℕ) : time n ≤ 400*(n+1)*(Nat.clog 2 n+1) := by
  have hsub : n-1 ≤ n := Nat.sub_le _ _
  unfold time sortTime dedupTime
  nlinarith

end ThreeSum.LightNormalize
