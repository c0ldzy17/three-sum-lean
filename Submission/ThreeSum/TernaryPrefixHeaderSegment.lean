import Submission.ThreeSum.LightTernaryPrefixHeader

namespace ThreeSum.LightTernaryPrefixHeader
open Light
set_option maxHeartbeats 4000000

def patchList (loc : ℕ→ℤ) : List ℤ→ List (ℕ×ℕ)→ List ℤ
  | xs,[]=>xs
  | xs,(i,r)::fs=>patchList loc (xs.set i (loc r)) fs

@[simp] theorem patchList_length (loc : ℕ→ℤ) (xs : List ℤ) (fs : List (ℕ×ℕ)) :
    (patchList loc xs fs).length=xs.length :=by
  induction fs generalizing xs with
  | nil=>rfl
  | cons f fs ih=>simp only [patchList,ih,List.length_set]

theorem store_seg {μ : ℕ→ℤ} {base : ℕ} {xs : List ℤ} (hs : Seg μ base xs)
    (i : ℕ) (z : ℤ) : Seg (Function.update μ (base+i) z) base (xs.set i z) :=by
  intro j hj
  have hjs : j<xs.length :=by simpa using hj
  by_cases he : j=i
  · subst j
    simp [List.getElem_set_self,hjs]
  · rw [Function.update_of_ne (by omega),hs j hjs]
    exact (List.getElem_set_of_ne (Ne.symm he) z hj).symm

theorem patch_seg {μ : ℕ→ℤ} {base : ℕ} {xs : List ℤ} (hs : Seg μ base xs)
    (loc : ℕ→ℤ) (fs : List (ℕ×ℕ)) :
    Seg (patch base loc μ fs) base (patchList loc xs fs) :=by
  induction fs generalizing μ xs with
  | nil=>exact hs
  | cons f fs ih=>exact ih (store_seg hs f.1 (loc f.2))

def resultHeader (templateValues : List ℤ)
    (template live hdr s m p power alpha2 alphaRank localQ radix J N T L groups nb bank powers Fbase Gbase : ℕ)
    (ret : ℤ) : List ℤ :=
  (patchList
    (frame (args template live hdr s m p power alpha2 alphaRank localQ radix J++
      locals N T L groups nb bank powers s p power alpha2 alphaRank localQ radix Fbase Gbase++[ret]))
    templateValues LightTernaryPrefixLoop.headerWrites).set 104 0

@[simp] theorem resultHeader_length (xs : List ℤ)
    (template live hdr s m p power alpha2 alphaRank localQ radix J N T L groups nb bank powers Fbase Gbase : ℕ)
    (ret : ℤ) :
    (resultHeader xs template live hdr s m p power alpha2 alphaRank localQ radix J N T L groups nb bank powers Fbase Gbase ret).length=xs.length :=by
  simp [resultHeader]

/-- Exact segment conversion for the actual finite header writes. -/
theorem result_segment {μ μ₀ ν : ℕ→ℤ} {template live hdr s m p power alpha2 alphaRank localQ radix J
    N T L groups nb bank powers Fbase Gbase : ℕ} {ret : ℤ} {xs : List ℤ}
    (hlen : xs.length=106) (hxs : Seg μ template xs)
    (hcopy : ∀i<106, μ₀ (live+i)=μ (template+i))
    (hν : ν=Function.update (patch live
      (frame (args template live hdr s m p power alpha2 alphaRank localQ radix J++
        locals N T L groups nb bank powers s p power alpha2 alphaRank localQ radix Fbase Gbase++[ret]))
      μ₀ LightTernaryPrefixLoop.headerWrites) (live+104) 0) :
    Seg ν live (resultHeader xs template live hdr s m p power alpha2 alphaRank localQ radix J
      N T L groups nb bank powers Fbase Gbase ret) :=by
  have hc : Seg μ₀ live xs :=by
    intro i hi
    exact (hcopy i (by omega)).trans (hxs i hi)
  subst ν
  exact store_seg (patch_seg hc _ _) 104 0

end ThreeSum.LightTernaryPrefixHeader
