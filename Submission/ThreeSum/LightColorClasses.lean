import Submission.ThreeSum.LightColorArray
import Submission.ThreeSum.ColorClassLists

/-!
# Original-array construction of all three color classes

A fixed six-procedure program builds the color array and extracts three
disjoint output segments with length headers. The third class is negated.
Original values and their multiplicities are kept until class normalization.
-/

namespace ThreeSum.LightColorClasses

open Light ColorClassLists

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

/-- Source, length, binary width, two coordinates, four map entries,
color-array output, three class headers, scratch. -/
def body (pColors pFilter : ℕ) : Stmt :=
  .call pColors [v 2,v 1,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 13] 14 ;;
  .call pFilter [v 0,v 9,v 10,v 1,k 0,k 1] 14 ;;
  .call pFilter [v 0,v 9,v 11,v 1,k 1,k 1] 14 ;;
  .call pFilter [v 0,v 9,v 12,v 1,k 2,k 0 -' k 1] 14

def time (W n : ℕ) : ℕ := LightColorArray.time W n+3*LightClassFilter.time n+200

structure Output {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (μ ν : ℕ → ℤ) (colors dst0 dst1 dst2 : ℕ) : Prop where
  colorValues : ∀ i < n, ν (colors+i) = (LightColorIndex.color p i : ℤ)
  header0 : ν dst0 = ((classList p x 0 1).length : ℤ)
  values0 : Seg ν (dst0+1) (classList p x 0 1)
  header1 : ν dst1 = ((classList p x 1 1).length : ℤ)
  values1 : Seg ν (dst1+1) (classList p x 1 1)
  header2 : ν dst2 = ((classList p x 2 (-1)).length : ℤ)
  values2 : Seg ν (dst2+1) (classList p x 2 (-1))
  kept : Kept μ ν colors

structure Procs (P : Program) (pMain : ℕ) where
  pColors : ℕ
  pPowers : ℕ
  pColor : ℕ
  pErase : ℕ
  pFilter : ℕ
  colors : P[pColors]? = some (LightColorArray.body pPowers pColor)
  powers : P[pPowers]? = some powTableBody
  color : P[pColor]? = some (LightColorIndex.body pErase)
  erase : P[pErase]? = some (LightMaskErase.body pErase)
  filter : P[pFilter]? = some LightClassFilter.body
  main : P[pMain]? = some (body pColors pFilter)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain src n W colors dst0 dst1 dst2 work U : ℕ} {μ : ℕ → ℤ}
    (C : Procs P pMain) (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : n ≤ 2^W)
    (hsrc : src+n ≤ colors) (hcolors : colors+n ≤ dst0)
    (h0 : dst0+(n+1) ≤ dst1) (h1 : dst1+(n+1) ≤ dst2) (h2 : dst2+(n+1) ≤ work)
    (hspace : work+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word) (hU : (U : ℤ) ≤ lim.word)
    (hd : d+W+3 ≤ lim.depth) (hread : Seg μ src (List.ofFn x))
    (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    Meets lim P pMain d [src,n,W,p.1.1.val,p.1.2.val,(p.2 (false,false)).val,
      (p.2 (false,true)).val,(p.2 (true,false)).val,(p.2 (true,true)).val,
      colors,dst0,dst1,dst2,work] μ (time W n)
      (fun _ ν => Output p x μ ν colors dst0 dst1 dst2) := by
  have hW := p.1.1.isLt
  have h3 : (3 : ℤ) ≤ lim.word := by
    have hh : 2^2 ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hh' : (4 : ℤ) ≤ ((2^(W+1) : ℕ) : ℤ) := by exact_mod_cast hh
    omega
  have read : ∀ i < n, μ (src+i) = value x i := by
    intro i hi
    have hh := hread i (by simpa using hi)
    simpa only [List.getElem_ofFn,← value_fin x ⟨i,hi⟩] using hh
  have bound : ∀ i < n, |value x i| ≤ (U : ℤ) := by
    intro i hi
    simpa only [value,hi,dite_true] using hbound ⟨i,hi⟩
  have len0 := length_classList_le p x 0 1
  have len1 := length_classList_le p x 1 1
  apply Meets.of_body C.main
  unfold body time
  have hc := LightColorArray.meets (d := d+1) (n := n) (dst := colors) (work := work)
    C.colors C.powers C.color C.erase μ p hw hn (by omega) hspace hword (by omega)
  light_call hc using LightColorArray.time,LightColorIndex.time,LightMaskErase.time,
    LightClassFilter.time with r ν₁ ⟨color₁,_,keep₁⟩
  have read₁ : ∀ i < n, ν₁ (src+i) = value x i := by
    intro i hi
    exact (keep₁ _ ⟨by omega,Or.inl (by omega)⟩).trans (read i hi)
  have hf0 := LightClassFilter.meets (d := d+1) (μ := ν₁) (src := src) (colors := colors)
    (dst := dst0) (n := n) (want := 0) (scale := 1) (U := U) C.filter
    (value x) (LightColorIndex.color p) hw h3 (by omega) hcolors (by omega)
    (by decide) (by norm_num) hU read₁ color₁ (fun i _ => LightColorIndex.color_lt p i) bound
  light_call hf0 using LightColorArray.time,LightColorIndex.time,LightMaskErase.time,
    LightClassFilter.time with r ν₂ ⟨_,header0,values0,keep₂⟩
  have read₂ : ∀ i < n, ν₂ (src+i) = value x i := by
    intro i hi
    exact (keep₂ _ (Or.inl (by omega))).trans (read₁ i hi)
  have color₂ : ∀ i < n, ν₂ (colors+i) = (LightColorIndex.color p i : ℤ) := by
    intro i hi
    exact (keep₂ _ (Or.inl (by omega))).trans (color₁ i hi)
  have hf1 := LightClassFilter.meets (d := d+1) (μ := ν₂) (src := src) (colors := colors)
    (dst := dst1) (n := n) (want := 1) (scale := 1) (U := U) C.filter
    (value x) (LightColorIndex.color p) hw h3 (by omega) (by omega) (by omega)
    (by decide) (by norm_num) hU read₂ color₂ (fun i _ => LightColorIndex.color_lt p i) bound
  light_call hf1 using LightColorArray.time,LightColorIndex.time,LightMaskErase.time,
    LightClassFilter.time with r ν₃ ⟨_,header1,values1,keep₃⟩
  have read₃ : ∀ i < n, ν₃ (src+i) = value x i := by
    intro i hi
    exact (keep₃ _ (Or.inl (by omega))).trans (read₂ i hi)
  have color₃ : ∀ i < n, ν₃ (colors+i) = (LightColorIndex.color p i : ℤ) := by
    intro i hi
    exact (keep₃ _ (Or.inl (by omega))).trans (color₂ i hi)
  have hf2 := LightClassFilter.meets (d := d+1) (μ := ν₃) (src := src) (colors := colors)
    (dst := dst2) (n := n) (want := 2) (scale := -1) (U := U) C.filter
    (value x) (LightColorIndex.color p) hw h3 (by omega) (by omega) (by omega)
    (by decide) (by norm_num) hU read₃ color₃ (fun i _ => LightColorIndex.color_lt p i) bound
  light_call hf2 using LightColorArray.time,LightColorIndex.time,LightMaskErase.time,
    LightClassFilter.time with r ν₄ ⟨_,header2,values2,keep₄⟩
  refine ⟨?_,?_,?_,?_,?_,header2,values2,?_⟩
  · intro i hi
    exact (keep₄ _ (Or.inl (by omega))).trans (color₃ i hi)
  · exact (keep₄ _ (Or.inl (by omega))).trans
      ((keep₃ _ (Or.inl (by omega))).trans header0)
  · exact (values0.of_sameOutside keep₃ (Or.inl (by change dst0+1+(classList p x 0 1).length ≤ dst1; omega))).of_sameOutside
      keep₄ (Or.inl (by change dst0+1+(classList p x 0 1).length ≤ dst2; omega))
  · exact (keep₄ _ (Or.inl (by omega))).trans header1
  · exact values1.of_sameOutside keep₄ (Or.inl (by change dst1+1+(classList p x 1 1).length ≤ dst2; omega))
  · intro a ha
    exact (keep₄ _ (Or.inl (by omega))).trans
      ((keep₃ _ (Or.inl (by omega))).trans
        ((keep₂ _ (Or.inl (by omega))).trans (keep₁ _ ⟨by omega,Or.inl ha⟩)))

def program : Program :=
  [body 1 5,LightColorArray.body 2 3,powTableBody,LightColorIndex.body 4,
    LightMaskErase.body 4,LightClassFilter.body]

def programProcs : Procs program 0 := ⟨1,2,3,4,5,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem program_meets {src n W colors dst0 dst1 dst2 work U : ℕ} {μ : ℕ → ℤ}
    (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : n ≤ 2^W)
    (hsrc : src+n ≤ colors) (hcolors : colors+n ≤ dst0)
    (h0 : dst0+(n+1) ≤ dst1) (h1 : dst1+(n+1) ≤ dst2) (h2 : dst2+(n+1) ≤ work)
    (hspace : work+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word) (hU : (U : ℤ) ≤ lim.word)
    (hd : d+W+3 ≤ lim.depth) (hread : Seg μ src (List.ofFn x))
    (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    Meets lim program 0 d [src,n,W,p.1.1.val,p.1.2.val,(p.2 (false,false)).val,
      (p.2 (false,true)).val,(p.2 (true,false)).val,(p.2 (true,true)).val,
      colors,dst0,dst1,dst2,work] μ (time W n)
      (fun _ ν => Output p x μ ν colors dst0 dst1 dst2) :=
  programProcs.meets p x hw hn hsrc hcolors h0 h1 h2 hspace hword hU hd hread hbound

theorem time_bound (W n : ℕ) : time W n ≤ 1200*(W+1)*(n+1) := by
  have h := LightColorArray.time_bound W n
  unfold time LightClassFilter.time
  nlinarith

end ThreeSum.LightColorClasses
