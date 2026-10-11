import Submission.ThreeSum.LightArray

/-!
# Stable extraction of one color class from the original signed array

The program reads stored colors and original values. It writes a length
header followed by exactly the selected values, optionally negated. Repeated
values are preserved; deduplication belongs to the later normalization pass.
-/

namespace ThreeSum.LightClassFilter

open Light

set_option maxHeartbeats 1200000

def items (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) : List ℤ :=
  ((List.range n).filter fun i => decide (color i = want)).map fun i => scale*x i

@[simp] theorem items_zero (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) :
    items x color want scale 0 = [] := by simp [items]

theorem items_succ (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) :
    items x color want scale (n+1) =
      items x color want scale n ++ (if color n = want then [scale*x n] else []) := by
  by_cases h : color n = want <;> simp [items,List.range_succ,h]

theorem items_length_le (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) :
    (items x color want scale n).length ≤ n := by
  simpa only [items,List.length_map,List.length_range] using
    List.length_filter_le (p := fun i => decide (color i = want)) (l := List.range n)

theorem mem_items (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) (z : ℤ) :
    z ∈ items x color want scale n ↔ ∃ i, i < n ∧ color i = want ∧ scale*x i = z := by
  simp [items,and_assoc]

def roundBody : Stmt :=
  .ite (M (v 1 +' v 7) =' v 4)
    (.store (v 2 +' k 1 +' v 6) (v 5 *' M (v 0 +' v 7)) ;;
      .set 6 (v 6 +' k 1)) .skip

/-- Source, color array, output header, input length, desired color, sign. -/
def body : Stmt :=
  .set 6 (k 0) ;;
  .for 7 (v 3) roundBody ;;
  .store (v 2) (v 6) ;;
  .set 0 (v 6)

def time (n : ℕ) : ℕ := 100*n+100

def Inv (μ : ℕ → ℤ) (x : ℕ → ℤ) (color : ℕ → ℕ)
    (src colors dst n want : ℕ) (scale : ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ ν : ℕ → ℤ,
    σ = ⟨frame [src,colors,dst,n,want,scale,(items x color want scale j).length,j],ν⟩ ∧
    Seg ν (dst+1) (items x color want scale j) ∧ SameOutside μ ν dst (n+1)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {p src colors dst n want U : ℕ} {scale : ℤ} {μ : ℕ → ℤ}
    (hmain : P[p]? = some body) (x : ℕ → ℤ) (color : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (h3 : (3 : ℤ) ≤ lim.word)
    (hsrc : src+n ≤ dst) (hcolors : colors+n ≤ dst) (hspace : dst+(n+1) ≤ lim.space)
    (hwant : want < 3) (hscale : |scale| ≤ 1) (hU : (U : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src+i) = x i)
    (hcolorRead : ∀ i < n, μ (colors+i) = (color i : ℤ))
    (hcolorLt : ∀ i < n, color i < 3) (hbound : ∀ i < n, |x i| ≤ (U : ℤ)) :
    Meets lim P p d [src,colors,dst,n,want,scale] μ (time n)
      (fun r ν => r = ((items x color want scale n).length : ℤ) ∧
        ν dst = ((items x color want scale n).length : ℤ) ∧
        Seg ν (dst+1) (items x color want scale n) ∧ SameOutside μ ν dst (n+1)) := by
  have hscaleBounds := abs_le.mp hscale
  have hnWord : (n : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by omega : n ≤ lim.space)).trans hw
  apply Meets.of_body hmain
  unfold body time
  light_set (0 : ℕ)
  light_assoc
  refine Ends.pieceThen (Ends.for (lim := lim) (P := P) (d := d)
    (i := 7) (hi := v 3) (body := roundBody) (T := 100*n+50)
    (Q := Inv μ x color src colors dst n want scale n)
    (Inv μ x color src colors dst n want scale) n 80
    ?start ?round ?done ?bound (hT := by light_time)) ?after
  case start =>
    exact ⟨μ,by simp [update_frame_setLocal],by simp,SameOutside.refl⟩
  case round =>
    rintro j _ hj _ ⟨ν,rfl,hseg,hkeep⟩
    have hlen := items_length_le x color want scale j
    have hcr : ν (colors+j) = (color j : ℤ) :=
      (hkeep _ (Or.inl (by omega))).trans (hcolorRead j hj)
    have hxr : ν (src+j) = x j :=
      (hkeep _ (Or.inl (by omega))).trans (hread j hj)
    have hx : |scale*x j| ≤ lim.word := by
      rw [abs_mul]
      exact ((mul_le_mul hscale (hbound j hj) (abs_nonneg _) (by norm_num)).trans
        (by simpa using hU))
    have hxb := abs_le.mp hx
    have hc := hcolorLt j hj
    unfold roundBody
    light_if he hn : color j = want using hcr
    · have hs : items x color want scale (j+1) = items x color want scale j ++ [scale*x j] := by
        rw [items_succ,if_pos he]
      have hslen : (items x color want scale (j+1)).length =
          (items x color want scale j).length+1 := by simp [hs]
      light_store (dst+1+(items x color want scale j).length) (scale*x j) using hxr
      light_set ((items x color want scale (j+1)).length : ℕ) using hslen
      refine ⟨by simp,Function.update ν (dst+1+(items x color want scale j).length) (scale*x j),
        by simp [update_frame_setLocal],?_,?_⟩
      · rw [hs]
        exact hseg.snoc (scale*x j)
      · exact hkeep.update ⟨by omega,by omega⟩ _
    · have hs : items x color want scale (j+1) = items x color want scale j := by
        rw [items_succ,if_neg hn,List.append_nil]
      light_skip
      exact ⟨by simp,ν,by simp [update_frame_setLocal,hs],by simpa [hs] using hseg,hkeep⟩
  case done =>
    intro σ _ h
    exact h
  case bound =>
    rintro j _ hj _ ⟨ν,rfl,_,_⟩
    light_side
  case after =>
    rintro _ ⟨ν,rfl,hseg,hkeep⟩
    have hlen := items_length_le x color want scale n
    light_store dst ((items x color want scale n).length : ℕ)
    light_set ((items x color want scale n).length : ℕ)
    exact ⟨by simp,by simp,hseg.update_out (Or.inl (by omega)) _,
      hkeep.update ⟨by omega,by omega⟩ _⟩

def program : Program := [body]

theorem program_meets {src colors dst n want U : ℕ} {scale : ℤ} {μ : ℕ → ℤ}
    (x : ℕ → ℤ) (color : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (h3 : (3 : ℤ) ≤ lim.word)
    (hsrc : src+n ≤ dst) (hcolors : colors+n ≤ dst) (hspace : dst+(n+1) ≤ lim.space)
    (hwant : want < 3) (hscale : |scale| ≤ 1) (hU : (U : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src+i) = x i)
    (hcolorRead : ∀ i < n, μ (colors+i) = (color i : ℤ))
    (hcolorLt : ∀ i < n, color i < 3) (hbound : ∀ i < n, |x i| ≤ (U : ℤ)) :
    Meets lim program 0 d [src,colors,dst,n,want,scale] μ (time n)
      (fun r ν => r = ((items x color want scale n).length : ℤ) ∧
        ν dst = ((items x color want scale n).length : ℤ) ∧
        Seg ν (dst+1) (items x color want scale n) ∧ SameOutside μ ν dst (n+1)) :=
  meets rfl x color hw h3 hsrc hcolors hspace hwant hscale hU hread hcolorRead hcolorLt hbound

end ThreeSum.LightClassFilter
