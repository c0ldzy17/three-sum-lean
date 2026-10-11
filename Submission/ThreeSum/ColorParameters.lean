import Submission.ThreeSum.ColorClassLists
import Mathlib.Data.List.FinRange

/-!
# A literal small coloring-parameter order

There are exactly 81*W² integer slots. Four ternary digits select the
color map, and the remaining quotient selects its two binary coordinates.
The inverse code proves that every separating parameter is present.
-/

namespace ThreeSum.ColorParameters

def count (W : ℕ) : ℕ := 81*W^2

def colorMap (a b c d : Fin 3) : (Bool × Bool) → Fin 3
  | (false,false) => a
  | (false,true) => b
  | (true,false) => c
  | (true,true) => d

def data (W t : ℕ) : List ℤ :=
  [t/81/W,t/81%W,t/27%3,t/9%3,t/3%3,t%3]

theorem width_pos {W t : ℕ} (ht : t < count W) : 0 < W := by
  by_contra hn
  have hw : W=0 := by omega
  simp [count,hw] at ht

theorem coordinate_bounds {W t : ℕ} (ht : t < count W) :
    t/81/W < W ∧ t/81%W < W := by
  have hw := width_pos ht
  have hq : t/81 < W*W := (Nat.div_lt_iff_lt_mul (by decide : 0 < 81)).mpr (by
    simpa only [count,pow_two,Nat.mul_comm] using ht)
  exact ⟨(Nat.div_lt_iff_lt_mul hw).mpr hq,Nat.mod_lt _ hw⟩

def parameter {W t : ℕ} (ht : t < count W) : Coloring.Parameter W :=
  ((⟨t/81/W,(coordinate_bounds ht).1⟩,⟨t/81%W,(coordinate_bounds ht).2⟩),
    colorMap ⟨t/27%3,Nat.mod_lt _ (by decide)⟩ ⟨t/9%3,Nat.mod_lt _ (by decide)⟩
      ⟨t/3%3,Nat.mod_lt _ (by decide)⟩ ⟨t%3,Nat.mod_lt _ (by decide)⟩)

def fields {W : ℕ} (p : Coloring.Parameter W) : List ℤ :=
  [p.1.1.val,p.1.2.val,(p.2 (false,false)).val,(p.2 (false,true)).val,
    (p.2 (true,false)).val,(p.2 (true,true)).val]

theorem fields_parameter {W t : ℕ} (ht : t < count W) : fields (parameter ht)=data W t := rfl

def index {W : ℕ} (p : Coloring.Parameter W) : ℕ :=
  ((((p.1.1.val*W+p.1.2.val)*3+(p.2 (false,false)).val)*3+
    (p.2 (false,true)).val)*3+(p.2 (true,false)).val)*3+(p.2 (true,true)).val

theorem coordinate_pair_lt {W : ℕ} (p : Coloring.Parameter W) :
    p.1.1.val*W+p.1.2.val < W*W := by
  calc
    _ < p.1.1.val*W+W := Nat.add_lt_add_left p.1.2.isLt _
    _ = (p.1.1.val+1)*W := by ring
    _ ≤ W*W := Nat.mul_le_mul_right _ (by omega)

theorem index_lt {W : ℕ} (p : Coloring.Parameter W) : index p < count W := by
  have hp := coordinate_pair_lt p
  have h0 := (p.2 (false,false)).isLt
  have h1 := (p.2 (false,true)).isLt
  have h2 := (p.2 (true,false)).isLt
  have h3 := (p.2 (true,true)).isLt
  unfold index count
  rw [pow_two]
  omega

theorem parameter_index {W : ℕ} (p : Coloring.Parameter W) : parameter (index_lt p)=p := by
  have hw : 0 < W := by have := p.1.1.isLt; omega
  have h0 := (p.2 (false,false)).isLt
  have h1 := (p.2 (false,true)).isLt
  have h2 := (p.2 (true,false)).isLt
  have h3 := (p.2 (true,true)).isLt
  have hq : index p/81=p.1.1.val*W+p.1.2.val := by unfold index; omega
  have hi : index p/81/W=p.1.1.val := by
    rw [hq,Nat.add_comm,Nat.add_mul_div_right _ _ hw,Nat.div_eq_of_lt p.1.2.isLt]
    simp
  have hj : index p/81%W=p.1.2.val := by
    rw [hq,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt p.1.2.isLt]
  apply Prod.ext
  · exact Prod.ext (Fin.ext hi) (Fin.ext hj)
  · funext xy
    rcases xy with ⟨x,y⟩
    cases x <;> cases y <;> apply Fin.ext <;> dsimp [parameter,colorMap] <;> unfold index <;> omega

def parameters (W : ℕ) : List (Coloring.Parameter W) :=
  List.ofFn fun t : Fin (count W) => parameter t.isLt

theorem mem_parameters {W : ℕ} (p : Coloring.Parameter W) : p ∈ parameters W := by
  apply List.mem_ofFn.mpr
  exact ⟨⟨index p,index_lt p⟩,parameter_index p⟩

theorem reduction_correct {n W : ℕ} (x : Fin n→ℤ) (hn : n ≤ 2^W) :
    Coloring.DistinctZeroSum x ↔
      ∃ t, ∃ ht : t < count W, ColorClassLists.witness (parameter ht) x := by
  rw [ColorClassLists.reduction_correct x hn]
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨index p,index_lt p,by simpa only [parameter_index] using hp⟩
  · rintro ⟨t,ht,hp⟩
    exact ⟨parameter ht,hp⟩

end ThreeSum.ColorParameters
