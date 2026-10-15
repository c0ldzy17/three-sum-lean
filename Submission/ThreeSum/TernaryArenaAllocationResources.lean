import Submission.ThreeSum.TernaryArenaAllocation

noncomputable section
namespace ThreeSum.TernaryArenaAllocationResources
open Light TernaryArenaLayout TernaryArenaAllocation
open TernaryCoverGoodMaps
variable {p m F : ℕ} [Fact p.Prime]

def need {maps : Fin F→Weight m p} {τ cap M b K H drift scale : ℕ}
    (A : Allocation maps τ cap M b K H drift scale) (n U : ℕ) : Need :=
  let C := capacity A.D A.E (n+U)
  ⟨1000*C,slots*C,C+200⟩

theorem ok {maps : Fin F→Weight m p} {τ cap M b K H drift scale n U free d : ℕ}
    (A : Allocation maps τ cap M b K H drift scale) {lim : Limits}
    (H : (need A n U).Ok lim free d) :
    finish free (capacity A.D A.E (n+U))≤lim.space ∧
    (capacity A.D A.E (n+U) : ℤ)≤lim.word ∧
    d+100+capacity A.D A.E (n+U)≤lim.depth ∧ (lim.space : ℤ)≤lim.word := by
  have hc := H.cells
  have hw := H.word
  have hd := H.depth
  dsimp [need,finish,addr] at hc hw hd ⊢
  refine ⟨by omega,?_,by omega,H.space⟩
  have hb : capacity A.D A.E (n+U)≤1000*capacity A.D A.E (n+U) := by omega
  exact (Int.ofNat_le.mpr hb).trans hw

theorem polyNeed {maps : Fin F→Weight m p} {τ cap M b K H drift scale : ℕ}
    (A : Allocation maps τ cap M b K H drift scale) : PolyNeed (need A) := by
  let B := 1000*256*(A.D+1)
  have hB : B≤2^Nat.size B := (Nat.lt_size_self B).le
  refine ⟨Nat.size B,A.E,fun n U=>?_⟩
  have hbase : n+U+1≤(n+1)*(U+1) := by nlinarith
  have hpow := Nat.pow_le_pow_left hbase A.E
  have hbound : 1000*capacity A.D A.E (n+U)≤polyBound (Nat.size B) A.E [n,U] := by
    calc
      _=B*(n+U+1)^A.E := by unfold capacity B; ring
      _≤2^Nat.size B*((n+1)*(U+1))^A.E := Nat.mul_le_mul hB hpow
      _=_ := by simp [polyBound]
  have hC := capacity_pos A.D A.E (n+U)
  refine ⟨hbound,?_,?_⟩
  · apply le_trans _ hbound
    change slots*capacity A.D A.E (n+U)≤1000*capacity A.D A.E (n+U)
    unfold slots
    omega
  · apply le_trans _ hbound
    change capacity A.D A.E (n+U)+200≤1000*capacity A.D A.E (n+U)
    omega


theorem menu_square {maps : Fin F→Weight m p} {τ cap M b K H drift scale : ℕ}
    (A : Allocation maps τ cap M b K H drift scale) (n U j : ℕ)
    (hj : j≤Nat.clog M (n^2)) :
    (p^(LightTernaryDimensions.dim M b p K n U))^2≤capacity A.D A.E (n+U) := by
  have hc := (A.fits n U j hj).menuCells
  have hq := TernaryExtensionEncoding.menu_field_upper (p := p)
    (LightTernaryDimensions.J M b n U+2) K
  have hq' : p^(LightTernaryDimensions.dim M b p K n U)≤
      8*p^(4*K+1)*(LightTernaryDimensions.J M b n U+3) := by
    simpa only [LightTernaryDimensions.dim,show LightTernaryDimensions.J M b n U+2+1=
      LightTernaryDimensions.J M b n U+3 by omega] using hq
  have hp := Nat.pow_le_pow_left hq' 2
  have hm : (8*p^(4*K+1)*(LightTernaryDimensions.J M b n U+3))^2≤
      (8*p^(4*K+1)*(LightTernaryDimensions.J M b n U+3))^2*
        (LightTernaryDimensions.J M b n U+2) := Nat.le_mul_of_pos_right _ (by omega)
  exact hp.trans (hm.trans hc)

end ThreeSum.TernaryArenaAllocationResources
