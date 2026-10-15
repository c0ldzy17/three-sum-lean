import Submission.ThreeSum.LightSignedCoefficientLayout

namespace ThreeSum.LightSignedCoefficientMatrix
open Light
set_option maxHeartbeats 3000000

/-- source,destination,row count,raw digit count. -/
def body (pRow : ℕ) : Stmt :=
  .for 4 (v 2) (.call pRow [v 0 +' v 4 *' (v 3 +' k 2),v 1 +' v 4 *' (v 3 +' k 2),v 3] 5)

def time (rows J : ℕ) : ℕ := rows*(LightSignedCoefficientLayout.time J+100)+10

variable {lim : Limits} {P : Program} {depth : ℕ}

theorem meets {proc pRow src dst rows J U : ℕ}
    (hp : P[proc]?=some (body pRow)) (hrow : P[pRow]?=some LightSignedCoefficientLayout.body)
    (μ : ℕ → ℤ) (f : ℕ → ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth < lim.depth)
    (hsrc : src+rows*(J+2) ≤ dst) (hspace : dst+rows*(J+2) ≤ lim.space)
    (hread : ∀ r < rows, ∀ i < J+2, μ (src+r*(J+2)+i)=f r i)
    (hf : ∀ r < rows, ∀ i < J+2, |f r i| ≤ (U : ℤ))
    (hword : (U : ℤ) ≤ lim.word)
    (hrowsWord : (rows : ℤ) ≤ lim.word) (hJWord : ((J+2 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P proc depth [src,dst,rows,J] μ (time rows J)
      (fun _ ν => (∀ r < rows, ∀ i < J+2,
        ν (dst+r*(J+2)+i)=f r (TernarySignedLayout.offset J i)) ∧
        SameOutside μ ν dst (rows*(J+2))) := by
  apply Meets.of_body hp
  unfold body time
  refine Ends.for (fun r σ => ∃ Z ν,
      σ=⟨frame [src,dst,rows,J,r,Z],ν⟩ ∧
      (∀ s < r, ∀ i < J+2, ν (dst+s*(J+2)+i)=f s (TernarySignedLayout.offset J i)) ∧
      SameOutside μ ν dst (rows*(J+2))) rows
      (LightSignedCoefficientLayout.time J+90) ?start ?round ?done ?bound
  case start =>
    refine ⟨0,μ,?_,?_,SameOutside.refl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : State))
        ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro s hs; omega
  case round =>
    rintro r _ hr _ ⟨Z,ν,rfl,written,kept⟩
    have hend : r*(J+2)+(J+2) ≤ rows*(J+2) := by
      have hh := Nat.mul_le_mul_right (J+2) (show r+1 ≤ rows by omega)
      nlinarith
    have hoffWord : ((r*(J+2) : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (show r*(J+2) ≤ lim.space by omega)).trans hw
    have hsrcWord : ((src+r*(J+2) : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (show src+r*(J+2) ≤ lim.space by omega)).trans hw
    have hdstWord : ((dst+r*(J+2) : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (show dst+r*(J+2) ≤ lim.space by omega)).trans hw
    have hoffWordInt : (r : ℤ)*((J : ℤ)+2) ≤ lim.word := by exact_mod_cast hoffWord
    have hoffNonnegInt : 0 ≤ (r : ℤ)*((J : ℤ)+2) := by positivity
    have hsrcWordInt : (src : ℤ)+(r : ℤ)*((J : ℤ)+2) ≤ lim.word := by exact_mod_cast hsrcWord
    have hdstWordInt : (dst : ℤ)+(r : ℤ)*((J : ℤ)+2) ≤ lim.word := by exact_mod_cast hdstWord
    have hreadν (i : ℕ) (hi : i < J+2) : ν (src+r*(J+2)+i)=f r i := by
      rw [kept _ (Or.inl (by omega)),hread r hr i hi]
    light_call (LightSignedCoefficientLayout.meets (depth := depth+1) (src := src+r*(J+2))
      (dst := dst+r*(J+2)) (J := J) (U := U) hrow ν (f r) hw
      (by omega) (by omega) hreadν (hf r hr) hword)
      using LightSignedCoefficientLayout.time
      with R ξ ⟨values,hkeep⟩
    refine ⟨by simp,R,ξ,by simp [update_frame_setLocal],?_,?_⟩
    · intro s hs i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
      · have hoff : s*(J+2)+i < r*(J+2) := by
          have hh := Nat.mul_le_mul_right (J+2) (show s+1 ≤ r by omega)
          nlinarith
        rw [hkeep _ (Or.inl (by omega)),written s hs i hi]
      · simpa [Nat.add_assoc] using values i hi
    · intro a ha
      rw [hkeep a (by omega),kept a ha]
  case done => rintro _ _ ⟨Z,ν,rfl,written,kept⟩; exact ⟨written,kept⟩
  case bound => rintro r _ _ _ ⟨Z,ν,rfl,_,_⟩; light_side

end ThreeSum.LightSignedCoefficientMatrix
