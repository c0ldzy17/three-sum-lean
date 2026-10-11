import Submission.ThreeSum.LightBlockCoefficients

/-!
# Reading constructed block coefficients in the flat mask order

The imperative coefficient constructor writes rows. The mask evaluator reads
one flat array. These lemmas identify the two layouts, including empty ground
sets, and specialize them to the unchanged schedule-occurrence encoding.
-/

namespace ThreeSum.BlockCoefficientRows

open BlockRows BlockIndex BlockEncoding GlobalEncoding LocalCoverBounds

def flat (J L p : ℕ) (sel : ℕ → ℕ) (w : ℕ → ℕ → ℕ) : ℕ → ℕ :=
  OneHotMask.extend fun i : Fin (J*L) =>
    let c := (coordEquiv J L).symm i
    p^c.1.val * w (sel c.1.val) c.2.val

theorem rows_flat {μ : ℕ → ℤ} {dst0 dst1 J L p : ℕ}
    {sel : ℕ → ℕ} {w0 w1 : ℕ → ℕ → ℕ}
    (hrows : LightBlockCoefficients.Rows μ dst0 dst1 L p sel w0 w1 J) :
    (∀ i < J*L, μ (dst0+i) = (flat J L p sel w0 i : ℤ)) ∧
    (∀ i < J*L, μ (dst1+i) = (flat J L p sel w1 i : ℤ)) := by
  have read (dst : ℕ) (w : ℕ → ℕ → ℕ)
      (hr : ∀ a < J, ∀ x < L, μ (dst+a*L+x) = (p^a*w (sel a) x : ℤ)) :
      ∀ i < J*L, μ (dst+i) = (flat J L p sel w i : ℤ) := by
    intro i hi
    let c := (coordEquiv J L).symm ⟨i,hi⟩
    have hc : c.1.val*L+c.2.val = i := by
      rw [← coordEquiv_val]
      exact congrArg Fin.val ((coordEquiv J L).apply_symm_apply ⟨i,hi⟩)
    have hf : flat J L p sel w i = p^c.1.val*w (sel c.1.val) c.2.val := by
      simp only [flat,OneHotMask.extend,hi,dite_true]
      rfl
    rw [hf]
    simpa only [Nat.add_assoc,hc,Nat.cast_mul,Nat.cast_pow] using
      hr c.1.val c.1.isLt c.2.val c.2.isLt
  exact ⟨read dst0 w0 (fun a ha x hx => (hrows a ha x hx).1),
    read dst1 w1 (fun a ha x hx => (hrows a ha x hx).2)⟩

theorem flat_le {J L p U M : ℕ} {sel : ℕ → ℕ} {w : ℕ → ℕ → ℕ}
    (hp : 1 ≤ p) (hsel : ∀ j < J, sel j < M)
    (hbound : ∀ s < M, ∀ i < L, w s i ≤ U) {i : ℕ} (hi : i < J*L) :
    flat J L p sel w i ≤ p^J*U := by
  let c := (coordEquiv J L).symm ⟨i,hi⟩
  change (if h : i < J*L then _ else 0) ≤ _
  rw [dif_pos hi]
  exact Nat.mul_le_mul (Nat.pow_le_pow_right hp (Nat.le_of_lt c.1.isLt))
    (hbound _ (hsel _ c.1.isLt) _ c.2.isLt)

def occurrenceIndices {h J : ℕ} (o : Occurrences h J) : ℕ → ℕ :=
  OneHotMask.extend fun i => (o i).val

@[simp] theorem occurrenceIndices_fin {h J : ℕ} (o : Occurrences h J) (i : Fin J) :
    occurrenceIndices o i.val = (o i).val := by
  exact OneHotMask.extend_fin _ i

def mapRow (h : ℕ) (b : Bool) (s : ℕ) : ℕ → ℕ :=
  if hs : s < scheduleSize h then
    OneHotMask.extend fun i : Fin (512*h) => (mapAt h ⟨s,hs⟩ (i,b)).val
  else fun _ => 0

@[simp] theorem mapRow_fin {h : ℕ} (b : Bool) (s : Occurrence h) (i : Fin (512*h)) :
    mapRow h b s.val i.val = (mapAt h s (i,b)).val := by
  simp only [mapRow,s.isLt,dite_true,OneHotMask.extend_fin]

theorem occurrenceIndices_lt {h J : ℕ} (o : Occurrences h J) {j : ℕ} (hj : j < J) :
    occurrenceIndices o j < scheduleSize h := by
  exact (occurrenceIndices_fin o ⟨j,hj⟩).trans_lt (o ⟨j,hj⟩).isLt

theorem mapRow_le {h : ℕ} (b : Bool) {s i : ℕ}
    (hs : s < scheduleSize h) (hi : i < 512*h) : mapRow h b s i ≤ localPrime h := by
  rw [mapRow_fin b ⟨s,hs⟩ ⟨i,hi⟩]
  exact Nat.le_of_lt (ZMod.val_lt _)

theorem flat_coefficient {h J : ℕ} (o : Occurrences h J) (b : Bool) :
    flat J (512*h) (localPrime h) (occurrenceIndices o) (mapRow h b) =
      OneHotMask.extend (coefficient o b ∘ (coordEquiv J (512*h)).symm) := by
  unfold flat
  apply congrArg OneHotMask.extend
  funext i
  simp only [occurrenceIndices_fin,mapRow_fin,Function.comp_apply,coefficient]

theorem eval_left {h J : ℕ} (o : Occurrences h J)
    (S : Finset (Coord J (512*h))) :
    (OneHotMask.eval
      (flat J (512*h) (localPrime h) (occurrenceIndices o) (mapRow h false))
      (flat J (512*h) (localPrime h) (occurrenceIndices o) (mapRow h true))
      (J*(512*h)) (SubsetAddress.subsetMask (indexSet S)) : ℤ) = endpointLeft o S := by
  rw [flat_coefficient,flat_coefficient]
  exact maskHash_left o S

theorem eval_right {h J : ℕ} (o : Occurrences h J)
    (S : Finset (Coord J (512*h))) :
    (OneHotMask.eval
      (flat J (512*h) (localPrime h) (occurrenceIndices o) (mapRow h true))
      (flat J (512*h) (localPrime h) (occurrenceIndices o) (mapRow h false))
      (J*(512*h)) (SubsetAddress.subsetMask (indexSet S)) : ℤ) = endpointRight o S := by
  rw [flat_coefficient,flat_coefficient]
  exact maskHash_right o S

end ThreeSum.BlockCoefficientRows
