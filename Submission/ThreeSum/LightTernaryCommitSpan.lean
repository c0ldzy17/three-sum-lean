import Submission.ThreeSum.LightArray

namespace ThreeSum.LightTernaryCommitSpan
open Light

def program : Program :=[copyBody]
def time (J rows : ℕ) : ℕ :=copyTime (rows*J)

/-- The selected expanded digit-span catalog is copied back into the fixed
old catalog. Both reserved catalog buffers can therefore have fixed pointers
through every prefix, with only their actual row count increasing. -/
theorem program_meets {lim : Limits} {oldCatalog newCatalog J rows d : ℕ}
    (μ : ℕ → ℤ) (hw : (lim.space : ℤ)≤lim.word)
    (hApart : oldCatalog+rows*J≤newCatalog)
    (hSpace : newCatalog+rows*J≤lim.space) :
    Meets lim program 0 d [newCatalog,oldCatalog,rows*J] μ (time J rows)
      (fun _ ν => (∀ k<rows, ∀ i<J,
          ν (oldCatalog+J*k+i)=μ (newCatalog+J*k+i)) ∧
        SameOutside μ ν oldCatalog (rows*J)) := by
  have hc := copy_meets (P := program) (p := 0) (d := d) (μ := μ)
    (src := newCatalog) (dst := oldCatalog) (n := rows*J) rfl hw hSpace
      (by omega) (Or.inr hApart)
  apply hc.mono le_rfl
  intro r ν hv
  refine ⟨?_,hv.2⟩
  intro k hk i hi
  have hp := Nat.mul_le_mul_left J (show k+1≤rows by omega)
  rw [Nat.mul_add,Nat.mul_one] at hp
  have hindex : J*k+i<rows*J := by nlinarith [Nat.mul_comm J rows]
  simpa only [Nat.add_assoc] using hv.1 (J*k+i) hindex

end ThreeSum.LightTernaryCommitSpan
