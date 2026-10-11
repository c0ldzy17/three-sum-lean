import Submission.ThreeSum.SourceFiniteInputs

/-! # Exact reusable memory boundary after the actual wanted-pair output -/

namespace ThreeSum.EncodedColorWantedData

open Light WantedResidueKeys

def nextFree (out M : ℕ) (left right : ℕ → ℤ) (NL NR : ℕ) (shift : ℤ) : ℕ :=
  LightWantedSetup.pairBase out NL NR M+2*total M left right NL NR shift

theorem header_le_nextFree (out M : ℕ) (left right : ℕ → ℤ) (NL NR : ℕ) (shift : ℤ) :
    out+4 ≤ nextFree out M left right NL NR shift := by
  unfold nextFree LightWantedSetup.pairBase LightSourceBucketSetup.next LightWantedSetup.bucketBase
    LightWantedSetup.rightCodes LightWantedSetup.leftCodes
  omega

theorem nextFree_read {μ : ℕ → ℤ} {out M NL NR : ℕ} {left right : ℕ → ℤ} {shift : ℤ}
    (H : LightWantedSetup.Output μ out M left right NL NR shift) :
    μ (out+2)=(nextFree out M left right NL NR shift : ℤ) := H.2.2.1

theorem of_kept {μ ν : ℕ → ℤ} {out M NL NR bound : ℕ} {left right : ℕ → ℤ} {shift : ℤ}
    (H : LightWantedSetup.Output μ out M left right NL NR shift)
    (K : Kept μ ν bound) (hb : nextFree out M left right NL NR shift ≤ bound) :
    LightWantedSetup.Output ν out M left right NL NR shift := by
  have hh := (header_le_nextFree out M left right NL NR shift).trans hb
  obtain ⟨hcount,hpair,hnext,hshift,ps,hlen,hnodup,hmem,hrows⟩ := H
  refine ⟨(K _ (by omega)).trans hcount,(K _ (by omega)).trans hpair,
    (K _ (by omega)).trans hnext,(K _ (by omega)).trans hshift,ps,hlen,hnodup,hmem,?_⟩
  apply hrows.of_kept K
  rw [WantedPairs.cells_length,hlen]
  exact hb

end ThreeSum.EncodedColorWantedData
