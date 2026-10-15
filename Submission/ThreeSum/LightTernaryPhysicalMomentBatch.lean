import Submission.ThreeSum.LightTernaryMomentBatch
import Submission.ThreeSum.TernaryPhysicalMomentSupport

/-! The actual detector batch for positive physical pair measures.
Repeated records and equal modes are grouped by the proved finite support
construction; no injective-mode or nonzero-weight advice is an input. -/
noncomputable section
namespace ThreeSum.LightTernaryPhysicalMomentBatch
open Light TernaryPhysicalMomentSupport FiniteMomentZeroDetector
open scoped BigOperators

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {H pMain records count originalA originalCount matrix scratch U : ℕ}
    (S : LightTernaryMomentBatch.Procs H P pMain)
    (Pair : ℕ→Type*) [∀ i, Fintype (Pair i)]
    (mode mass : ∀ i, Pair i→ℤ) (position : ℕ→ℕ) (A : ℕ→ℤ) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+1<lim.depth)
    (hrecords : records+3*count≤scratch) (hAarray : originalA+originalCount≤scratch)
    (hmatrix : matrix+(2*H+1)*count≤scratch) (hspace : scratch+(2*H+1)≤lim.space)
    (hpositions : ∀ i<count, position i<originalCount)
    (hpositionRead : ∀ i<count, μ (records+3*i)=(position i : ℤ))
    (hAread : ∀ j<originalCount, μ (originalA+j)=A j)
    (hA : ∀ j<originalCount, |A j|≤(U : ℤ))
    (hword : max (U : ℤ) (LightMomentDeterminant.wordBound U H)≤lim.word)
    (hpositive : ∀ i<count, ∀ a, 0<mass i a)
    (hsupport : ∀ i<count, (support (mode i)).card≤H)
    (hmabs : ∀ i<count, ∀ k≤2*H, |∑ a, mass i a*mode i a^k|≤(U : ℤ))
    (hm : ∀ i<count, ∀ k≤2*H, μ (matrix+k*count+i)=∑ a, mass i a*mode i a^k) :
    Meets lim P pMain d [records,count,originalA,originalCount,matrix,scratch] μ
      (LightTernaryMomentBatch.time H count)
      (fun r ν => r=(if ∃ i<count, ∃ a, mode i a=A (position i) then 1 else 0 : ℤ) ∧
        Kept μ ν scratch) := by
  classical
  let t : ℕ→ℕ := fun i => (support (mode i)).card
  let v : ∀ i, Fin (t i)→ℤ := fun i => values (mode i)
  let w : ∀ i, Fin (t i)→ℤ := fun i => weights (mode i) (mass i)
  have hv : ∀ i<count, Function.Injective (v i) := fun i hi => values_injective (mode i)
  have hwgt : ∀ i<count, ∀ a, w i a≠0 := by
    intro i hi a
    exact ne_of_gt (weights_positive (mode i) (mass i) (hpositive i hi) a)
  have hmabs' : ∀ i<count, ∀ k≤2*H, |moment (v i) (w i) k|≤(U : ℤ) := by
    intro i hi k hk
    change |moment (values (mode i)) (weights (mode i) (mass i)) k|≤(U : ℤ)
    rw [grouped_moment]
    exact hmabs i hi k hk
  have hm' : ∀ i<count, ∀ k≤2*H,
      μ (matrix+k*count+i)=moment (v i) (w i) k := by
    intro i hi k hk
    change μ (matrix+k*count+i)=moment (values (mode i)) (weights (mode i) (mass i)) k
    rw [grouped_moment]
    exact hm i hi k hk
  have hh := S.meets (μ := μ) position t A v w hw hd hrecords hAarray hmatrix hspace
    hpositions hpositionRead hAread hA hword hv hwgt hsupport hmabs' hm'
  have he : (∃ i<count, ∃ a, v i a=A (position i)) ↔
      ∃ i<count, ∃ a, mode i a=A (position i) := by
    constructor
    · rintro ⟨i,hi,ha⟩
      exact ⟨i,hi,(target_iff (mode i) (A (position i))).mp ha⟩
    · rintro ⟨i,hi,ha⟩
      exact ⟨i,hi,(target_iff (mode i) (A (position i))).mpr ha⟩
  simpa only [he] using hh

end ThreeSum.LightTernaryPhysicalMomentBatch
