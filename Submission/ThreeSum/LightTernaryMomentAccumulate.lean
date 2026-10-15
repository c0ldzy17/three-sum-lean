import Submission.ThreeSum.LightArray

/-! Costed zeroing and signed channel accumulation for the moment matrix. -/
namespace ThreeSum.LightTernaryMomentAccumulate
open Light

def body : Stmt := pass 3 (v 2) (v 0)
  (M (v 0 +' v 3) +' M (v 1 +' v 3))

def time (count : ℕ) : ℕ := 24*count+10

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {p dst src count U : ℕ}
    (hmain : P[p]?=some body) (μ : ℕ→ℤ) (accum channel : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (hdst : dst+count≤lim.space) (hsrc : src+count≤lim.space)
    (hsep : LightArray.SourceSafe src dst count)
    (haccum : ∀ i<count, μ (dst+i)=accum i)
    (hchannel : ∀ i<count, μ (src+i)=channel i)
    (hbounded : ∀ i<count, |accum i|≤(U : ℤ) ∧ |channel i|≤(U : ℤ))
    (hword : 2*(U : ℤ)≤lim.word) :
    Meets lim P p d [dst,src,count] μ (time count)
      (fun _ ν => (∀ i<count, ν (dst+i)=accum i+channel i) ∧ SameOutside μ ν dst count) := by
  apply Meets.of_body hmain
  unfold body time
  refine Ends.pass (fun i => accum i+channel i) ?round
    ⟨fun i hi => by dsimp only; exact wrote_done hi,by light_keep⟩ hw hdst rfl rfl
  case round =>
    intro i hi
    have hrA := LightArray.source_read (μ := μ)
      (f := fun i => accum i+channel i) (show LightArray.SourceSafe dst dst count from Or.inl rfl) hi
    have hrB := LightArray.source_read (μ := μ)
      (f := fun i => accum i+channel i) hsep hi
    have hA := haccum i hi
    have hB := hchannel i hi
    have hbounds := hbounded i hi
    have hU : (U : ℤ)≤lim.word := by omega
    have hsum : |accum i+channel i|≤lim.word :=
      (abs_add_le _ _).trans ((add_le_add hbounds.1 hbounds.2).trans (by omega))
    have hs := abs_le.mp hsum
    have ha := abs_le.mp hbounds.1
    have hb := abs_le.mp hbounds.2
    light_side [hrA,hrB,hA,hB]

theorem zero_meets {p matrix terms count : ℕ}
    (hmain : P[p]?=some fillBody) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hspace : matrix+terms*count≤lim.space) :
    Meets lim P p d [matrix,terms*count,0] μ (fillTime (terms*count))
      (fun _ ν => (∀ k<terms, ∀ i<count, ν (matrix+k*count+i)=0) ∧
        SameOutside μ ν matrix (terms*count)) := by
  apply (fill_meets hmain hw hspace).mono (by omega)
  rintro r ν ⟨hseg,hkeep⟩
  refine ⟨?_,hkeep⟩
  intro k hk i hi
  have hm := Nat.mul_le_mul_right count (show k+1≤terms by omega)
  simp only [Nat.add_mul,one_mul] at hm
  have hj : k*count+i<terms*count := by omega
  have hv := hseg (k*count+i) (by simpa using hj)
  simpa [List.getElem_replicate,Nat.add_assoc] using hv

/-- An accumulation writes one matrix row and preserves every other row,
including rows already completed by earlier channels. -/
theorem other_row_kept {μ ν : ℕ→ℤ} {matrix count k l : ℕ}
    (hkeep : SameOutside μ ν (matrix+k*count) count) (hkl : k≠l) :
    ∀ i<count, ν (matrix+l*count+i)=μ (matrix+l*count+i) := by
  intro i hi
  apply hkeep
  by_cases hlk : l<k
  · left
    have hm := Nat.mul_le_mul_right count (show l+1≤k by omega)
    simp only [Nat.add_mul,one_mul] at hm
    omega
  · right
    have hm := Nat.mul_le_mul_right count (show k+1≤l by omega)
    simp only [Nat.add_mul,one_mul] at hm
    omega

def program : Program := [body,fillBody]

end ThreeSum.LightTernaryMomentAccumulate
