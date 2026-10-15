import Submission.ThreeSum.LightTernaryTensorFactoryReady
import Submission.ThreeSum.PolynomialResources

/-! Explicit polynomial word and storage resources for the executed fourth
tensor and paired-potential kernels. The circuit degree depends only on K. -/
noncomputable section
namespace ThreeSum.TernaryTensorWordResources
open LightTernaryPairedPolynomial TernaryPairedColumnEnumeration StageBounds

def polynomialBound (K V : ℕ) : ℕ :=
  (polynomial K).coefficient.toNat*(V+1)^(polynomial K).degree

theorem polynomial_bound (K V : ℕ) :
    (polynomial K).bound (V : ℤ)≤(polynomialBound K V : ℤ) := by
  have hc := (polynomial K).coefficient_pos
  have he : ((polynomial K).coefficient.toNat : ℤ)=(polynomial K).coefficient :=
    Int.toNat_of_nonneg (by omega)
  simpa [polynomialBound,he] using (polynomial K).bound_polynomial (by positivity : (0 : ℤ)≤V)

theorem polynomial_expression (K V : ℕ) :
    (polynomial K).coefficient*((V : ℤ)+1)^(polynomial K).degree=(polynomialBound K V : ℤ) := by
  have hc := (polynomial K).coefficient_pos
  have he : ((polynomial K).coefficient.toNat : ℤ)=(polynomial K).coefficient :=
    Int.toNat_of_nonneg (by omega)
  simp [polynomialBound,he]

def potentialWord (K J V : ℕ) : ℕ :=
  10*((J+2)^(width K+1)+(J+2)^width K+width K+(J+2)+2)+
    2*((J+2)^width K+1)*(polynomialBound K V+1)

theorem potential_word_bound (K J V : ℕ) :
    LightTernaryPairedPotential.word K (J+2) V≤(potentialWord K J V : ℤ) := by
  have hp := polynomial_bound K V
  unfold LightTernaryPairedPotential.word potentialWord
  push_cast
  gcongr

def word (K J count V sourceU : ℕ) : ℕ :=
  potentialWord K J V+polynomialBound K V+
    count*(J+2)^width K*polynomialBound K V+
    LightWeightRow.word 4 (J+2) ((J+2)^4) 0 1+
    J+3+count+(J+2)^4+(sourceU+1)^2+1

def need (K J count V sourceU : ℕ) : Light.Need :=
  ⟨word K J count V sourceU,count*(J+2)^4+width K+(width K+1)+12,5⟩

theorem kernel_guard (K J count V sourceU : ℕ) :
    LightTernaryPairedPotential.word K (J+2) V≤(word K J count V sourceU : ℤ) := by
  apply (potential_word_bound K J V).trans
  exact_mod_cast (show potentialWord K J V≤word K J count V sourceU by unfold word; omega)

theorem polynomial_guard (K J count V sourceU : ℕ) :
    (polynomial K).coefficient*((V : ℤ)+1)^(polynomial K).degree≤(word K J count V sourceU : ℤ) := by
  rw [polynomial_expression]
  exact_mod_cast (show polynomialBound K V≤word K J count V sourceU by unfold word; omega)

theorem sum_guard (K J count V sourceU : ℕ) :
    (count : ℤ)*((J+2)^width K : ℕ)*(polynomial K).bound V≤(word K J count V sourceU : ℤ) := by
  have hp := mul_le_mul_of_nonneg_left (polynomial_bound K V)
    (show (0 : ℤ)≤(count : ℤ)*((J+2)^width K : ℕ) by positivity)
  apply hp.trans
  exact_mod_cast (show count*(J+2)^width K*polynomialBound K V≤word K J count V sourceU by
    unfold word; omega)

theorem remaining_guards (K J count V sourceU : ℕ) :
    (sourceU+1)^2≤word K J count V sourceU ∧
    J+3≤word K J count V sourceU ∧ count≤word K J count V sourceU ∧
    (J+2)^4≤word K J count V sourceU ∧
    LightWeightRow.word 4 (J+2) ((J+2)^4) 0 1≤word K J count V sourceU := by
  unfold word
  omega

private def Poly (f : ℕ→ℕ) : Prop :=∃ a : ℝ, PowerBound f a
private theorem Poly.const (c : ℕ) : Poly (fun _ => c) :=⟨0,PowerBound.const c⟩
private theorem Poly.add {f g : ℕ→ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun n => f n+g n) := by
  obtain ⟨a,ha⟩ := hf
  obtain ⟨b,hb⟩ := hg
  exact ⟨max a b,(ha.mono_exponent (le_max_left _ _)).add_same
    (hb.mono_exponent (le_max_right _ _))⟩
private theorem Poly.mul {f g : ℕ→ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun n => f n*g n) := by
  obtain ⟨a,ha⟩ := hf
  obtain ⟨b,hb⟩ := hg
  exact ⟨a+b,ha.mul hb⟩
private theorem Poly.pow {f : ℕ→ℕ} (hf : Poly f) (k : ℕ) : Poly (fun n => f n^k) := by
  obtain ⟨a,ha⟩ := hf
  exact ⟨k*a,ha.pow k⟩

theorem polyNeed {J count V sourceU : ℕ→ℕ} {a b c e : ℝ}
    (hJ : PowerBound J a) (hc : PowerBound count b) (hV : PowerBound V c)
    (hU : PowerBound sourceU e) (K : ℕ) :
    Light.PolyNeed (fun n _U => need K (J n) (count n) (V n) (sourceU n)) := by
  have hj : Poly J :=⟨a,hJ⟩
  have hcount : Poly count :=⟨b,hc⟩
  have hv : Poly V :=⟨c,hV⟩
  have hu : Poly sourceU :=⟨e,hU⟩
  have hj2 := hj.add (Poly.const 2)
  have hjw := hj2.pow (width K)
  have hpv : Poly (fun n => polynomialBound K (V n)) := by
    exact (Poly.const _).mul ((hv.add (Poly.const 1)).pow _)
  have hp : Poly (fun n => potentialWord K (J n) (V n)) := by
    exact ((Poly.const 10).mul (((((hj2.pow (width K+1)).add hjw).add
      (Poly.const (width K))).add hj2).add (Poly.const 2))).add
      (((Poly.const 2).mul (hjw.add (Poly.const 1))).mul (hpv.add (Poly.const 1)))
  have hr : Poly (fun n => LightWeightRow.word 4 (J n+2) ((J n+2)^4) 0 1) := by
    simpa only [LightWeightRow.word] using (Poly.const 4).mul
      (((((((hj2.pow 4).add (hj2.pow 5)).add hj2).add (Poly.const 4)).add
        (Poly.const 0)).add (Poly.const 1)).add (Poly.const 2))
  have hw : Poly (fun n => word K (J n) (count n) (V n) (sourceU n)) := by
    exact (((((((((hp.add hpv).add ((hcount.mul hjw).mul hpv)).add hr).add hj).add
      (Poly.const 3)).add hcount).add (hj2.pow 4)).add
      ((hu.add (Poly.const 1)).pow 2)).add (Poly.const 1))
  have hcells : Poly (fun n => count n*(J n+2)^4+width K+(width K+1)+12) :=
    (((hcount.mul (hj2.pow 4)).add (Poly.const (width K))).add
      (Poly.const (width K+1))).add (Poly.const 12)
  obtain ⟨aw,hw⟩ := hw
  obtain ⟨ac,hcells⟩ := hcells
  apply PolynomialResources.polyNeed_of_separate_envelopes hw hcells (PowerBound.const 5) 0 0 0
  · intro n U
    simp only [need,pow_zero,mul_one,le_refl]
  · intro n U
    simp only [need,pow_zero,mul_one,le_refl]
  · intro n U
    simp only [need,pow_zero,mul_one,le_refl]

end ThreeSum.TernaryTensorWordResources
