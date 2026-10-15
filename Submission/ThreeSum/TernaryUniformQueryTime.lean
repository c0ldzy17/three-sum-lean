import Submission.ThreeSum.TernaryActualPrefixRuntime
import Submission.ThreeSum.TernaryArenaQueryTime
import Submission.ThreeSum.TernaryArenaFrontBounds
import Submission.ThreeSum.TernaryArenaAllocation

noncomputable section
namespace ThreeSum.TernaryUniformQueryTime
open TernaryArenaSourceSetup TernaryLocalParameters TernaryCoverGoodMaps
open TernaryActualPrefixRuntime TernaryArenaAllocation TernaryArenaPrefixFootprints
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]

/-- One proof-only budget for all actual typed queries in a prefix loop. -/
def maximum (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (R : ℕ) : ℕ :=
  (Finset.range (R+1)).sup fun j => TernaryArenaCountReady.queryTime (m:=m) (r:=j) I
    (valueCap (r:=j) maps cap I)

theorem le_maximum (maps : Fin F→Weight m p) (cap : ℕ) (I : Input)
    {j R : ℕ} (hj : j≤R) :
    TernaryArenaCountReady.queryTime (m:=m) (r:=j) I (valueCap (r:=j) maps cap I)≤
      maximum maps cap I R :=
  Finset.le_sup (f:=fun j => TernaryArenaCountReady.queryTime (m:=m) (r:=j) I
    (valueCap (r:=j) maps cap I)) (Finset.mem_range.mpr (by omega))

theorem envelope_mono {j R : ℕ} (hj : j≤R) :
    TernaryCountFrontendBudget.envelope m j≤TernaryCountFrontendBudget.envelope m R := by
  have hlen : fixedLength (j*m)≤fixedLength (R*m) := by
    unfold fixedLength
    gcongr
  have hlog : 0≤Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have hent : 0≤TernaryParameters.queryEntropy := TernaryParameters.analytic_admissibility.2.1.le
  unfold TernaryCountFrontendBudget.envelope
  apply div_le_div_of_nonneg_right _ TernaryParameters.gibbs_parameters.2.2.1.le
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hlen) hlog) hent

def coefficient (m D E κ : ℕ) : ℕ :=100000*(widthCoefficient m D E κ)^3

private theorem sup_cast_le {α : Type*} (s : Finset α) (f : α→ℕ) (B : ℝ)
    (hB : 0≤B) (h : ∀a∈s,(f a:ℝ)≤B) : ((s.sup f:ℕ):ℝ)≤B := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hB
  | @insert a s ha ih =>
    rw [Finset.sup_insert,Nat.cast_max]
    exact max_le (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

/-- Uniform repricing uses the final prefix's query envelope. Earlier stages
retain their actual record counts; no bound by their smaller query maximum
is asserted. -/
theorem maximum_bound {n U κ D E : ℕ} (maps : Fin F→Weight m p) (cap : ℕ) (I : Input)
    (hm : 0<m) (hn : 1<n) (hU : U≤n^κ)
    (hword : ∀j≤TernaryCoverScale.radixLength m n,
      TernaryFrontendResources.eulerBound (N m j) (valueCap (r:=j) maps cap I)≤D*(n+U+1)^E) :
    (maximum maps cap I (TernaryCoverScale.radixLength m n):ℝ)≤
      (coefficient m D E κ:ℝ)*(TernaryCoverScale.radixLength m n+1:ℕ)^3*
        TernaryCountFrontendBudget.envelope m (TernaryCoverScale.radixLength m n) := by
  unfold maximum
  apply sup_cast_le
  · exact mul_nonneg (by positivity) (TernaryCountFrontendBudget.envelope_pos _ _).le
  intro j hj
  have hj' : j≤TernaryCoverScale.radixLength m n := by
    have := Finset.mem_range.mp hj
    omega
  have htime := TernaryArenaQueryTime.bound (m:=m) (r:=j) I (valueCap (r:=j) maps cap I)
  have hwidth := canonical_width_bound maps cap I hm hn hj' hU (hword j hj')
  have hw : ((TernaryCountFrontendBudget.width (N m j)
      (nearConfig (m:=m) (r:=j) I false (valueCap (r:=j) maps cap I))
      (nearConfig (m:=m) (r:=j) I true (valueCap (r:=j) maps cap I)):ℕ):ℝ)^3≤
      ((widthCoefficient m D E κ:ℝ)*(TernaryCoverScale.radixLength m n+1:ℕ))^3 := by
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hwidth) 3
  have he := envelope_mono (m:=m) hj'
  have hh := mul_le_mul
    (mul_le_mul_of_nonneg_left hw (by norm_num : (0:ℝ)≤100000)) he
    (TernaryCountFrontendBudget.envelope_pos m j).le (by positivity)
  exact htime.trans (by simpa only [coefficient,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,mul_pow,mul_assoc] using hh)

/-- The already allocated division words provide the uniform logarithmic
width bound, including arbitrary actual source values and multiplicities. -/
theorem allocated_word {τ cap M b K H drift scale n U r : ℕ}
    (maps : Fin F→Weight m p) (Alloc : Allocation maps τ cap M b K H drift scale) (I : Input)
    (hr : r≤Nat.clog M (n^2)) (hB : I.nB≤n) (hC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightTernaryDimensions.J M b n U))
    (hweight : I.weightCap≤weight H (4^fixedLength m) U) :
    TernaryFrontendResources.eulerBound (N m r) (valueCap (r:=r) maps cap I)≤
      (256*(Alloc.D+1))*(n+U+1)^Alloc.E := by
  have hfront := TernaryArenaFrontBounds.front_bounds (r:=r) maps τ cap M b K H drift scale I n U
    hB hC hO hweight
  have hdivision := hfront.2.2.2.2.2.2.2.1
  have hfits := (Alloc.fits n U r hr).nearDivision
  change _≤TernaryArenaLayout.capacity Alloc.D Alloc.E (n+U)
  omega

end ThreeSum.TernaryUniformQueryTime
