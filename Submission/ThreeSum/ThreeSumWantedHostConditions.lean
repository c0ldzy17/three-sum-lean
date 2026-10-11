import Submission.ThreeSum.ThreeSumWantedHostData
import Submission.ThreeSum.DenseGuardAuxiliary
import Submission.ThreeSum.BandRawAColorOriginal

/-!
# Uniform size conditions and original-color semantics for the wanted consumer

The cutoff is chosen before any memory, color, or original array. The
auxiliary-prime separation premise is proved for the actual generated pool.
-/

namespace ThreeSum.ThreeSumWantedHostConditions

open Light Scales BandScales Filter RawIncidences BandRawA ColorClassLists
open scoped Topology

set_option maxHeartbeats 1600000
set_option maxRecDepth 12000

structure Ready (k n : ℕ) : Prop where
  positive : 0<n
  half : 0<microHalf (inputBits n)
  radix : 4≤Scales.radix n
  divisor : divisorBudget k n*primeWindow n≤candidateCount n*(4*(k+2)*(inputBits n+1))
  separates : ∀ z : ℤ, z≠0 → z.natAbs≤3*n^k → ∃ l∈DenseGuard.actualAux n, ¬l∣z

theorem ready_eventually (k : ℕ) : ∀ᶠ n : ℕ in atTop, Ready k n := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    (microHalf_tendsto_atTop.comp inputBits_tendsto_atTop).eventually (eventually_ge_atTop 1),
    radix_eventually_ge_four,actual_divisor_budget k,DenseGuard.actual_aux_separates k]
      with n hn hh hr hd hs
  simp only [Function.comp_apply] at hh
  exact ⟨by omega,by omega,hr,hd,hs⟩

theorem exists_cutoff (k : ℕ) : ∃ N : ℕ, ∀ n≥N, Ready k n :=
  eventually_atTop.mp (ready_eventually k)

noncomputable def cutoff (k : ℕ) : ℕ := Classical.choose (exists_cutoff k)

theorem ready_of_cutoff_le {k n : ℕ} (hn : cutoff k≤n) : Ready k n :=
  Classical.choose_spec (exists_cutoff k) n hn

def OriginalZero (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : Prop :=
  let rs := sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC
  ∃ t∈finiteAllProducts A.length B.length C.length (bandSize n) rs,
    difference (fun i => valueAt A.length (bandSize n) rs (fun j => A.getD j 0) i.val)
      (fun i => B.getD i.val 0) (fun i => C.getD i.val 0) t=0

theorem original_zero_iff_witness {μ : ℕ→ℤ} {free n : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    OriginalZero n A B C hsA hsB hsC ↔ ColorClassLists.witness color x := by
  rw [← finite_color_iff color x (bandSize_pos n) hsA hsB hsC
    H.normalized.2.1.2.2.1 H.normalized.2.2.1.2.2.1 H.normalized.2.2.2.1.2.2.1]
  unfold OriginalZero finiteEquation
  apply exists_congr
  intro t
  apply and_congr_right
  intro _
  dsimp only [difference]
  constructor <;> intro he <;> omega

theorem actual_separation {μ : ℕ→ℤ} {free n k : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hn : Ready k n) (hx : ∀ i, |x i|≤((n^k : ℕ) : ℤ)) :
    let rs := sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC
    ∀ t∈finiteAllProducts A.length B.length C.length (bandSize n) rs,
      difference (fun i => valueAt A.length (bandSize n) rs (fun j => A.getD j 0) i.val)
        (fun i => B.getD i.val 0) (fun i => C.getD i.val 0) t≠0 →
      ∃ l∈DenseGuard.actualAux n, ¬l∣difference
        (fun i => valueAt A.length (bandSize n) rs (fun j => A.getD j 0) i.val)
        (fun i => B.getD i.val 0) (fun i => C.getD i.val 0) t := by
  dsimp only
  intro t ht hz
  apply hn.separates _ hz
  obtain ⟨ha,hb,hc⟩ := finite_product_original_values
    H.normalized.2.1.2.2.1 H.normalized.2.2.1.2.2.1 H.normalized.2.2.2.1.2.2.1 ht
  have haBound := LightColorBands.class_bounded color x 0 1 (by norm_num) hx _ ha
  have hbBound := LightColorBands.class_bounded color x 1 1 (by norm_num) hx _ hb
  have hcBound := LightColorBands.class_bounded color x 2 (-1) (by norm_num) hx _ hc
  have hdiff : |difference
      (fun i => valueAt A.length (bandSize n)
        (sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC) (fun j => A.getD j 0) i.val)
      (fun i => B.getD i.val 0) (fun i => C.getD i.val 0) t|≤((3*n^k : ℕ) : ℤ) := by
    unfold difference
    have hfirst := abs_sub_le (C.getD t.2.2.val 0) 0 (B.getD t.2.1.val 0)
    have hlast := abs_sub_le (C.getD t.2.2.val 0-B.getD t.2.1.val 0) 0
      (valueAt A.length (bandSize n)
        (sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC) (fun j => A.getD j 0) t.1.val)
    simp only [sub_zero,zero_sub,abs_neg] at hfirst hlast
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    omega
  exact_mod_cast (show ((difference
      (fun i => valueAt A.length (bandSize n)
        (sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC) (fun j => A.getD j 0) i.val)
      (fun i => B.getD i.val 0) (fun i => C.getD i.val 0) t).natAbs : ℤ)≤((3*n^k : ℕ) : ℤ) by
    simpa only [Int.natCast_natAbs] using hdiff)

end ThreeSum.ThreeSumWantedHostConditions
