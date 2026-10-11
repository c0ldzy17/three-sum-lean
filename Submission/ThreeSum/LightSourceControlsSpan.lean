import Submission.ThreeSum.SourceControlLayout
import Submission.ThreeSum.LightSourceControlsMax

/-! # Actual arithmetic computation of the exact source-bank span -/

namespace ThreeSum.LightSourceControlsSpan

open Light SourceControlLayout

set_option maxHeartbeats 2000000
set_option maxRecDepth 14000

/-- J, total width, compact capacity, occurrence count, and the two
logarithms needed by the retained stage workspace. -/
def body (pMax : ℕ) : Stmt :=
  .set 6 (v 1 +' k 1) ;;
  .set 7 (v 6 *' v 6 +' v 6) ;;
  .call pMax [v 7,v 5 +' k 2] 8 ;;
  .call pMax [v 8,v 4 +' k 5] 9 ;;
  .call pMax [v 9,v 0 +' k 1] 10 ;;
  .set 11 (k 5 *' v 2 +' k 2 *' v 1 +' k 4 +' k 2 *' v 6 *' v 2) ;;
  .set 0 (v 3 *' v 11 +' v 2 +' v 1 +' k 2 +' v 10)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain pMax J W K S logP logE : ℕ}
    (hmain : P[pMain]?=some (body pMax)) (hmax : P[pMax]?=some LightSourceControlsMax.body)
    (μ : ℕ → ℤ) (hd : d < lim.depth)
    (hword : (word J W K S logP logE : ℤ) ≤ lim.word) :
    Meets lim P pMain d [J,W,K,S,logP,logE] μ 1000
      (fun r ν => r=(span J W K S logP logE : ℤ) ∧ ν=μ) := by
  have hall (x : ℕ) (hx : x ≤ word J W K S logP logE) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hs : scratch J W logP logE ≤ word J W K S logP logE := by
    unfold word span
    omega
  have hu : (W+1)^2+(W+1) ≤ scratch J W logP logE :=
    (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hv : max ((W+1)^2+(W+1)) (logE+2) ≤ scratch J W logP logE :=
    (le_max_left _ _).trans (le_max_left _ _)
  have ht : max (max ((W+1)^2+(W+1)) (logE+2)) (logP+5) ≤ scratch J W logP logE :=
    le_max_left _ _
  have hstride : stride W K ≤ word J W K S logP logE := by unfold word; omega
  have hJ := hall J (by unfold word; omega)
  have hJ1 := hall (J+1) (by unfold word; omega)
  have h1 : (1 : ℤ) ≤ lim.word := hall 1 (by unfold word; omega)
  have hW := hall W (by unfold word; omega)
  have hK := hall K (by unfold word; omega)
  have hS := hall S (by unfold word; omega)
  have hP := hall logP (by unfold word; omega)
  have hE := hall logE (by unfold word; omega)
  have hW1 := hall (W+1) (by unfold word; omega)
  have hquad := hall ((W+1)^2) (by unfold word; omega)
  have hquad' : ((W : ℤ)+1)*((W : ℤ)+1) ≤ lim.word := by
    simpa only [Nat.cast_pow,Nat.cast_add,Nat.cast_one,pow_two,Nat.cast_mul] using hquad
  have hquadNonneg : (0 : ℤ) ≤ ((W : ℤ)+1)*((W : ℤ)+1) := by positivity
  have huZ := hall ((W+1)^2+(W+1)) (hu.trans hs)
  have huZ' : ((W : ℤ)+1)*((W : ℤ)+1)+((W : ℤ)+1) ≤ lim.word := by
    simpa only [Nat.cast_add,Nat.cast_pow,Nat.cast_mul,Nat.cast_one,pow_two] using huZ
  have hvZ := hall (max ((W+1)^2+(W+1)) (logE+2)) (hv.trans hs)
  have htZ := hall (max (max ((W+1)^2+(W+1)) (logE+2)) (logP+5)) (ht.trans hs)
  have hsZ := hall (scratch J W logP logE) hs
  have h5K := hall (5*K) ((by unfold stride; omega : 5*K ≤ stride W K).trans hstride)
  have h2W := hall (2*W) ((by unfold stride; omega : 2*W ≤ stride W K).trans hstride)
  have h2W1 := hall (2*(W+1)) (by unfold word stride; omega)
  have hfamily := hall (2*(W+1)*K)
    ((by unfold stride; omega : 2*(W+1)*K ≤ stride W K).trans hstride)
  have hfamilyZ : (2 : ℤ)*((W : ℤ)+1)*(K : ℤ) ≤ lim.word := by exact_mod_cast hfamily
  have hfamilyNonneg : (0 : ℤ) ≤ (2 : ℤ)*((W : ℤ)+1)*(K : ℤ) := by positivity
  have hstrZ := hall (stride W K) hstride
  have hstrZ' : 5*(K : ℤ)+2*(W : ℤ)+4+2*((W : ℤ)+1)*(K : ℤ) ≤ lim.word := by
    simpa only [stride,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hstrZ
  have hresult := hall (span J W K S logP logE) (by unfold word; omega)
  have hresult' : (S : ℤ)*(stride W K : ℤ)+(K : ℤ)+(W : ℤ)+2+(scratch J W logP logE : ℤ) ≤ lim.word := by
    simpa only [span,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hresult
  have hprod := hall (S*stride W K) (by unfold word span; omega)
  have hprodZ : (S : ℤ)*(stride W K : ℤ) ≤ lim.word := by exact_mod_cast hprod
  have hprodNonneg : (0 : ℤ) ≤ (S : ℤ)*(stride W K : ℤ) := by positivity
  apply Meets.of_body hmain
  unfold body
  light_set (W+1 : ℕ)
  light_set ((W+1)^2+(W+1) : ℕ) using pow_two
  have hm₁ := LightSourceControlsMax.meets (d := d+1) hmax μ hvZ
  light_call hm₁ with r₁ ν₁ ⟨hr₁,hν₁⟩
  subst ν₁
  have hm₂ := LightSourceControlsMax.meets (d := d+1) hmax μ htZ
  light_call hm₂ using hr₁ with r₂ ν₂ ⟨hr₂,hν₂⟩
  subst ν₂
  have hm₃ := LightSourceControlsMax.meets (d := d+1) hmax μ hsZ
  light_call hm₃ using hr₂,scratch with r₃ ν₃ ⟨hr₃,hν₃⟩
  subst ν₃
  have hr₃' : r₃=(scratch J W logP logE : ℤ) := hr₃
  light_set (stride W K : ℕ) using stride
  light_set (span J W K S logP logE : ℕ) using span,hr₃'
  exact ⟨rfl,rfl⟩

def program : Program := [body 1,LightSourceControlsMax.body]

end ThreeSum.LightSourceControlsSpan
