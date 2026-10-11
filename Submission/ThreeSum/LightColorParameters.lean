import Submission.ThreeSum.ColorParameters
import Submission.ThreeSum.LightSmallDivide
import Submission.ThreeSum.LightArray
import Mathlib.Tactic.IntervalCases

/-!
# Execute one coloring-parameter slot

Five exact scalar divisions recover the two binary coordinates and four
ternary colors. Only six output cells are written, so the outer color loop
can reuse this record. The complete family has only polynomially many slots
in the binary index width.
-/

namespace ThreeSum.LightColorParameters

open Light ColorParameters

set_option maxHeartbeats 1600000
set_option maxRecDepth 9000

def body (pDivide : ℕ) : Stmt :=
  .call pDivide [v 1,k 3] 3 ;;
  .call pDivide [v 3,k 3] 4 ;;
  .call pDivide [v 4,k 3] 5 ;;
  .call pDivide [v 5,k 3] 6 ;;
  .call pDivide [v 6,v 0] 7 ;;
  .set 8 (v 6 -' v 7 *' v 0) ;;
  .set 9 (v 5 -' v 6 *' k 3) ;;
  .set 10 (v 4 -' v 5 *' k 3) ;;
  .set 11 (v 3 -' v 4 *' k 3) ;;
  .set 12 (v 1 -' v 3 *' k 3) ;;
  .store (v 2) (v 7) ;;
  .store (v 2 +' k 1) (v 8) ;;
  .store (v 2 +' k 2) (v 9) ;;
  .store (v 2 +' k 3) (v 10) ;;
  .store (v 2 +' k 4) (v 11) ;;
  .store (v 2 +' k 5) (v 12) ;;
  .set 0 (v 2)

def time (t : ℕ) : ℕ := 100*t+2000

theorem remainder (a b : ℕ) :
    (a : ℤ)-((a/b : ℕ) : ℤ)*(b : ℤ)=((a%b : ℕ) : ℤ) := by
  have hh : (a/b)*b+a%b=a := by simpa only [Nat.mul_comm] using Nat.div_add_mod a b
  have hz : ((a/b : ℕ) : ℤ)*(b : ℤ)+((a%b : ℕ) : ℤ)=(a : ℤ) := by exact_mod_cast hh
  omega

variable {lim : Limits} {P : Program} {d W t free : ℕ} {μ : ℕ → ℤ}

theorem meets {pMain pDivide : ℕ} (hp : P[pMain]?=some (body pDivide))
    (hdiv : P[pDivide]?=some LightSmallDivide.body)
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : free+6 ≤ lim.space)
    (hword : ((t+W+10 : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim P pMain d [W,t,free] μ (time t)
      (fun result ν => result=(free : ℤ) ∧ Seg ν free (data W t) ∧ SameOutside μ ν free 6) := by
  have hq3 : t/3 ≤ t := Nat.div_le_self _ _
  have hq9 : t/9 ≤ t := Nat.div_le_self _ _
  have hq27 : t/27 ≤ t := Nat.div_le_self _ _
  have hq81 : t/81 ≤ t := Nat.div_le_self _ _
  have hiLe : t/81/W ≤ t := (Nat.div_le_self _ _).trans hq81
  have call (a b : ℕ) (ha : a ≤ t) (hb : b ≤ W+3) :
      Meets lim P pDivide (d+1) [a,b] μ (20*t+40)
        (fun result ν => result=((a/b : ℕ) : ℤ) ∧ ν=μ) :=
    (LightSmallDivide.meets hdiv μ ((Int.ofNat_le.mpr (by omega)).trans hword)).mono_time
      ((LightSmallDivide.time_bound a b).trans (by omega))
  have prodFit (a b : ℕ) (ha : a ≤ t) :
      ((a/b : ℕ) : ℤ)*(b : ℤ) ≤ lim.word := by
    have hh := (Nat.div_mul_le_self a b).trans ha
    have hh' : ((a/b : ℕ) : ℤ)*(b : ℤ) ≤ (t : ℤ) := by exact_mod_cast hh
    omega
  have hprodW := prodFit (t/81) W hq81
  have hprod3 := prodFit t 3 le_rfl
  have hprod9 := prodFit (t/3) 3 hq3
  have hprod27 := prodFit (t/9) 3 hq9
  have hprod81 := prodFit (t/27) 3 hq27
  have hremW := remainder (t/81) W
  have hrem3 := remainder t 3
  have hrem9 := remainder (t/3) 3
  have hrem27 := remainder (t/9) 3
  have hrem81 := remainder (t/27) 3
  norm_num only [Nat.div_div_eq_div_mul] at hprod9 hprod27 hprod81 hrem9 hrem27 hrem81
  have hnW : (0 : ℤ) ≤ ((t/81/W : ℕ) : ℤ)*(W : ℤ) := by positivity
  have hn3 : (0 : ℤ) ≤ ((t/3 : ℕ) : ℤ)*3 := by positivity
  have hn9 : (0 : ℤ) ≤ ((t/9 : ℕ) : ℤ)*3 := by positivity
  have hn27 : (0 : ℤ) ≤ ((t/27 : ℕ) : ℤ)*3 := by positivity
  have hn81 : (0 : ℤ) ≤ ((t/81 : ℕ) : ℤ)*3 := by positivity
  have hprodWI : (t : ℤ)/81/(W : ℤ)*(W : ℤ) ≤ lim.word := by
    simpa only [Int.natCast_ediv,Nat.cast_ofNat] using hprodW
  have hnWI : (0 : ℤ) ≤ (t : ℤ)/81/(W : ℤ)*(W : ℤ) := by
    exact mul_nonneg (Int.ediv_nonneg
      (Int.ediv_nonneg (Int.natCast_nonneg _) (by decide)) (Int.natCast_nonneg _))
      (Int.natCast_nonneg _)
  have hremWI : (t : ℤ)/81-(t : ℤ)/81/(W : ℤ)*(W : ℤ)=(t : ℤ)/81%(W : ℤ) := by
    simpa only [Int.natCast_ediv,Int.natCast_emod,Nat.cast_ofNat] using hremW
  apply Meets.of_body hp
  unfold body time
  light_call (call t 3 le_rfl (by omega)) with q3 μ₁ ⟨hq3',hμ₁⟩
  subst μ₁
  light_call (call (t/3) 3 hq3 (by omega)) using hq3' with q9 μ₂ ⟨hq9',hμ₂⟩
  subst μ₂
  norm_num only [Nat.div_div_eq_div_mul] at hq9'
  light_call (call (t/9) 3 hq9 (by omega)) using hq9' with q27 μ₃ ⟨hq27',hμ₃⟩
  subst μ₃
  norm_num only [Nat.div_div_eq_div_mul] at hq27'
  light_call (call (t/27) 3 hq27 (by omega)) using hq27' with q81 μ₄ ⟨hq81',hμ₄⟩
  subst μ₄
  norm_num only [Nat.div_div_eq_div_mul] at hq81'
  have hq81ZI : q81=(t : ℤ)/81 := by simpa only [Int.natCast_ediv,Nat.cast_ofNat] using hq81'
  light_call (call (t/81) W hq81 (by omega)) using hq81' with i μ₅ ⟨hi,hμ₅⟩
  subst μ₅
  have hiZI : i=(t : ℤ)/81/(W : ℤ) := by
    simpa only [Int.natCast_ediv,Nat.cast_ofNat] using hi
  light_set (t/81%W : ℕ) using hq81',hi,hremW,hremWI,hq81ZI,hiZI
  light_set (t/27%3 : ℕ) using hq27',hq81',hrem81
  light_set (t/9%3 : ℕ) using hq9',hq27',hrem27
  light_set (t/3%3 : ℕ) using hq3',hq9',hrem9
  light_set (t%3 : ℕ) using hq3',hrem3
  light_store free (t/81/W : ℕ) using hi
  light_store (free+1) (t/81%W : ℕ)
  light_store (free+2) (t/27%3 : ℕ)
  light_store (free+3) (t/9%3 : ℕ)
  light_store (free+4) (t/3%3 : ℕ)
  light_store (free+5) (t%3 : ℕ)
  light_set (free : ℕ)
  refine ⟨rfl,?_,by light_keep⟩
  intro j hj
  have hj' : j < 6 := by simpa only [data,List.length_cons,List.length_nil] using hj
  interval_cases j <;> simp [data]

def program : Program := [body 1,LightSmallDivide.body]

theorem program_meets (hw : (lim.space : ℤ) ≤ lim.word) (hspace : free+6 ≤ lim.space)
    (hword : ((t+W+10 : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim program 0 d [W,t,free] μ (time t)
      (fun result ν => result=(free : ℤ) ∧ Seg ν free (data W t) ∧ SameOutside μ ν free 6) :=
  meets rfl rfl hw hspace hword hd

theorem parameter_meets (ht : t < count W)
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : free+6 ≤ lim.space)
    (hword : ((t+W+10 : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim program 0 d [W,t,free] μ (time t)
      (fun result ν => result=(free : ℤ) ∧ Seg ν free (fields (parameter ht)) ∧ SameOutside μ ν free 6) := by
  simpa only [fields_parameter] using program_meets hw hspace hword hd

end ThreeSum.LightColorParameters
