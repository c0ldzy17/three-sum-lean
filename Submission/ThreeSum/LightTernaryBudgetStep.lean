import Submission.ThreeSum.LightArray

namespace ThreeSum.LightTernaryBudgetStep
open Light
set_option maxHeartbeats 3000000

/-- Six consecutive stored selector denominators and thresholds. -/
def body : Stmt :=
  .set 5 (M (v 0) *' v 1) ;;
  .set 6 (M (v 0 +' k 1) *' v 1) ;;
  .set 7 (M (v 0 +' k 2) *' v 2) ;;
  .set 8 (M (v 0 +' k 3) *' k 9) ;;
  .set 9 (M (v 0 +' k 4) *' k 9) ;;
  .set 10 (M (v 0 +' k 5) *' v 3 *' v 4) ;;
  .store (v 0) (v 5) ;;
  .store (v 0 +' k 1) (v 6) ;;
  .store (v 0 +' k 2) (v 7) ;;
  .store (v 0 +' k 3) (v 8) ;;
  .store (v 0 +' k 4) (v 9) ;;
  .store (v 0 +' k 5) (v 10) ;;
  .set 0 (k 0)

def oldValues (xB xC xP tB tC tP : ℕ) : List ℤ := [xB,xC,xP,tB,tC,tP]
def nextValues (p a b s xB xC xP tB tC tP : ℕ) : List ℤ :=
  [xB*p,xC*p,xP*a,tB*9,tC*9,tP*b*s]

def changed (μ : ℕ→ ℤ) (base p a b s xB xC xP tB tC tP : ℕ) : ℕ→ ℤ :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update μ base (xB*p)) (base+1) (xC*p))
      (base+2) (xP*a)) (base+3) (tB*9)) (base+4) (tC*9)) (base+5) (tP*b*s)

theorem meets {lim : Limits} {P : Program} {main d base p a b s xB xC xP tB tC tP : ℕ}
    (hmain : P[main]?=some body) (μ : ℕ→ ℤ)
    (hw : (lim.space:ℤ)≤lim.word) (h9 : (9:ℤ)≤lim.word) (hspace : base+6≤lim.space)
    (hread : Seg μ base (oldValues xB xC xP tB tC tP))
    (hnext : ∀ x∈nextValues p a b s xB xC xP tB tC tP, x≤lim.word)
    (hmid : ((tP*b:ℕ):ℤ)≤lim.word) :
    Meets lim P main d [base,p,a,b,s] μ 250
      (fun r ν=>r=0 ∧ ν=changed μ base p a b s xB xC xP tB tC tP) := by
  have hxB : μ base=(xB:ℤ) := by simpa [oldValues] using hread 0 (by simp [oldValues])
  have hxC : μ (base+1)=(xC:ℤ) := by simpa [oldValues] using hread 1 (by simp [oldValues])
  have hxP : μ (base+2)=(xP:ℤ) := by simpa [oldValues] using hread 2 (by simp [oldValues])
  have htB : μ (base+3)=(tB:ℤ) := by simpa [oldValues] using hread 3 (by simp [oldValues])
  have htC : μ (base+4)=(tC:ℤ) := by simpa [oldValues] using hread 4 (by simp [oldValues])
  have htP : μ (base+5)=(tP:ℤ) := by simpa [oldValues] using hread 5 (by simp [oldValues])
  have haddr (i : ℕ) : ((base:ℤ)+(i:ℤ)).toNat=base+i := by omega
  have ha1 : ((base:ℤ)+1).toNat=base+1 := by omega
  have ha2 : ((base:ℤ)+2).toNat=base+2 := by omega
  have ha3 : ((base:ℤ)+3).toNat=base+3 := by omega
  have ha4 : ((base:ℤ)+4).toNat=base+4 := by omega
  have ha5 : ((base:ℤ)+5).toNat=base+5 := by omega
  have hb := hnext (xB*p) (by simp [nextValues])
  have hc := hnext (xC*p) (by simp [nextValues])
  have hp := hnext (xP*a) (by simp [nextValues])
  have htb := hnext (tB*9) (by simp [nextValues])
  have htc := hnext (tC*9) (by simp [nextValues])
  have htp := hnext (tP*b*s) (by simp [nextValues])
  have hnB : (0:ℤ)≤(xB:ℤ)*(p:ℤ) := by positivity
  have hnC : (0:ℤ)≤(xC:ℤ)*(p:ℤ) := by positivity
  have hnP : (0:ℤ)≤(xP:ℤ)*(a:ℤ) := by positivity
  have hnT : (0:ℤ)≤(tP:ℤ)*(b:ℤ)*(s:ℤ) := by positivity
  apply Meets.of_body hmain
  unfold body
  light_set (xB*p:ℕ) using hxB,haddr
  light_set (xC*p:ℕ) using hxC,ha1
  light_set (xP*a:ℕ) using hxP,ha2
  light_set (tB*9:ℕ) using htB,ha3
  light_set (tC*9:ℕ) using htC,ha4
  light_set (tP*b*s:ℕ) using htP,ha5
  light_store base (xB*p:ℕ)
  light_store (base+1) (xC*p:ℕ)
  light_store (base+2) (xP*a:ℕ)
  light_store (base+3) (tB*9:ℕ)
  light_store (base+4) (tC*9:ℕ)
  light_store (base+5) (tP*b*s:ℕ)
  light_set (0:ℕ)
  exact ⟨by simp, rfl⟩

theorem changed_seg (μ : ℕ→ ℤ) (base p a b s xB xC xP tB tC tP : ℕ) :
    Seg (changed μ base p a b s xB xC xP tB tC tP) base
      (nextValues p a b s xB xC xP tB tC tP) := by
  intro i hi
  simp only [nextValues,List.length_cons,List.length_nil] at hi
  have he : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl <;> simp [changed,nextValues]

theorem changed_outside (μ : ℕ→ ℤ) (base p a b s xB xC xP tB tC tP : ℕ) :
    SameOutside μ (changed μ base p a b s xB xC xP tB tC tP) base 6 := by
  intro i hi
  have h0 : i≠base := by omega
  have h1 : i≠base+1 := by omega
  have h2 : i≠base+2 := by omega
  have h3 : i≠base+3 := by omega
  have h4 : i≠base+4 := by omega
  have h5 : i≠base+5 := by omega
  simp [changed,Function.update_of_ne,h0,h1,h2,h3,h4,h5]

theorem nextValues_budget (p a b s j N U : ℕ) :
    nextValues p a b s (p^j) (p^j) (a^j) (9^j*N) (9^j*N) (U*(b*s)^j)=
      oldValues (p^(j+1)) (p^(j+1)) (a^(j+1)) (9^(j+1)*N) (9^(j+1)*N) (U*(b*s)^(j+1)) := by
  simp only [nextValues,oldValues,pow_succ,Nat.cast_mul,Nat.cast_pow,List.cons.injEq]
  repeat' constructor
  all_goals ring

end ThreeSum.LightTernaryBudgetStep
