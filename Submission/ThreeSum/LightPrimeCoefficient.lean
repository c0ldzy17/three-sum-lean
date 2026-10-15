import Submission.ThreeSum.LightSmallDivide

/-! Actual modular arithmetic on prime-field coefficient representatives.
The modulus is supplied as an ordinary natural word; all divisions are the
already costed finite counting procedure. -/
namespace ThreeSum.LightPrimeCoefficient
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

/-- `acc + x*y (mod p)`, for coefficients represented in `[0,p)`. -/
def mulAddBody (pDivide : ℕ) : Stmt :=
  .call pDivide [v 0 +' v 1 *' v 2,v 3] 4 ;;
  .set 0 (v 0 +' v 1 *' v 2 -' v 4 *' v 3)

def word (p : ℕ) : ℕ := 4*(p+1)^2

def mulAddTime (p : ℕ) : ℕ := 20*(p+1)^2+100

theorem mulAdd_meets {pMain pDivide acc x y p : ℕ}
    (hmain : P[pMain]?=some (mulAddBody pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body) (μ : ℕ → ℤ)
    (hd : d<lim.depth) (hp : 0<p) (ha : acc<p) (hx : x<p) (hy : y<p)
    (hword : (word p : ℤ)≤lim.word) :
    Meets lim P pMain d [acc,x,y,p] μ (mulAddTime p)
      (fun r ν => r=(((acc+x*y)%p : ℕ) : ℤ) ∧ ν=μ) := by
  let n := acc+x*y
  have hn : n≤(p+1)^2 := by dsimp [n]; nlinarith
  have hprod : (n/p)*p≤n := Nat.div_mul_le_self n p
  have hq : n/p≤n := Nat.div_le_self n p
  have hmod : n%p≤n := Nat.mod_le n p
  have hb (z : ℕ) (hz : z≤word p) : (z : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr hz).trans hword
  have hacc := hb acc (by unfold word; nlinarith)
  have hxx := hb x (by unfold word; nlinarith)
  have hyy := hb y (by unfold word; nlinarith)
  have hpp := hb p (by unfold word; nlinarith)
  have hxy := hb (x*y) (by unfold word; nlinarith)
  have hnn := hb n (by unfold word; nlinarith)
  have hqq := hb (n/p) (by unfold word; nlinarith)
  have hpprod := hb ((n/p)*p) (by unfold word; nlinarith)
  have hmodWord := hb (n%p) (by unfold word; nlinarith)
  have hdivideWord := hb (n+p+2) (by unfold word; nlinarith)
  have hnInt : (acc : ℤ)+(x : ℤ)*(y : ℤ)=(n : ℤ) := by simp [n]
  have hprodInt : (((n/p : ℕ) : ℤ)*(p : ℤ))=(((n/p)*p : ℕ) : ℤ) := by push_cast; rfl
  have hrem : (n : ℤ)-((n/p : ℕ) : ℤ)*(p : ℤ)=((n%p : ℕ) : ℤ) := by
    have hh : n%p+(n/p)*p=n := by simpa only [Nat.mul_comm] using Nat.mod_add_div n p
    have hz : ((n%p : ℕ) : ℤ)+((n/p : ℕ) : ℤ)*(p : ℤ)=(n : ℤ) := by exact_mod_cast hh
    omega
  have htimeBound : (acc+x*y)/p≤p^2+2*p+1 := by have hh := hq.trans hn; dsimp [n] at hh; nlinarith
  have hprodIntWord : (n : ℤ)/(p : ℤ)*(p : ℤ)≤lim.word := by
    simpa only [Int.natCast_mul,Int.natCast_ediv] using hpprod
  have hprodIntNonneg : 0≤(n : ℤ)/(p : ℤ)*(p : ℤ) := by positivity
  apply Meets.of_body hmain
  unfold mulAddBody mulAddTime
  light_call (LightSmallDivide.meets (d := d+1) (a := n) (b := p) hdivide μ hdivideWord)
    using LightSmallDivide.time with q ν ⟨hqval,hν⟩
  subst ν
  subst q
  have hremExpanded : (acc : ℤ)+(x : ℤ)*(y : ℤ)-((n/p : ℕ) : ℤ)*(p : ℤ)=((n%p : ℕ) : ℤ) := by simpa only [hnInt] using hrem
  simp only [Int.natCast_ediv] at hremExpanded
  light_set (n%p : ℕ) using hprodInt,hremExpanded,LightSmallDivide.time
  exact ⟨rfl,rfl⟩

end ThreeSum.LightPrimeCoefficient
