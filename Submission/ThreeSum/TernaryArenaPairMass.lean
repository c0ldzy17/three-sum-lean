import Submission.ThreeSum.TernaryArenaSourceSetup
import Submission.ThreeSum.TernaryNativeMomentBounds
import Submission.ThreeSum.TernarySignedPadding
import Submission.ThreeSum.ArithmeticStageBounds

/-! A pointwise polynomial magnitude envelope for the actual canonical
source pair records. This does not rely on asymptotic entropy estimates. -/
noncomputable section
namespace ThreeSum.TernaryArenaPairMass
open TernaryArenaSourceSetup TernaryCanonicalDictionaries TernaryNativeMomentBounds
open TernaryNativeCompleteFrontend
open TernaryCoverGoodMaps TernaryLocalParameters StageBounds
variable {p m F r : ℕ} [Fact p.Prime]

def tableWidth (maps : Fin F→Weight m p) (cap : ℕ) : ℕ :=
  max (localRecords maps cap false).length (localRecords maps cap true).length
def base (maps : Fin F→Weight m p) (cap : ℕ) : ℕ :=
  (tableWidth maps cap+1)^2*2^(fixedLength m)
def envelope (maps : Fin F→Weight m p) (cap M n : ℕ) : ℕ :=
  M^(base maps cap)*(n+1)^(2*base maps cap+2)

theorem fixed_pow_clog (M A n : ℕ) (hM : 1<M) :
    A^(Nat.clog M (n^2))≤M^A*(n+1)^(2*A) := by
  have hA : A≤M^A := (Nat.lt_pow_self hM).le
  have hc := Nat.clog_mono_right M (Nat.pow_le_pow_left (Nat.le_succ n) 2)
  have hp := (Nat.pow_le_pow_right hM.le hc).trans
    (TernarySignedPadding.clog_power_bound hM (by positivity : 0<(n+1)^2))
  calc
    _≤(M^A)^(Nat.clog M (n^2)) := Nat.pow_le_pow_left hA _
    _=(M^(Nat.clog M (n^2)))^A := by rw [← pow_mul,← pow_mul,Nat.mul_comm A]
    _≤(M*(n+1)^2)^A := Nat.pow_le_pow_left hp A
    _=_ := by rw [mul_pow,← pow_mul]

theorem pairMass_le (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (M n : ℕ)
    (hM : 1<M) (hr : r≤Nat.clog M (n^2)) (hl : I.nB≤n) (hc : I.nC≤n) :
    pairBound (setup (r := r) maps τ cap Q I)*2^(N m r)≤envelope maps cap M n := by
  let R := tableWidth maps cap+1
  let A := base maps cap
  have hlp : (localRecords maps cap false).length^r≤R^r :=
    Nat.pow_le_pow_left ((le_max_left _ _).trans (Nat.le_succ _)) _
  have hrp : (localRecords maps cap true).length^r≤R^r :=
    Nat.pow_le_pow_left ((le_max_right _ _).trans (Nat.le_succ _)) _
  have hsize : pairBound (setup (r := r) maps τ cap Q I)≤(n*R^r)*(n*R^r) := by
    dsimp [pairBound,setup,source,LightTernarySourceHost.size]
    exact Nat.mul_le_mul (Nat.mul_le_mul hl (by simpa using hlp))
      (Nat.mul_le_mul hc (by simpa using hrp))
  have hrep : (n*R^r)*(n*R^r)*2^(N m r)=n^2*A^r := by
    dsimp [A,base,N,R]
    simp only [mul_pow,← Nat.pow_mul]
    rw [show 2*r=r+r by omega,pow_add,Nat.mul_comm (fixedLength m) r]
    ring
  have hA : A^r≤M^A*(n+1)^(2*A) :=
    (Nat.pow_le_pow_right (show 1≤A by
      dsimp [A,base]
      exact Nat.succ_le_of_lt (by positivity)) hr).trans (fixed_pow_clog M A n hM)
  calc
    _≤(n*R^r)*(n*R^r)*2^(N m r) := Nat.mul_le_mul_right _ hsize
    _=n^2*A^r := hrep
    _≤(n+1)^2*(M^A*(n+1)^(2*A)) :=
      Nat.mul_le_mul (by nlinarith) hA
    _=envelope maps cap M n := by
      dsimp [envelope,A]
      rw [pow_add]
      ring

theorem envelope_powerBound (maps : Fin F→Weight m p) (cap M : ℕ) :
    PowerBound (envelope maps cap M) (2*base maps cap+2) := by
  change PowerBound (fun n => M^(base maps cap)*(n+1)^(2*base maps cap+2)) _
  have hplus : PowerBound (fun n => n+1) 1 :=
    ArithmeticStageBounds.identity_powerBound.add_same
      ((PowerBound.const 1).mono_exponent (by norm_num))
  simpa using (PowerBound.const (M^base maps cap)).mul
    (hplus.pow (2*base maps cap+2))

end ThreeSum.TernaryArenaPairMass
