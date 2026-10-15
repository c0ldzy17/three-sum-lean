import Submission.ThreeSum.TernaryArenaFixedParameters
import Submission.ThreeSum.TernaryExecutableParameters
import Submission.ThreeSum.TernaryColoredSolverNeed
import Submission.ThreeSum.TernaryFastProgramResources
import Submission.ThreeSum.TernaryActualRuntimeParameters

noncomputable section
namespace ThreeSum.TernaryConcreteProfile
open Light TernaryLocalParameters TernaryCoverGoodMaps TernaryCoverScale
open TernaryOversizePrime TernaryOversizeRates TernaryOversizeOverhead TernarySignedPadding
open TernaryArenaFixedParameters TernaryArenaBudgetExistence
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000

/-- All parameters are chosen once for the original magnitude exponent κ.
None depends on input values, color classes, or the field polynomial found
at runtime. -/
structure Profile (κ : ℕ) where
  K : ℕ
  t : ℕ
  m : ℕ
  cutoff : ℕ
  large : 100000000≤K
  basePositive : 0<t
  blockPositive : 0<m
  good : GoodBlock K m
  overhead : overheadCharge (selectedMoment K) 19 3 m<microAllowance K
  carry : carryExponent m (2^t) (κ : ℝ)<microAllowance K
  minor : (2*K).factorial*(2^t)^(2*K)<nativePrime K m
  basePrime : 2*(2^t)<nativePrime K m
  driftBound : (9*pairFactor m (familyLength K m) K)^4*(outputSize m)^(4*K+3)≤
    ((nativePrime K m)^(2*K))^4
  primeLarge : 9<nativePrime K m
  collisionRate : TernaryPairedCollisionRate.charge K m<(7483/10000 : ℝ)
  inputGuards : ∀n≥cutoff, InputGuards K m (2^t) κ n

theorem exists_profile (κ : ℕ) : Nonempty (Profile κ) := by
  have hKex : ∃K : ℕ, 100000000≤K := ⟨100000000,le_rfl⟩
  let K := Classical.choose hKex
  have hK : 100000000≤K := Classical.choose_spec hKex
  obtain ⟨t,m,n0,ht,hm,hg,ho,hc,hd,hp,hdrift,hp9,hcharge,hinputs⟩ :=
    simultaneous_cutoff hK κ 19 3 1
  exact ⟨⟨K,t,m,n0,hK,ht,by omega,hg,ho,hc,hd,hp,hdrift,hp9,hcharge,hinputs⟩⟩

def profile (κ : ℕ) : Profile κ := Classical.choice (exists_profile κ)

namespace Profile
variable {κ : ℕ}

def p (P : Profile κ) := nativePrime P.K P.m
def M (P : Profile κ) := outputSize P.m
def radix (P : Profile κ) := 2^P.t
def k (P : Profile κ) := selectedMoment P.K
def F (P : Profile κ) := TernaryExecutableParameters.F P.K P.m P.k
def cap (P : Profile κ) := TernaryExecutableParameters.cap P.K P.m
def threshold (P : Profile κ) := TernaryExecutableParameters.threshold P.K P.m P.k

instance (P : Profile κ) : Fact P.p.Prime := inferInstanceAs (Fact (nativePrime P.K P.m).Prime)

def maps (P : Profile κ) : Fin P.F→Weight P.m P.p :=
  TernaryExecutableParameters.maps P.K P.m P.k

def H (P : Profile κ) := 2*P.p^P.K
def drift (P : Profile κ) := 9*P.F*P.M*(TernaryGoodOutputCatalog.Rbar P.m)^P.K
def scale (P : Profile κ) := 2^((fixedPi P.m 2)*P.K)

theorem K_pos (P : Profile κ) : 0<P.K := by have := P.large; omega
theorem M_gt_one (P : Profile κ) : 1<P.M := by
  have hh := outputSize_ge_sixteen P.blockPositive
  exact lt_of_lt_of_le (by decide : 1<16) hh
theorem radix_gt_one (P : Profile κ) : 1<P.radix := by
  have hh := Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) (show 1≤P.t by have := P.basePositive; omega)
  exact lt_of_lt_of_le (by decide : 1<2) hh
theorem k_pos (P : Profile κ) : 0<P.k := selectedMoment_pos P.K_pos
theorem F_gt_one (P : Profile κ) : 1<P.F := TernaryExecutableParameters.family_gt_one P.K_pos P.m P.k

def output (P : Profile κ) : TernaryGoodOutputCatalog.Output P.m :=
  TernaryExecutableParameters.output P.K_pos P.blockPositive P.k_pos

def allocation (P : Profile κ) :
    TernaryArenaAllocation.Allocation P.maps P.threshold P.cap P.M P.radix P.K P.H P.drift P.scale :=
  TernaryArenaAllocation.allocation P.maps P.threshold P.cap P.M P.radix P.K P.H P.drift P.scale
    P.M_gt_one P.radix_gt_one

def color (P : Profile κ) : Program :=
  TernaryExecutable.color P.maps P.threshold P.cap P.M P.radix P.K
    P.allocation.D P.allocation.E P.output

def program (P : Profile κ) : Program :=
  TernaryExecutable.program P.maps P.threshold P.cap P.M P.radix P.K
    P.allocation.D P.allocation.E κ P.output

def main (P : Profile κ) := TernaryExecutable.main (p:=P.p) P.K

def colorNeed (P : Profile κ) : ℕ→ℕ→Need := TernaryColoredSolverNeed.fixedNeed P.allocation κ
def need (P : Profile κ) : ℕ→ℕ→Need :=
  TernaryFastProgramResources.need P.M P.radix P.p P.K κ P.colorNeed

theorem color_polyNeed (P : Profile κ) : PolyNeed P.colorNeed :=
  TernaryColoredSolverNeed.fixed_polyNeed P.allocation P.M_gt_one P.radix_gt_one κ

theorem polyNeed (P : Profile κ) : PolyNeed P.need :=
  TernaryFastProgramResources.polyNeed P.M_gt_one P.radix_gt_one κ P.color_polyNeed

theorem program_length (P : Profile κ) : P.program.length=P.main+1 :=
  TernaryExecutable.program_length _ _ _ _ _ _ _ _ _ _

theorem local_nonempty (P : Profile κ) (right : Bool) :
    0<(TernaryNativeCompleteFrontend.localRecords P.maps P.cap right).length :=
  TernaryExecutableParameters.source_nonempty P.K_pos P.blockPositive P.k_pos right

theorem cover (P : Profile κ) (a b : ZMod P.p) :
    ∃i, TernaryCoverFrequency.Covers P.m P.p P.cap P.threshold (P.maps i) (a,b) :=
  TernaryExecutableParameters.cover P.K_pos P.blockPositive P.k_pos a b

theorem tag_bound (P : Profile κ) : P.radix≤2*(4^fixedLength P.m)+1 :=
  radix_tag_bound P.K_pos P.radix_gt_one.le P.minor

end Profile
end ThreeSum.TernaryConcreteProfile
