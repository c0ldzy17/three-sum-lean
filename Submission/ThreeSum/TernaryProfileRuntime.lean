import Submission.ThreeSum.TernaryConcreteProfile
import Submission.ThreeSum.TernaryActualGlobalQueryRuntime
import Submission.ThreeSum.TernaryFastProgramBudget
import Submission.ThreeSum.TernarySolverEndBridge

noncomputable section
namespace ThreeSum.TernaryConcreteProfile.Profile
open Light StageBounds TernaryLocalParameters TernaryActualColoredRuntime
open TernaryActualPrefixRuntime TernaryOversizeOverhead Filter
open scoped Topology
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {κ : ℕ}

def wordD (P : Profile κ) : ℕ :=256*(P.allocation.D+1)

/-- The actual per-color envelope depends only on the fixed magnitude
exponent's profile and original input length. -/
def colorTime (P : Profile κ) : ℕ→ℕ :=
  TernaryActualGlobalQueryRuntime.uniformTime P.K P.k 19 3 P.m P.F P.wordD
    P.allocation.E κ P.p P.H P.radix

def fastTime (P : Profile κ) (n : ℕ) : ℕ :=
  LightTernaryFastProgramProof.time P.M P.radix P.p P.K κ (P.colorTime n) n

theorem preparation_le_colorTime (P : Profile κ) (n : ℕ) :
    LightTernaryColorPreparationProof.time n
      (LightTernaryDimensions.J P.M P.radix n (n^κ)) (n^κ)+
      LightTernaryArenaTemplate.time P.allocation.E+LightTernaryInitialBudgets.time P.K+10000≤
        P.colorTime n := by
  unfold colorTime TernaryActualGlobalQueryRuntime.uniformTime TernaryActualColoredRuntime.uniformTime
  change _≤LightTernaryColorPreparationProof.time n
    (LightTernaryDimensions.J P.M P.radix n (n^κ)) (n^κ)+_+_+_+10000+_
  omega

theorem colorTime_large (P : Profile κ) (n : ℕ) : 10000≤P.colorTime n := by
  have hh := preparation_le_colorTime P n
  omega

theorem color_powerBound (P : Profile κ) : PowerBound P.colorTime exponent := by
  have hδ : 0≤microAllowance P.K := by unfold microAllowance; positivity
  have hroom := (selected_room P.large).le
  exact TernaryActualGlobalQueryRuntime.PB
    P.blockPositive P.radix_gt_one hδ P.carry hroom

theorem fast_powerBound (P : Profile κ) : PowerBound P.fastTime exponent :=
  TernaryFastProgramBudget.full P.blockPositive P.radix_gt_one P.color_powerBound
    (by norm_num [exponent])

def hybridProgram (P : Profile κ) : Program :=
  TernaryHybridCore.program P.program P.main κ P.cutoff

def hybridMain (P : Profile κ) : ℕ :=P.program.length+5

def hybridNeed (P : Profile κ) : ℕ→ℕ→Need :=
  TernaryHybridResources.need P.need κ P.cutoff

def hybridTime (P : Profile κ) : ℕ→ℕ→ℕ :=
  TernaryHybridCore.time P.fastTime κ P.cutoff

theorem hybrid_polyNeed (P : Profile κ) : PolyNeed P.hybridNeed :=
  TernaryHybridResources.poly_need P.need P.polyNeed κ P.cutoff

theorem hybrid_time_target (P : Profile κ) :
    ∀ᶠ n : ℕ in atTop,
      timeUpTo P.hybridTime n ((n:ℝ)^(κ:ℝ))≤(n:ℝ)^(1921/1000:ℝ) :=
  TernaryHybridCosts.timeUpTo_eventually P.fast_powerBound
    (by norm_num [exponent]) (by norm_num [exponent]) κ P.cutoff

end ThreeSum.TernaryConcreteProfile.Profile
