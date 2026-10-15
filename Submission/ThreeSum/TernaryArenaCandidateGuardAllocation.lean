import Submission.ThreeSum.TernaryArenaCandidateGuard
import Submission.ThreeSum.TernaryArenaAllocationResources
import Submission.ThreeSum.TernaryArenaPrimitiveBounds

noncomputable section
namespace ThreeSum.TernaryArenaCandidateGuardAllocation
open Light TernaryLocalParameters TernaryCoverGoodMaps TernaryArenaLayout
open TernaryArenaSourceSetup TernaryArenaSeedCandidate TernaryArenaPrefixFootprints
open TernaryArenaAllocation LightTernarySeedScoreFactory
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000

/-- The fixed arena hardware need discharges every primitive candidate
resource guard, including the actual number of menu seeds. -/
theorem resources {lim : Limits} {depth K H M b drift scale n U seed positionCap : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Alloc : Allocation maps τ cap M b K H drift scale)
    (I : Input) (A : Inputs) (D : Data (config p r I A seed))
    (hok : (TernaryArenaAllocationResources.need Alloc n U).Ok lim I.free depth)
    (hcap : I.capacity=capacity Alloc.D Alloc.E (n+U))
    (hr : r≤Nat.clog M (n^2)) (hJ : A.J=LightTernaryDimensions.J M b n U)
    (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightTernaryDimensions.J M b n U))
    (hpos : positionCap≤n) (hB : D.bB<p) (hC : D.bC<p) (hOut : D.bO<p)
    (hseed : seed<(p^(LightTernaryDimensions.dim M b p K n U))^2) :
    TernaryArenaCandidateGuard.Resources (lim := lim) (depth := depth)
      (positionCap := positionCap) maps τ I A D := by
  have HC : Fits I.capacity (numbers maps τ cap M b K H drift scale n U r) := by
    rw [hcap]
    exact Alloc.fits n U r hr
  obtain ⟨hend,hword,hdepth,hspace⟩ := TernaryArenaAllocationResources.ok Alloc hok
  rw [←hcap] at hend hword hdepth
  obtain ⟨_,_,hrequest,hcoord,hcatalog,hhist,hwanted,hdivide⟩ :=
    TernaryArenaPrimitiveBounds.spatial (r := r) maps τ cap M b K H drift scale I A n U
      hJ hnB hnC hO HC
  have hprim := TernaryArenaPrimitiveBounds.word_bound maps τ cap M b K H drift scale
    I A seed positionCap n U D hJ hnB hnC hpos hB hC hOut
  have hprimWord : (TernaryArenaSeedPrimitiveGuards.word maps τ I A seed positionCap D : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (hprim.trans HC.sourceWord)).trans hword
  have hrC : r≤I.capacity := by
    have hh := HC.depth
    dsimp only [numbers] at hh
    omega
  have hseeds := TernaryArenaAllocationResources.menu_square Alloc n U r hr
  rw [←hcap] at hseeds
  exact ⟨hrequest,hcoord,hcatalog,hhist,hwanted,hdivide,hprimWord,by omega,
    hseed.trans_le hseeds⟩

/-- The span commit stores only the digit restriction and fits the next
prefix catalog in one padded slot. -/
theorem new_span (maps : Fin F→Weight m p) (τ cap M b K H drift scale n U : ℕ)
    (I : Input) (A : Inputs) (hr : 0<r)
    (hJ : A.J=LightTernaryDimensions.J M b n U)
    (HC : Fits I.capacity (numbers maps τ cap M b K H drift scale n U r)) :
    A.J*p^(r-1)*p≤I.capacity := by
  have hh := HC.spanCells
  dsimp only [numbers] at hh
  have he : r-1+1=r := by omega
  rw [mul_assoc,←pow_succ,he]
  rw [hJ,mul_comm]
  exact hh

end ThreeSum.TernaryArenaCandidateGuardAllocation
