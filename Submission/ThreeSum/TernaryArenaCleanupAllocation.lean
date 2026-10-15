import Submission.ThreeSum.TernaryArenaFinalGuardAllocation
import Submission.ThreeSum.TernaryArenaCleanupLayout

noncomputable section
namespace ThreeSum.TernaryArenaCleanupAllocation
open Light TernaryArenaLayout TernaryArenaSourceSetup TernaryArenaPrefixFootprints
open TernaryCoverGoodMaps TernaryLocalParameters TernaryArenaAllocation TernaryExtensionEncoding
set_option maxHeartbeats 8000000
variable {p m F r J : ℕ} [Fact p.Prime]

theorem inputs {lim : Limits} {d M b K H drift scale n U : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Alloc : Allocation maps τ cap M b K H drift scale)
    (I : Input) (aBase nA bBase cBase : ℕ)
    (Row : (TernarySignedReduction.Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ) (μ : ℕ→ℤ)
    (hok : (TernaryArenaAllocationResources.need Alloc n U).Ok lim I.free d)
    (hcap : I.capacity=capacity Alloc.D Alloc.E (n+U)) (hr : r≤Nat.clog M (n^2))
    (hnB : I.nB≤n) (hnC : I.nC≤n) (hn : n<2^(2*N m r))
    (hA : aBase+nA≤I.free) (hB : bBase+I.nB≤I.free) (hC : cBase+I.nC≤I.free)
    (hreadA : ∀i<nA,μ (aBase+i)=A i) (hreadB : ∀i<I.nB,μ (bBase+i)=B i)
    (hreadC : ∀i<I.nC,μ (cBase+i)=C i)
    (hreadKB : ∀i<I.nB,μ (addr I.free I.capacity 4+i)=(keysB i : ℤ))
    (hreadKC : ∀i<I.nC,μ (addr I.free I.capacity 5+i)=(keysC i : ℤ))
    (hkB : ∀i<I.nB,keysB i=coefficientCode (TernaryNativeRequesterCoverage.sourceLeft Row U b (B i)))
    (hkC : ∀i<I.nC,keysC i=coefficientCode (TernaryNativeRequesterCoverage.sourceRight Row U b (C i)))
    (habsA : ∀i<nA,|A i|≤(U : ℤ)) (habsB : ∀i<I.nB,|B i|≤(U : ℤ))
    (habsC : ∀i<I.nC,|C i|≤(U : ℤ))
    (hsortedB : ∀i j,i<j→j<I.nB→B i<B j)
    (hsortedC : ∀i j,i<j→j<I.nC→C i<C j) :
    LightTernaryPreparedPostSelection.Inputs
      (TernaryArenaCleanupLayout.layout I.free I.capacity aBase nA bBase I.nB cBase I.nC
        (p^r) (2*N m r)) lim d U (2*N m r) μ A B C keysB keysC := by
  have HC : Fits I.capacity (numbers maps τ cap M b K H drift scale n U r) := by
    rw [hcap]
    exact Alloc.fits n U r hr
  obtain ⟨hend,hword,hdepth,hw⟩ := TernaryArenaAllocationResources.ok Alloc hok
  rw [←hcap] at hend hword hdepth
  have hcounts : 4*n+2≤I.capacity := by
    have hh := HC.reporterCells
    dsimp only [numbers] at hh
    omega
  have hL : 2*N m r+1≤I.capacity := by
    have hh := HC.prefixCells
    have he : N m r=fixedLength m*r := by unfold N; ring
    rw [he]
    dsimp only [numbers] at hh
    omega
  have hW := TernaryArenaFinalBounds.cleanup_words (r := r) maps τ cap M b K H drift scale n U
  have hq : p^r≤I.capacity := by
    have hh := hW.2.1.trans HC.reporterWord
    omega
  have hwCleanup : (((I.nB+I.nC+2^(2*N m r+1)+16 : ℕ)) : ℤ)≤lim.word := by
    have hh : I.nB+I.nC+2^(2*N m r+1)+16≤
      (numbers maps τ cap M b K H drift scale n U r).reporterWord := by omega
    exact (Int.ofNat_le.mpr (hh.trans HC.reporterWord)).trans hword
  have score (a : ℕ) (ha : a≤n) : ((a*a+a+p^r+16 : ℕ) : ℤ)≤lim.word := by
    have hm := Nat.mul_le_mul ha ha
    have hh : a*a+a+p^r+16≤(numbers maps τ cap M b K H drift scale n U r).reporterWord := by omega
    exact (Int.ofNat_le.mpr (hh.trans HC.reporterWord)).trans hword
  apply TernaryArenaCleanupLayout.inputs μ A B C keysB keysC hw hend
    (hA.trans (by unfold addr; omega)) (hB.trans (by unfold addr; omega))
    (hC.trans (by unfold addr; omega)) (by omega) (by omega) (by omega) hq hL
    hwCleanup (score I.nB hnB) (score I.nC hnC) ?_ ?_ hreadKB hreadKC habsA habsB habsC
    hreadA hreadB hreadC ?_ hsortedB hsortedC (hnB.trans_lt hn) (hnC.trans_lt hn) (by omega)
  · intro i hi
    rw [hkB i hi]
    exact coefficientCode_lt _
  · intro i hi
    rw [hkC i hi]
    exact coefficientCode_lt _
  · exact (Int.ofNat_le.mpr (hW.2.2.trans HC.reporterWord)).trans hword

end ThreeSum.TernaryArenaCleanupAllocation
