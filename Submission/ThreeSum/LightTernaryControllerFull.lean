import Submission.ThreeSum.LightTernarySeedScoreFull
import Submission.ThreeSum.LightTernaryControllerFactory

noncomputable section
namespace ThreeSum.LightTernaryControllerFactory
open Light LightTernarySeedScoreFactory
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

structure Candidate.FullGuard {C : Config} [Fact C.p.Prime] (D : Candidate C) (lim : Limits)
    (depth K R S : ℕ) (raws : List ℤ) (words maps : List ℕ) (μ : ℕ→ℤ) : Prop where
  toGuard : D.Guard lim depth K R S raws words maps μ
  retain : C.wanted+(D.data.wantedRows R S raws words maps).length≤C.tensor
  locations : ∀x∈[C.flags+C.seed,C.scoreB+C.seed,C.scoreC+C.seed,C.scorePaired+C.seed],
    x<C.Bnew ∧ x≠C.header+104

def Candidate.FullDone {C : Config} [Fact C.p.Prime] (D : Candidate C)
    (K R S : ℕ) (raws : List ℤ) (words maps : List ℕ) (μ ν : ℕ→ℤ) : Prop :=
  D.Done K μ ν ∧ LightTernarySeedScoreFull.Outputs C D.data R S raws words maps ν

/-- Strong candidate execution retains every actual next-prefix key and
literal wanted record, including the real dynamic header count. -/
theorem Candidate.run_full {C : Config} [Fact C.p.Prime] {D : Candidate C} {lim : Limits}
    {depth K R S : ℕ} {raws : List ℤ} {words maps : List ℕ} {μ : ℕ→ℤ}
    (G : D.FullGuard lim depth K R S raws words maps μ) :
    Meets lim (LightTernarySeedScore.program C.p R S K raws words maps
      D.host.left.xs D.host.left.ys D.host.left.zs D.host.right.xs D.host.right.ys D.host.right.zs)
      164 depth C.argv μ (D.runtime K R S raws words maps)
      (fun r ν=>r=D.data.flag ∧ D.FullDone K R S raws words maps μ ν) := by
  have hh := G.toGuard.1.run_full G.retain D.leftHom D.rightHom D.queryRank
    (fun i : Fin D.host.front.count => TernaryNativePairMoments.Pair D.host i.val)
    (fun i => TernaryNativeTensorScore.originalLeft D.host C.J D.L i.val)
    (fun i => TernaryNativeTensorScore.originalRight D.host C.J D.Rvalues i.val) ((2 : ℤ)^D.twos)
    (by
      intro i a b c e
      rw [TernaryNativeTensorScore.score_eq_original_tensor,
        TernaryConvolution.factorial_eq_power_two,D.queryTwos i.val i.isLt])
    (by simpa only [Candidate.score,TernaryNativeTensorScore.pairedPotential,Nat.cast_sum] using G.toGuard.2)
  have hf := G.locations (C.flags+C.seed) (by simp)
  have hb := G.locations (C.scoreB+C.seed) (by simp)
  have hc := G.locations (C.scoreC+C.seed) (by simp)
  have hp := G.locations (C.scorePaired+C.seed) (by simp)
  have hh' : Meets lim (LightTernarySeedScore.program C.p R S K raws words maps
      D.host.left.xs D.host.left.ys D.host.left.zs D.host.right.xs D.host.right.ys D.host.right.zs)
      164 depth C.argv μ (D.runtime K R S raws words maps)
      (fun r ν=>r=D.data.flag ∧ ∃ξ,
        (KeptInput C μ ξ ∧ LightTernarySeedScoreFull.Outputs C D.data R S raws words maps ξ) ∧
        ν=Function.update (Function.update (Function.update (Function.update ξ
          (C.flags+C.seed) D.data.flag) (C.scoreB+C.seed) D.data.collisionB)
          (C.scoreC+C.seed) D.data.collisionC) (C.scorePaired+C.seed) (D.score K)) := by
    simpa only [Candidate.runtime,Candidate.score,TernaryNativeTensorScore.pairedPotential,Nat.cast_sum] using hh
  apply hh'.mono le_rfl
  rintro ret ν ⟨hr,ξ,⟨hkeep,ho⟩,hν⟩
  refine ⟨hr,⟨ξ,hkeep,hν⟩,?_⟩
  have same (x : ℕ) (hx : C.Bnew≤x) : ν x=ξ x := by
    rw [hν]
    simp only [Function.update_of_ne (show x≠C.scorePaired+C.seed by omega),
      Function.update_of_ne (show x≠C.scoreC+C.seed by omega),
      Function.update_of_ne (show x≠C.scoreB+C.seed by omega),
      Function.update_of_ne (show x≠C.flags+C.seed by omega)]
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i hi
    rw [same _ (by omega)]
    exact ho.B i hi
  · intro i hi
    rw [same _ (by have := G.toGuard.1.append.BC; omega)]
    exact ho.Cvalues i hi
  · intro i hi
    rw [same _ (by have := G.toGuard.1.append.BC; have := G.toGuard.1.append.CO; omega)]
    exact ho.O i hi
  · intro i hi
    rw [same _ (by have := G.toGuard.1.append.BC; have := G.toGuard.1.append.CO; have := G.toGuard.1.wanted.targetEnd; omega)]
    exact ho.wanted i hi
  · rw [hν]
    simpa only [Function.update_of_ne hp.2.symm,Function.update_of_ne hc.2.symm,
      Function.update_of_ne hb.2.symm,Function.update_of_ne hf.2.symm] using ho.count

end ThreeSum.LightTernaryControllerFactory
