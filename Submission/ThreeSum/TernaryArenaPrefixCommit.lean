import Submission.ThreeSum.LightTernaryPrefixFinish
import Submission.ThreeSum.TernaryArenaSeedCandidate

noncomputable section
namespace ThreeSum.TernaryArenaPrefixCommit
open Light TernaryArenaLayout TernaryArenaSourceSetup TernaryArenaSeedCandidate
open LightTernarySeedScoreFactory LightTernaryControllerFactory LightTernaryPrefixFinish

/-- Fixed slots discharge every actual key/span commit separation. -/
theorem layout (p r rows : ℕ) (I : Input) (A : Inputs) {lim : Limits}
    (h48 : 48≤I.capacity) (hB : I.nB≤I.capacity) (hC : I.nC≤I.capacity)
    (hO : I.requesterCount≤I.capacity) (hSpan : rows*A.J≤I.capacity)
    (hspace : finish I.free I.capacity≤lim.space) :
    Layout (config p r I A 0) lim (addr I.free I.capacity 3) rows (addr I.free I.capacity 8) :=by
  constructor
  · exact before (by decide : 3<4) h48
  · exact before (by decide : 4<5) hB
  · exact before (by decide : 5<6) hC
  · exact before (by decide : 6<16) hO
  · exact before (by decide : 6<17) hO
  · exact before (by decide : 6<18) hO
  · exact region_space (by decide : 16<slots) hB hspace
  · exact region_space (by decide : 17<slots) hC hspace
  · exact region_space (by decide : 18<slots) hO hspace
  · exact before (by decide : 6<7) hO
  · exact before (by decide : 7<8) hSpan
  · exact region_space (by decide : 8<slots) hSpan hspace

/-- The retained keys are the exact append results of the selected replay. -/
theorem keys {C : Config} {D : Data C} {R S rows newSpan : ℕ}
    {raws : List ℤ} {words maps : List ℕ} {ξ ν : ℕ→ℤ}
    (H : Committed C rows newSpan ξ ν)
    (O : LightTernarySeedScoreFull.Outputs C D R S raws words maps ξ) :
    Reads ν C.Bold C.nB D.newB ∧ Reads ν C.Cold C.nC D.newC ∧ Reads ν C.Oold C.nO D.newO :=by
  refine ⟨?_,?_,?_⟩
  · intro i hi; exact (H.2.1 i hi).trans (O.B i hi)
  · intro i hi; exact (H.2.2.1 i hi).trans (O.Cvalues i hi)
  · intro i hi; exact (H.2.2.2.1 i hi).trans (O.O i hi)

/-- Committing only the retained key/span regions leaves actual banks,
headers, menus and original digit matrices unchanged. -/
theorem outside {C : Config} {rows newSpan : ℕ} {ξ ν : ℕ→ℤ}
    (H : Committed C rows newSpan ξ ν) (x : ℕ)
    (hk : x<C.Bold ∨ C.Oold+C.nO≤x) (hs : x<C.catalog ∨ C.catalog+rows*C.J≤x) :
    ν x=ξ x :=H.2.2.2.2.2 x hk hs

end ThreeSum.TernaryArenaPrefixCommit
