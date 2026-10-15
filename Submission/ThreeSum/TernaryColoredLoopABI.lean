import Submission.ThreeSum.TernaryArenaLoopState
import Submission.ThreeSum.LightTernaryColoredSolver

noncomputable section
namespace ThreeSum.TernaryColoredLoopABI
open Light TernaryArenaLayout TernaryArenaLoop LightTernaryColoredSolver TernaryLocalParameters
variable {p m F K N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
set_option maxHeartbeats 1500000

theorem values (S : Setup p m F K N E) (loc μ : ℕ→ℤ) (header : ℕ)
    (h5 : loc 5=(header:ℤ)) (h6 : loc 6=(S.input.free:ℤ))
    (h8 : loc 8=(addr S.input.free S.input.capacity 2:ℤ))
    (h9 : loc 9=(addr S.input.free S.input.capacity 3:ℤ))
    (h10 : loc 10=(addr S.input.free S.input.capacity 1:ℤ))
    (h11 : loc 11=(addr S.input.free S.input.capacity 13:ℤ))
    (hR : μ (header+15)=(S.rounds:ℤ)) (hJ : μ (header+16)=(S.arrays.J:ℤ)) :
    (loopArgs m F p (fixedAlpha m 2) (TernaryArenaSourceSetup.alphaRank m)
      (TernaryCodeSemantics.address S.Q.val) S.wordRadix S.alpha S.beta S.budgetScale).map
        (fun e=>e.val ⟨loc,μ⟩)=S.initArgs := by
  simp only [loopArgs,List.map_cons,List.map_nil,H,M,v,k,Expr.val,Op.eval,h5,h6,h8,h9,h10,h11,
    ←Nat.cast_add,Int.toNat_natCast,hR,hJ,Setup.initArgs,Setup.argv,LightTernaryPrefixLoop.args]
  simp [addr]

def scalar (S : Setup p m F K N E) : ℕ :=
  m+F+p+fixedAlpha m 2+TernaryArenaSourceSetup.alphaRank m+TernaryCodeSemantics.address S.Q.val+
    S.wordRadix+S.alpha+S.beta+S.budgetScale+S.arrays.J+S.rounds

theorem safe {lim : Limits} (S : Setup p m F K N E) (loc μ : ℕ→ℤ) (header : ℕ)
    (h5 : loc 5=(header:ℤ)) (hheader : header+17≤lim.space)
    (hw : (lim.space:ℤ)≤lim.word) (hs : (scalar S:ℤ)≤lim.word) :
    ∀e∈loopArgs m F p (fixedAlpha m 2) (TernaryArenaSourceSetup.alphaRank m)
      (TernaryCodeSemantics.address S.Q.val) S.wordRadix S.alpha S.beta S.budgetScale,
      e.Safe lim ⟨loc,μ⟩ := by
  have hb : ((header+16:ℕ):ℤ)<lim.space := by exact_mod_cast (show header+16<lim.space by omega)
  simp only [scalar,Nat.cast_add] at hs
  intro e he
  simp only [loopArgs,List.mem_cons,List.mem_nil_iff,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [H,M,k,v,Expr.Safe,Expr.val,Op.eval,h5,Limits.Addr]
  all_goals try trivial
  all_goals try omega
  all_goals try simp only [Nat.cast_ofNat,abs_of_nonneg (by positivity : (0:ℤ)≤(header:ℤ)+15),
    abs_of_nonneg (by positivity : (0:ℤ)≤(header:ℤ)+16)]
  all_goals repeat' apply And.intro
  all_goals first | trivial | omega

@[simp] theorem cost (m F p alpha2 alphaRank localQ R a b scale : ℕ) :
    ((loopArgs m F p alpha2 alphaRank localQ R a b scale).map Expr.cost).sum=23 := by rfl

end ThreeSum.TernaryColoredLoopABI
