import Submission.ThreeSum.LightPairSearchMain

namespace ThreeSum.LightPairSearch
open Light
variable {lim : Limits}

def program (predicates : Program) (pPred : ℕ) : Program :=
  predicates++[rowBody pPred,body predicates.length]

/-- The arbitrary predicate library is physically included in the program.
Every call uses its proved execution time and preserves its memory invariant. -/
theorem program_meets (predicates : Program) (pPred : ℕ) {q ctx T d : ℕ}
    (good : ℕ → ℕ → Prop) [DecidableRel good] (I : (ℕ → ℤ) → Prop)
    (hq : 0<q) (μ : ℕ → ℤ) (hI : I μ)
    (hword : ((q*q+q+ctx+20 : ℕ) : ℤ) ≤ lim.word)
    (hd : d+1<lim.depth)
    (hpred : ∀ u<q, ∀ v<q, ∀ ν, I ν → Meets lim predicates pPred (d+2) [u,v,ctx] ν T
      (fun r ξ => r=(if good u v then 1 else 0) ∧ I ξ)) :
    Meets lim (program predicates pPred) (predicates.length+1) d [q,ctx] μ
      (q*q*(T+200)+100)
      (fun r ν => r=(first (goodCode q good) (q*q) : ℤ) ∧ I ν) := by
  have hmain : (program predicates pPred)[predicates.length+1]?=some (body predicates.length) := by
    simp [program,List.getElem?_append_right]
  have hrow : (program predicates pPred)[predicates.length]?=some (rowBody pPred) := by
    simp [program,List.getElem?_append_right]
  have hc := meets hmain hrow good I hq μ hI hword hd
    (fun u hu v hv ν hν => (hpred u hu v hv ν hν).append [rowBody pPred,body predicates.length])
  exact hc.mono_time (time_bound q T hq)

end ThreeSum.LightPairSearch
