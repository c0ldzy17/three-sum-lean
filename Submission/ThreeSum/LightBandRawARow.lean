import Submission.ThreeSum.BandRawA
import Submission.ThreeSumApsp.Lang.Lib.Copy

/-!
# One actual A-band incidence row

Values are copied from the retained sorted A segment. Parallel arrays
receive the physical owner slot and the sorted-array coordinate.
-/

namespace ThreeSum.LightBandRawARow

open Light

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000

/-- Source, value output, owner output, position output, length, owner, start. -/
def body (pCopy pFill : ℕ) : Stmt :=
  .call pCopy [v 0,v 1,v 4] 7 ;;
  .call pFill [v 2,v 4,v 5] 7 ;;
  pass 8 (v 4) (v 3) (v 6 +' v 8)

def time (n : ℕ) : ℕ := copyTime n+fillTime n+30*n+100

def KeptOthers (μ ν : ℕ → ℤ) (values owners positions n : ℕ) : Prop :=
  SameOn (fun a => Outside values n a ∧ Outside owners n a ∧ Outside positions n a) μ ν

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {src values owners positions n owner start : ℕ}

theorem meets {pMain pCopy pFill : ℕ}
    (hmain : P[pMain]?=some (body pCopy pFill))
    (hcopy : P[pCopy]?=some copyBody) (hfill : P[pFill]?=some fillBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hsrc : src+n ≤ values) (hvalues : values+n ≤ owners)
    (howners : owners+n ≤ positions) (hspace : positions+n ≤ lim.space)
    (hstart : start+n ≤ lim.space) :
    Meets lim P pMain d [src,values,owners,positions,n,owner,start] μ (time n)
      (fun _ ν =>
        (∀ j < n, ν (values+j)=μ (src+j) ∧
          ν (owners+j)=(owner : ℤ) ∧ ν (positions+j)=((start+j : ℕ) : ℤ)) ∧
        KeptOthers μ ν values owners positions n) := by
  apply Meets.of_body hmain
  unfold body time
  light_call (copy_meets (d := d+1) (μ := μ) (src := src) (dst := values) (n := n)
    hcopy hw (by omega) (by omega) (Or.inl hsrc))
    with unused ν₁ ⟨hcopied,hkeepCopy⟩
  light_call (fill_meets (d := d+1) (μ := ν₁) (dst := owners) (n := n) (x := (owner : ℤ))
    hfill hw (by omega)) with unused ν₂ ⟨hfilled,hkeepFill⟩
  refine Ends.pass (fun j => ((start+j : ℕ) : ℤ)) (fun j hj => ?_)
    ?_ hw hspace rfl rfl (hT := by light_time [copyTime,fillTime])
  · light_side
  · dsimp only
    constructor
    · intro j hj
      constructor
      · rw [wrote_rest (by omega),hkeepFill _ (Or.inl (by omega))]
        exact hcopied j hj
      · constructor
        · rw [wrote_rest (by omega)]
          exact (hfilled j (by simpa using hj)).trans (List.getElem_replicate ..)
        · exact wrote_done hj
    · intro a ha
      rw [wrote_rest ha.2.2,hkeepFill a ha.2.1,hkeepCopy a ha.1]

def program : Program := [body 1 2,copyBody,fillBody]

end ThreeSum.LightBandRawARow
