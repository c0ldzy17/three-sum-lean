import Submission.ThreeSum.LightArray

/-!
# Append an entire matching residue fiber as original-position pairs

The row performs exactly one iteration per matching right index. It writes
interleaved original left/right positions and preserves every earlier row.
-/

namespace ThreeSum.LightWantedRow

open Light

set_option maxHeartbeats 900000

/-- Left position, right-index array, fiber start/length, output base,
and number of pairs already written. -/
def body : Stmt :=
  .for 6 (v 3) (
    .store (v 4 +' k 2 *' (v 5 +' v 6)) (v 0) ;;
    .store (v 4 +' k 2 *' (v 5 +' v 6) +' k 1) (M (v 1 +' v 2 +' v 6)))

def time (n : ℕ) : ℕ := 120*n+20

def Inv (μ : ℕ → ℤ) (left src start n dst previous j : ℕ) (σ : State) : Prop :=
  ∃ ν : ℕ → ℤ, σ=⟨frame [left,src,start,n,dst,previous,j],ν⟩ ∧
    (∀ t < j, ν (dst+2*(previous+t))=(left : ℤ) ∧
      ν (dst+2*(previous+t)+1)=μ (src+start+t)) ∧
    SameOutside μ ν (dst+2*previous) (2*n)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain left src start n dst previous : ℕ} {μ : ℕ → ℤ}
    (hmain : P[pMain]? = some body)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+start+n ≤ dst) (hspace : dst+2*(previous+n) ≤ lim.space)
    (hleft : (left : ℤ) ≤ lim.word)
    (hvalues : ∀ t < n, |μ (src+start+t)| ≤ lim.word) :
    Meets lim P pMain d [left,src,start,n,dst,previous] μ (time n)
      (fun _ ν => (∀ t < n, ν (dst+2*(previous+t))=(left : ℤ) ∧
        ν (dst+2*(previous+t)+1)=μ (src+start+t)) ∧
        SameOutside μ ν (dst+2*previous) (2*n)) := by
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ left src start n dst previous) n 112 ?start ?round ?done ?bound
  case start =>
    refine ⟨μ,by simp [update_frame_setLocal],?_,SameOutside.refl⟩
    intro t ht
    omega
  case round =>
    rintro j _ hj _ ⟨ν,rfl,written,kept⟩
    have hread : ν (src+start+j)=μ (src+start+j) := kept _ (Or.inl (by omega))
    have hvalue := abs_le.mp (hvalues j hj)
    have hreadAfter : Function.update ν (dst+2*(previous+j)) (left : ℤ) (src+start+j)=
        μ (src+start+j) := by
      rw [Function.update_of_ne (by omega),hread]
    have haddress : ((src : ℤ)+(start : ℤ)+(j : ℤ)).toNat=src+start+j := by omega
    light_store (dst+2*(previous+j)) (left : ℕ)
    light_store (dst+2*(previous+j)+1) (μ (src+start+j) : ℤ) using haddress,hreadAfter
    refine ⟨by simp,
      Function.update (Function.update ν (dst+2*(previous+j)) (left : ℤ))
        (dst+2*(previous+j)+1) (μ (src+start+j)),
      by simp [update_frame_setLocal],?_,?_⟩
    · intro t ht
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
      · constructor
        · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
          exact (written t ht).1
        · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
          exact (written t ht).2
      · constructor
        · rw [Function.update_of_ne (by omega),Function.update_self]
        · rw [Function.update_self]
    · intro a ha
      rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
      exact kept a ha
  case done =>
    rintro _ _ ⟨ν,rfl,written,kept⟩
    exact ⟨written,kept⟩
  case bound =>
    rintro j _ hj _ ⟨ν,rfl,_,_⟩
    simp

def program : Program := [body]

end ThreeSum.LightWantedRow
