import Submission.ThreeSum.LightArray
import Submission.ThreeSum.Balancing

/-!
# A finite array minimum scan in the benchmark language

The selected index is a deterministic left-to-right minimum. Its value
can therefore instantiate the exact mean bound for offset balancing.
-/

namespace ThreeSum.LightMinimum

open Light

def least (f : ℕ → ℤ) : ℕ → ℕ
  | 0 => 0
  | n+1 => if f n < f (least f n) then n else least f n

theorem least_lt (f : ℕ → ℤ) {n : ℕ} (hn : 0 < n) : least f n < n := by
  induction n with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero => simp [least]
      | succ n =>
          have h := ih (by omega)
          unfold least
          split <;> omega

theorem least_lt_of_le (f : ℕ → ℤ) {j n : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    least f j < n := by
  by_cases h : j = 0
  · simp [h, least, hn]
  · exact (least_lt f (by omega)).trans_le hj

theorem least_value_le (f : ℕ → ℤ) (n i : ℕ) (hi : i < n) :
    f (least f n) ≤ f i := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases h : f n < f (least f n)
      · rw [least, if_pos h]
        by_cases hin : i < n
        · exact h.le.trans (ih hin)
        · have he : i = n := by omega
          simp [he]
      · rw [least, if_neg h]
        by_cases hin : i < n
        · exact ih hin
        · have he : i = n := by omega
          simpa only [he] using le_of_not_gt h

def scanBody : Stmt :=
  .ite (M (v 0 +' v 3) <' M (v 0 +' v 2)) (.set 2 (v 3)) .skip

def body : Stmt :=
  .set 2 (k 0) ;;
  .for 3 (v 1) scanBody ;;
  .set 0 (v 2)

def time (n : ℕ) : ℕ := 32*n + 20

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {p : ℕ} (hp : P[p]? = some body)
    {μ : ℕ → ℤ} {src n : ℕ} (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : 0 < n)
    (hsrc : src+n ≤ lim.space)
    (hread : ∀ i < n, μ (src+i) = f i) :
    Meets lim P p d [src, n] μ (time n)
      fun r μ' => r = (least f n : ℤ) ∧ μ' = μ := by
  apply Meets.of_body hp
  unfold body time
  light_set 0
  refine Ends.pieceThen (Ends.for (T := 28*n+6)
    (Q := fun σ => σ = ⟨frame [(src : ℤ), n, least f n, n], μ⟩)
    (fun j σ => σ = ⟨frame [(src : ℤ), n, least f j, j], μ⟩) n 20
    ?_ ?_ ?_ ?_ (hT := by light_time)) ?_
  · simp [least, update_frame_setLocal]
  · rintro j _ hj _ rfl
    have hbest : least f j < n := least_lt_of_le f hn (by omega)
    have hjread := hread j hj
    have hbread := hread (least f j) hbest
    unfold scanBody
    refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by light_side)
    · have hcmp : f j < f (least f j) := by simpa [hjread, hbread] using hc
      refine Ends.setLast ?_ (hs := by light_side) (hT := by light_time)
      simp [least, hcmp, update_frame_setLocal]
    · have hcmp : ¬ f j < f (least f j) := by simpa [hjread, hbread] using hc
      apply Ends.skip
      simp [least, hcmp, update_frame_setLocal]
  · intro σ hcounter hshape
    exact hshape
  · rintro j _ hj _ rfl
    light_side
  · intro σ hshape
    rw [hshape]
    light_set (least f n)
    exact ⟨rfl, rfl⟩

end ThreeSum.LightMinimum
