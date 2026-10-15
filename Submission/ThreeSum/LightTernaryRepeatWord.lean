import Submission.ThreeSum.LightNatPower

namespace ThreeSum.LightTernaryRepeatWord
open Light
set_option maxHeartbeats 2000000

def value (q b : ℕ) : ℕ→ ℕ
  | 0=>0
  | i+1=>value q b i*b+q

def body : Stmt :=
  .set 3 (k 0) ;;
  .for 4 (v 2) (.set 3 (v 3 *' v 1 +' v 0)) ;;
  .set 0 (v 3)

def time (s : ℕ) : ℕ := 30*s+30

theorem meets {lim : Limits} {P : Program} {d p q b s : ℕ}
    (hp : P[p]?=some body) (μ : ℕ→ ℤ)
    (hq : (q:ℤ)≤ lim.word) (hb : (b:ℤ)≤ lim.word) (hs : (s:ℤ)≤ lim.word)
    (hfit : ∀ i≤ s, (value q b i:ℤ)≤ lim.word) :
    Meets lim P p d [q,b,s] μ (time s) (fun r ν=>r=(value q b s:ℤ) ∧ ν=μ) := by
  have h0 : (0:ℤ)≤ lim.word := by omega
  apply Meets.of_body hp
  unfold body time
  light_set (0:ℕ)
  refine Ends.pieceThen (Ends.for (T:= 25*s+10)
    (Q:= fun σ=>σ=⟨frame [q,b,s,(value q b s:ℕ),s],μ⟩)
    (fun i σ=>σ=⟨frame [q,b,s,(value q b i:ℕ),i],μ⟩) s 7
    ?start ?round ?done ?bound) ?after (hT:= by light_time)
  case start =>simp [update_frame_setLocal,value]
  case round =>
    rintro i σ hi hc rfl
    have hnext:= hfit (i+1) (by omega)
    have he : (value q b (i+1):ℤ)=(value q b i:ℤ)*(b:ℤ)+(q:ℤ) :=by simp [value]
    have hprod : (value q b i:ℤ)*(b:ℤ)≤lim.word :=by omega
    have hprod0 : (0:ℤ)≤ (value q b i:ℤ)*(b:ℤ) := by positivity
    refine Ends.setLast ?_ (hs:= by light_side [value]) (hT:= by light_time)
    simp [update_frame_setLocal,value]
  case done =>intro σ _ hI; exact hI
  case bound =>rintro i σ hi hc rfl; light_side
  case after =>
    rintro σ rfl
    have hv:= hfit s le_rfl
    light_set (value q b s:ℕ)
    exact ⟨rfl,rfl⟩

end ThreeSum.LightTernaryRepeatWord
