import Submission.ThreeSum.LightArray

/-!
# Actual cumulative mass guard before expensive reporting

The root header is the actual Initialize output, whose third cell contains
the queried raw mass. This procedure adds that cell to the retained running
counter and returns one exactly when the computed threshold is exceeded.
It changes only the counter cell.
-/

namespace ThreeSum.LightDenseGuard

open Light

def body : Stmt :=
  .set 3 (M (v 0) +' M (v 1 +' k 2)) ;;
  .store (v 0) (v 3) ;;
  .ite (v 2 <' v 3) (.set 0 (k 1)) (.set 0 (k 0))

def time : ℕ := 60

variable {lim : Limits} {P : Program} {μ : ℕ→ℤ}
  {counter root old mass threshold d : ℕ}

theorem meets {p : ℕ} (hp : P[p]?=some body)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hcounter : counter+1 ≤ lim.space) (hroot : root+3 ≤ lim.space)
    (hword : ((old+mass+threshold+2 : ℕ) : ℤ) ≤ lim.word)
    (hread : μ counter=(old : ℤ)) (hmass : μ (root+2)=(mass : ℤ)) :
    Meets lim P p d [counter,root,threshold] μ time
      (fun result ν => result=(if threshold < old+mass then 1 else 0 : ℤ) ∧
        ν counter=((old+mass : ℕ) : ℤ) ∧ SameOutside μ ν counter 1) := by
  have hmassZ : μ (((root : ℤ)+2).toNat)=(mass : ℤ) := by
    rw [show ((root : ℤ)+2).toNat=root+2 by omega]
    exact hmass
  apply Meets.of_body hp
  unfold body time
  light_set (old+mass : ℕ) using hread,hmass,hmassZ
  light_store counter (old+mass : ℕ)
  light_if hyes hno : threshold < old+mass
  · light_set (1 : ℕ)
    exact ⟨by simp [hyes],by simp,by light_keep⟩
  · light_set (0 : ℕ)
    exact ⟨by simp [hno],by simp,by light_keep⟩

def program : Program := [body]

theorem program_meets (hw : (lim.space : ℤ) ≤ lim.word)
    (hcounter : counter+1 ≤ lim.space) (hroot : root+3 ≤ lim.space)
    (hword : ((old+mass+threshold+2 : ℕ) : ℤ) ≤ lim.word)
    (hread : μ counter=(old : ℤ)) (hmass : μ (root+2)=(mass : ℤ)) :
    Meets lim program 0 d [counter,root,threshold] μ time
      (fun result ν => result=(if threshold < old+mass then 1 else 0 : ℤ) ∧
        ν counter=((old+mass : ℕ) : ℤ) ∧ SameOutside μ ν counter 1) :=
  meets rfl hw hcounter hroot hword hread hmass

end ThreeSum.LightDenseGuard
