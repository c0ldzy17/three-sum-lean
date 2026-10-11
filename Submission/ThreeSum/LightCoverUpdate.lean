import Submission.ThreeSum.LightArray

/-! # Removing the targets covered by the selected candidate -/

namespace ThreeSum.LightCoverUpdate

open Light

def body : Stmt :=
  pass 3 (v 2) (v 1)
    (M (v 1 +' v 3) *' (k 1 -' M (v 0 +' v 3)))

def time (n : ℕ) : ℕ := 26*n+6

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {p : ℕ} (hp : P[p]? = some body)
    {μ : ℕ → ℤ} {row activePtr n : ℕ} (cover active : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hrow : row+n ≤ lim.space) (hactive : activePtr+n ≤ lim.space)
    (hsep : Apart row n activePtr n)
    (hread : ∀ j < n, μ (row+j) = (cover j : ℤ))
    (hreadActive : ∀ j < n, μ (activePtr+j) = (active j : ℤ))
    (hcover : ∀ j < n, cover j ≤ 1) (hact : ∀ j < n, active j ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim P p d [row,activePtr,n] μ (time n)
      (fun _ μ' => (∀ j < n, μ' (activePtr+j) = ((active j*(1-cover j) : ℕ) : ℤ)) ∧
        SameOutside μ μ' activePtr n) := by
  have he (j : ℕ) (hj : j < n) :
      ((active j*(1-cover j) : ℕ) : ℤ) = (active j : ℤ)*(1-(cover j : ℤ)) := by
    rw [Nat.cast_mul,Nat.cast_sub (hcover j hj)]
    norm_num
  refine Meets.of_body hp (Ends.pass
    (fun j => (active j : ℤ)*(1-(cover j : ℤ))) (fun j hj => ?_)
    ⟨fun j hj => (wrote_done (μ := μ) (dst := activePtr)
      (f := fun j => (active j : ℤ)*(1-(cover j : ℤ))) hj).trans (he j hj).symm,by light_keep⟩ hw hactive rfl rfl
    (hT := by light_time [time]))
  have hr : wrote μ activePtr (fun j => (active j : ℤ)*(1-(cover j : ℤ))) j (row+j) = μ (row+j) :=
    wrote_rest (by omega)
  have ha : wrote μ activePtr (fun j => (active j : ℤ)*(1-(cover j : ℤ))) j (activePtr+j) = μ (activePtr+j) :=
    wrote_rest (by omega)
  have hrc := hread j hj
  have hac := hreadActive j hj
  have hc := hcover j hj
  have hav := hact j hj
  have hcZ : (0 : ℤ) ≤ 1-(cover j : ℤ) ∧ 1-(cover j : ℤ) ≤ 1 := by omega
  have hpZ : (0 : ℤ) ≤ (active j : ℤ)*(1-(cover j : ℤ)) ∧
      (active j : ℤ)*(1-(cover j : ℤ)) ≤ 1 := by
    constructor
    · exact mul_nonneg (Int.natCast_nonneg _) hcZ.1
    · exact (mul_le_mul (by exact_mod_cast hav : (active j : ℤ) ≤ 1) hcZ.2 hcZ.1 (by norm_num)).trans (by norm_num)
  light_side [hr,ha,hrc,hac]

def program : Program := [body]

theorem program_meets
    {μ : ℕ → ℤ} {row activePtr n : ℕ} (cover active : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hrow : row+n ≤ lim.space) (hactive : activePtr+n ≤ lim.space)
    (hsep : Apart row n activePtr n)
    (hread : ∀ j < n, μ (row+j) = (cover j : ℤ))
    (hreadActive : ∀ j < n, μ (activePtr+j) = (active j : ℤ))
    (hcover : ∀ j < n, cover j ≤ 1) (hact : ∀ j < n, active j ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim program 0 d [row,activePtr,n] μ (time n)
      (fun _ μ' => (∀ j < n, μ' (activePtr+j) = ((active j*(1-cover j) : ℕ) : ℤ)) ∧
        SameOutside μ μ' activePtr n) :=
  meets rfl cover active hw hrow hactive hsep hread hreadActive hcover hact hword

end ThreeSum.LightCoverUpdate
