import Submission.ThreeSum.TernaryResidueScore

/-!
# Deterministic prime selection using the measured represented FALSE score

The selected score is computed by residue-filtered trinary queries.  Each
step retains its representation-cap loss.  The chain length is arbitrary,
including a fixed large program constant; no random prime is sampled.
-/

namespace ThreeSum.TernaryResidueChain

open Finset
open scoped BigOperators

/-- Concrete finite minimum search of the backend's natural score. -/
def selectPrime (candidates : List ℕ) (encodedScore : ℕ → ℕ) (q : ℕ) : ℕ :=
  (candidates.argmin fun p => encodedScore (q*p)).getD 0

theorem selectPrime_mem (candidates : List ℕ) (hne : candidates ≠ [])
    (encodedScore : ℕ → ℕ) (q : ℕ) :
    selectPrime candidates encodedScore q ∈ candidates := by
  unfold selectPrime
  cases h : candidates.argmin (fun p => encodedScore (q*p)) with
  | none => exact False.elim (hne (List.argmin_eq_none.mp h))
  | some p =>
    simp only [Option.getD_some]
    exact List.argmin_mem (f := fun p => encodedScore (q*p))
      (by simpa only [Option.mem_def] using h)

theorem selectPrime_min (candidates : List ℕ) (encodedScore : ℕ → ℕ) (q : ℕ)
    {p : ℕ} (hp : p ∈ candidates) :
    encodedScore (q*selectPrime candidates encodedScore q) ≤ encodedScore (q*p) := by
  unfold selectPrime
  cases h : candidates.argmin (fun p => encodedScore (q*p)) with
  | none => have := List.argmin_eq_none.mp h; simp_all
  | some p =>
    simp only [Option.getD_some]
    exact List.le_of_mem_argmin (f := fun p => encodedScore (q*p)) hp
      (by simpa only [Option.mem_def] using h)

theorem selected_step_bound (candidates : List ℕ) (encodedScore : ℕ → ℕ)
    (C : Finset ℕ) (hC : C.Nonempty) (hall : ∀ p ∈ C, p ∈ candidates)
    (q K : ℕ)
    (havg : (∑ p ∈ C, encodedScore (q*p)) ≤ K*encodedScore q) :
    C.card * encodedScore (q*selectPrime candidates encodedScore q) ≤ K*encodedScore q := by
  obtain ⟨p,hp,hmin⟩ := C.exists_min_image (fun p => encodedScore (q*p)) hC
  have hsum : C.card*encodedScore (q*p) ≤ ∑ p ∈ C, encodedScore (q*p) := by
    simpa [nsmul_eq_mul] using
      (C.card_nsmul_le_sum (fun p => encodedScore (q*p)) _ hmin)
  have hcontract : C.card*encodedScore (q*p) ≤ K*encodedScore q :=
    hsum.trans havg
  exact (Nat.mul_le_mul_left _ (selectPrime_min candidates encodedScore q (hall p hp))).trans hcontract

def modulus (candidates : List ℕ) (encodedScore : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | r+1 =>
    let q := modulus candidates encodedScore r
    q*selectPrime candidates encodedScore q

theorem modulus_bounds (candidates : List ℕ) (hne : candidates ≠ [])
    (encodedScore : ℕ → ℕ) (y Y r : ℕ)
    (hlo : ∀ p ∈ candidates, y ≤ p) (hhi : ∀ p ∈ candidates, p ≤ Y) :
    y^r ≤ modulus candidates encodedScore r ∧ modulus candidates encodedScore r ≤ Y^r := by
  induction r with
  | zero => simp [modulus]
  | succ r ih =>
    have hmem := selectPrime_mem candidates hne encodedScore (modulus candidates encodedScore r)
    constructor
    · simpa [modulus,pow_succ] using Nat.mul_le_mul ih.1 (hlo _ hmem)
    · simpa [modulus,pow_succ] using Nat.mul_le_mul ih.2 (hhi _ hmem)

/-- The averaging premise is needed only at the actual bounded prefixes.
This permits the finite local-cover cap to be scoped to the actual radix
range, rather than assumed for arbitrary larger scalar moduli. -/
theorem modulus_score_bound (candidates : List ℕ) (encodedScore : ℕ → ℕ)
    (C : Finset ℕ) (hC : C.Nonempty) (hall : ∀ p ∈ C, p ∈ candidates)
    (K D r : ℕ)
    (havg : ∀ j < D,
      (∑ p ∈ C, encodedScore (modulus candidates encodedScore j*p)) ≤
        K*encodedScore (modulus candidates encodedScore j))
    (hr : r ≤ D) :
    C.card^r * encodedScore (modulus candidates encodedScore r) ≤
      K^r * encodedScore 1 := by
  revert hr
  induction r with
  | zero => intro _; simp [modulus]
  | succ r ih =>
    intro hr
    let q := modulus candidates encodedScore r
    have hstep := selected_step_bound candidates encodedScore C hC hall q K
      (havg r (by omega))
    have hprev := ih (by omega)
    calc
      _ = C.card^r * (C.card * encodedScore (q*selectPrime candidates encodedScore q)) := by
        simp only [modulus,q]; ring
      _ ≤ C.card^r * (K*encodedScore q) := Nat.mul_le_mul_left _ hstep
      _ = K * (C.card^r * encodedScore q) := by ring
      _ ≤ K * (K^r * encodedScore 1) := Nat.mul_le_mul_left _ hprev
      _ = _ := by ring

/-- Specialization keeps the measured representation cap S raised to the
chain depth D.  This is the exact finite loss used by the fixed-depth ledger. -/
theorem represented_chain_bound {ι : Type*} (T : Finset ι) (difference : ι → ℤ)
    (L : Finset ℤ) (repr : ℕ → ι → ℕ) (candidates : List ℕ) (C : Finset ℕ)
    (hC : C.Nonempty) (hall : ∀ p ∈ C, p ∈ candidates) (S K D : ℕ)
    (havg : ∀ j < D,
      (∑ p ∈ C, TernaryResidueScore.score T difference L repr
        (modulus candidates (TernaryResidueScore.score T difference L repr) j*p)) ≤
      (S*K)*TernaryResidueScore.score T difference L repr
        (modulus candidates (TernaryResidueScore.score T difference L repr) j)) :
    C.card^D * TernaryResidueScore.score T difference L repr
      (modulus candidates (TernaryResidueScore.score T difference L repr) D) ≤
      S^D*K^D*TernaryResidueScore.score T difference L repr 1 := by
  have hh := modulus_score_bound candidates (TernaryResidueScore.score T difference L repr)
    C hC hall (S*K) D D havg le_rfl
  simpa only [mul_pow,mul_assoc] using hh

end ThreeSum.TernaryResidueChain
