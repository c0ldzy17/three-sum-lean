import Submission.ThreeSum.Radix
import Submission.ThreeSum.RadixKeyLists
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

namespace ThreeSum.TernaryWantedRadix
open Finset

/-- The list indices are physical local output records, including equal keys. -/
def localBucket (p : ℤ) (raws : List ℤ) (x : ℤ) : List ℕ :=
  (List.range raws.length).filter fun i => p ∣ x-raws.getD i 0

@[simp] theorem mem_localBucket (p : ℤ) (raws : List ℤ) (x : ℤ) (i : ℕ) :
    i ∈ localBucket p raws x ↔ i < raws.length ∧ p ∣ x-raws.getD i 0 := by
  simp [localBucket]

theorem localBucket_nodup (p : ℤ) (raws : List ℤ) (x : ℤ) : (localBucket p raws x).Nodup :=
  (List.nodup_range).filter _

/-- Only the local residue fiber is visited; each chosen key fixes its carry. -/
def wantedOutputs (p : ℤ) (raws : List ℤ) : ℕ → ℤ → List (List ℕ)
  | 0, _ => [[]]
  | j+1, x => (localBucket p raws x).flatMap fun i =>
      (wantedOutputs p raws j ((x-raws.getD i 0)/p)).map (List.cons i)

theorem mem_wantedOutputs (p : ℤ) (hp : p ≠ 0) (raws : List ℤ) :
    ∀ j x is, is ∈ wantedOutputs p raws j x ↔
      is.length=j ∧ (∀ i ∈ is, i < raws.length) ∧
      p^j ∣ x-Radix.positionalHash p (fun i => raws.getD i 0) is := by
  intro j
  induction j with
  | zero => intro x is; cases is <;> simp [wantedOutputs,Radix.positionalHash]
  | succ j ih =>
    intro x is
    cases is with
    | nil => simp [wantedOutputs]
    | cons i is =>
      simp only [wantedOutputs,List.mem_flatMap,List.mem_map,List.cons.injEq]
      have he : (∃ a ∈ localBucket p raws x, ∃ ys ∈ wantedOutputs p raws j ((x-raws.getD a 0)/p),
          a=i ∧ ys=is) ↔
          i ∈ localBucket p raws x ∧ is ∈ wantedOutputs p raws j ((x-raws.getD i 0)/p) := by
        aesop
      rw [he,mem_localBucket,ih]
      simp only [List.length_cons,Nat.add_right_cancel_iff,List.mem_cons,forall_eq_or_imp,
        Radix.positionalHash,Radix.radix_divisibility p _ _ _ hp]
      tauto

theorem wantedOutputs_nodup (p : ℤ) (raws : List ℤ) : ∀ j x, (wantedOutputs p raws j x).Nodup := by
  intro j
  induction j with
  | zero => intro x; simp [wantedOutputs]
  | succ j ih =>
    intro x
    apply List.nodup_flatMap.mpr
    constructor
    · intro i hi
      exact (ih _).map (fun _ _ h => (List.cons.inj h).2)
    · exact (localBucket_nodup p raws x).imp (fun {a b} hab ys ha hb => by
        obtain ⟨tail,_,rfl⟩ := List.mem_map.mp ha
        obtain ⟨other,_,h⟩ := List.mem_map.mp hb
        exact hab (List.cons.inj h).1.symm)

private theorem flatMap_length_le {A B : Type*} (xs : List A) (f : A → List B) (n : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ n) : (xs.flatMap f).length ≤ xs.length*n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    nlinarith

theorem wantedOutputs_length_le (p : ℤ) (raws : List ℤ) (C : ℕ)
    (hcap : ∀ x, (localBucket p raws x).length ≤ C) :
    ∀ j x, (wantedOutputs p raws j x).length ≤ C^j := by
  intro j
  induction j with
  | zero => intro x; simp [wantedOutputs]
  | succ j ih =>
    intro x
    calc
      _ ≤ (localBucket p raws x).length*C^j :=
        flatMap_length_le _ _ _ (fun i _ => by simpa using ih ((x-raws.getD i 0)/p))
      _ ≤ C*C^j := Nat.mul_le_mul_right _ (hcap x)
      _ = _ := (pow_succ' _ _).symm

def encode (N code scale : ℕ) : List ℕ → ℕ
  | [] => code
  | i::is => encode N (code+scale*i) (scale*N) is

def wantedCodes (p : ℤ) (raws : List ℤ) (j : ℕ) (x : ℤ) (code scale : ℕ) : List ℕ :=
  (wantedOutputs p raws j x).map (encode raws.length code scale)

theorem wantedCodes_succ (p : ℤ) (raws : List ℤ) (j : ℕ) (x : ℤ) (code scale : ℕ) :
    wantedCodes p raws (j+1) x code scale = (localBucket p raws x).flatMap fun i =>
      wantedCodes p raws j ((x-raws.getD i 0)/p) (code+scale*i) (scale*raws.length) := by
  simp [wantedCodes,wantedOutputs,List.map_flatMap,List.map_map,Function.comp_def,encode]

/-- The complete DFS node count, including branches that later die. -/
def visits (p : ℤ) (raws : List ℤ) : ℕ → ℤ → ℕ
  | 0, _ => 1
  | j+1, x => 1+((localBucket p raws x).map fun i => visits p raws j ((x-raws.getD i 0)/p)).sum

theorem visits_le (p : ℤ) (raws : List ℤ) (C : ℕ) (hC : 1 ≤ C)
    (hcap : ∀ x, (localBucket p raws x).length ≤ C) :
    ∀ j x, visits p raws j x ≤ (j+1)*C^j := by
  intro j
  induction j with
  | zero => intro x; simp [visits]
  | succ j ih =>
    intro x
    have hs : ((localBucket p raws x).map fun i => visits p raws j ((x-raws.getD i 0)/p)).sum ≤
        (localBucket p raws x).length*((j+1)*C^j) := by
      induction localBucket p raws x with
      | nil => simp
      | cons i is ih' =>
        simp only [List.map_cons,List.sum_cons,List.length_cons]
        have h := ih ((x-raws.getD i 0)/p)
        nlinarith
    have hb := Nat.mul_le_mul_right ((j+1)*C^j) (hcap x)
    have hp := one_le_pow₀ hC (n := j+1)
    simp only [visits]
    rw [pow_succ'] at hp ⊢
    nlinarith

theorem child_target_bound (p V : ℕ) (hp : 2 ≤ p) {x a : ℤ}
    (hx : |x| ≤ (V : ℤ)) (ha : |a| ≤ (V : ℤ)) (hdiv : (p : ℤ) ∣ x-a) :
    |(x-a)/(p : ℤ)| ≤ (V : ℤ) := by
  have he := Int.mul_ediv_cancel' hdiv
  have hh : |x-a| ≤ 2*(V : ℤ) := by
    have h : |x-a| ≤ |x|+|a| := by simpa using abs_sub_le x 0 a
    linarith
  have hpz : (2 : ℤ) ≤ p := by exact_mod_cast hp
  have hpn : (0 : ℤ) ≤ p := by positivity
  have he' : |x-a| = (p : ℤ)*|(x-a)/(p : ℤ)| := by nth_rewrite 1 [← he]; rw [abs_mul,abs_of_nonneg hpn]
  nlinarith [abs_nonneg ((x-a)/(p : ℤ))]


def codeLimit (N code scale j : ℕ) : ℕ := (code+scale)*(2*N)^j

theorem codeLimit_base {N code scale j : ℕ} (hN : 1 ≤ N) :
    code+scale ≤ codeLimit N code scale j := by
  unfold codeLimit
  exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))

theorem codeLimit_child {N code scale j i : ℕ} (hN : 1 ≤ N) (hi : i < N) :
    codeLimit N (code+scale*i) (scale*N) j ≤ codeLimit N code scale (j+1) := by
  unfold codeLimit
  rw [pow_succ']
  have h : code+scale*i+scale*N ≤ (code+scale)*(2*N) := by nlinarith
  simpa [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul_right ((2*N)^j) h

theorem wantedCodes_length (p : ℤ) (raws : List ℤ) (j : ℕ) (x : ℤ) (code scale : ℕ) :
    (wantedCodes p raws j x code scale).length = (wantedOutputs p raws j x).length := by
  simp [wantedCodes]

theorem wantedCodes_bound (p : ℤ) (raws : List ℤ) (hN : 1 ≤ raws.length) :
    ∀ j x code scale z, z ∈ wantedCodes p raws j x code scale →
      z ≤ codeLimit raws.length code scale j := by
  intro j
  induction j with
  | zero =>
    intro x code scale z hz
    have he : z = code := by simpa [wantedCodes,wantedOutputs,encode] using hz
    subst z
    simp [codeLimit]
  | succ j ih =>
    intro x code scale z hz
    rw [wantedCodes_succ] at hz
    obtain ⟨i,hi,hz⟩ := List.mem_flatMap.mp hz
    exact (ih _ _ _ _ hz).trans (codeLimit_child hN (mem_localBucket _ _ _ _ |>.mp hi).1)

theorem localBucket_eq_of_emod {p : ℤ} (raws : List ℤ) {x y : ℤ} (h : x%p = y%p) :
    localBucket p raws x = localBucket p raws y := by
  unfold localBucket
  congr 1
  funext i
  apply decide_eq_decide.mpr
  simp only [Int.dvd_iff_emod_eq_zero,Int.sub_emod,Int.emod_emod,h]

end ThreeSum.TernaryWantedRadix
