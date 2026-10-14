import Submission.ThreeSum.TernaryEnumeration

/-!
# Sorted canonical two-bit addresses for the compressed ternary bank

Each trit is encoded as `00`, `01`, or `11`.  The address width is twice the
number of trits, but only valid bank words are enumerated.  This permits the
existing verified bit routines to manipulate the addresses without scanning
the ambient Boolean cube.
-/

namespace ThreeSum.TernaryAddresses

open ThreeSum.TernaryEnumeration

def digitCode (d : ℕ) : ℕ := if d = 2 then 3 else d

def code : List ℕ → ℕ
  | [] => 0
  | d :: xs => digitCode d * 4 ^ xs.length + code xs

def codes : ℕ → ℕ → List ℕ
  | 0, _ => [0]
  | n + 1, t => (digits t).flatMap fun d =>
      (codes n (t - d)).map (fun a => digitCode d * 4 ^ n + a)

theorem digitCode_le {d : ℕ} (hd : d < 3) : digitCode d ≤ 3 := by
  unfold digitCode
  split <;> omega

theorem digitCode_strict {d e : ℕ} (hd : d < 3) (he : e < 3) (hde : d < e) :
    digitCode d < digitCode e := by
  interval_cases d <;> interval_cases e <;> norm_num [digitCode] at *

theorem code_lt (xs : List ℕ) (h : ∀ d ∈ xs, d < 3) : code xs < 4 ^ xs.length := by
  induction xs with
  | nil => simp [code]
  | cons d xs ih =>
    have hd := digitCode_le (h d (by simp))
    have hx := ih (fun e he => h e (by simp [he]))
    have hp : 0 < 4 ^ xs.length := by positivity
    simp only [code, List.length_cons, pow_succ]
    nlinarith

theorem codes_eq_map (n t : ℕ) : codes n t = (words n t).map code := by
  induction n generalizing t with
  | zero => simp [codes, words, code]
  | succ n ih =>
    simp only [codes, words, List.map_flatMap]
    congr 1
    funext d
    rw [ih]
    simp only [List.map_map]
    apply List.map_congr_left
    intro xs hx
    have hlen := ((mem_words n (t - d) xs).mp hx).1
    simp [code, hlen]

@[simp] theorem codes_length (n t : ℕ) : (codes n t).length = (words n t).length := by
  simp [codes_eq_map]

theorem mem_codes_lt {n t a : ℕ} (ha : a ∈ codes n t) : a < 4 ^ n := by
  rw [codes_eq_map] at ha
  obtain ⟨xs, hx, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hlen, hall, _⟩ := (mem_words n t xs).mp hx
  simpa [hlen] using code_lt xs hall

theorem codes_strictly_sorted (n t : ℕ) : (codes n t).Pairwise (· < ·) := by
  induction n generalizing t with
  | zero => simp [codes]
  | succ n ih =>
    rw [codes, List.pairwise_flatMap]
    constructor
    · intro d hd
      rw [List.pairwise_map]
      exact (ih (t - d)).imp (fun h => Nat.add_lt_add_left h _)
    · have hdigits : (digits t).Pairwise (· < ·) :=
        List.pairwise_lt_range.filter _
      apply hdigits.imp_of_mem
      intro d e hd he hde a ha b hb
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
      have hd3 := (mem_digits.mp hd).1
      have he3 := (mem_digits.mp he).1
      have hdc := digitCode_strict hd3 he3 hde
      have hx4 := mem_codes_lt hx
      have hp : 0 < 4 ^ n := by positivity
      nlinarith

theorem codes_nodup (n t : ℕ) : (codes n t).Nodup :=
  (codes_strictly_sorted n t).imp (fun h => Nat.ne_of_lt h)

theorem visits_le_codes (n t : ℕ) : visits n t ≤ (n + 1) * (codes n t).length := by
  simpa only [codes_length] using visits_le n t

end ThreeSum.TernaryAddresses
