import Submission.ThreeSum.BandEnumeration

/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition

def size (n g : ℕ) : ℕ := if n = 0 then 0 else (n-1)/g+1
def start (g i : ℕ) : ℕ := i*g
def stop (n g i : ℕ) : ℕ := min n ((i+1)*g)

theorem size_le (n g : ℕ) : size n g ≤ n := by
  unfold size
  split_ifs with h
  · omega
  · have hdiv := Nat.div_le_self (n-1) g
    omega

theorem size_mono {n m g : ℕ} (h : n ≤ m) : size n g ≤ size m g := by
  by_cases hn : n = 0
  · simp [size,hn]
  · have hm : m ≠ 0 := by omega
    have hd := Nat.div_le_div_right (c := g) (show n-1 ≤ m-1 by omega)
    simp only [size,if_neg hn,if_neg hm]
    omega

/-- A finite ceiling bound, including the empty input. -/
theorem size_mul_le (n g : ℕ) : size n g*g ≤ n+g := by
  by_cases hn : n = 0
  · simp [size,hn]
  · have hd := Nat.div_mul_le_self (n-1) g
    simp only [size,if_neg hn,Nat.add_mul,Nat.one_mul]
    omega

theorem start_lt {n g i : ℕ} (hg : 0 < g) (hi : i < size n g) : start g i < n := by
  unfold size at hi
  split_ifs at hi with hn
  · omega
  · have hid : i ≤ (n-1)/g := by omega
    have hm := (Nat.le_div_iff_mul_le hg).mp hid
    unfold start
    omega

theorem start_lt_stop {n g i : ℕ} (hg : 0 < g) (hi : i < size n g) :
    start g i < stop n g i := by
  have hn := start_lt hg hi
  unfold start stop at *
  have hprod : i*g < (i+1)*g := Nat.mul_lt_mul_of_pos_right (by omega) hg
  omega

theorem stop_le (n g i : ℕ) : stop n g i ≤ n := min_le_left _ _

theorem stop_sub_one_lt {n g i : ℕ} (hg : 0 < g) (hi : i < size n g) :
    stop n g i-1 < n := by
  have hp := start_lt_stop hg hi
  have hs := stop_le n g i
  omega

theorem length_le (n g i : ℕ) : stop n g i-start g i ≤ g := by
  have hle : stop n g i ≤ (i+1)*g := min_le_right _ _
  unfold start
  simp only [Nat.add_mul,Nat.one_mul] at hle
  omega

theorem index_lt_size {n g i : ℕ} (hi : i < n) : i/g < size n g := by
  have hn : n ≠ 0 := by omega
  have hh := Nat.div_le_div_right (c := g) (show i ≤ n-1 by omega)
  simp only [size,if_neg hn]
  omega

theorem index_bounds {n g i : ℕ} (hg : 0 < g) (hi : i < n) :
    start g (i/g) ≤ i ∧ i < stop n g (i/g) := by
  have hlo := Nat.div_mul_le_self i g
  have hmod := Nat.mod_lt i hg
  have hsum := Nat.mod_add_div i g
  unfold start stop
  constructor
  · exact hlo
  · have hh : i < (i/g+1)*g := by nlinarith
    omega

theorem monotone_of_strict {f : ℕ → ℤ} {n i j : ℕ}
    (hs : ∀ i j, i < j → j < n → f i < f j) (hij : i ≤ j) (hj : j < n) :
    f i ≤ f j := by
  rcases lt_or_eq_of_le hij with h | rfl
  · exact (hs i j h hj).le
  · rfl

def family (f : ℕ → ℤ) (n g : ℕ) (hg : 0 < g)
    (hs : ∀ i j, i < j → j < n → f i < f j) : BandEnumeration.Family where
  size := size n g
  lower i := f (start g i)
  upper i := f (stop n g i-1)
  nonempty i hi := monotone_of_strict hs (by have := start_lt_stop hg hi; omega)
    (stop_sub_one_lt hg hi)
  sorted i j hij hj := monotone_of_strict hs (Nat.mul_le_mul_right g hij) (start_lt hg hj)
  separated i j hij hj := by
    have hstop : stop n g i ≤ (i+1)*g := min_le_right _ _
    have hprod : (i+1)*g ≤ j*g := Nat.mul_le_mul_right g (by omega)
    have hpositive : 0 < j*g := by
      have hjpos : 0 < j := by omega
      exact Nat.mul_pos hjpos hg
    apply hs _ _ (by unfold start; omega) (start_lt hg hj)

theorem covers (f : ℕ → ℤ) (n g : ℕ) (hg : 0 < g)
    (hs : ∀ i j, i < j → j < n → f i < f j) {i : ℕ} (hi : i < n) :
    let A := family f n g hg hs
    A.lower (i/g) ≤ f i ∧ f i ≤ A.upper (i/g) := by
  have hb := index_bounds hg hi
  have hib := index_lt_size (g := g) hi
  exact ⟨monotone_of_strict hs hb.1 hi,
    monotone_of_strict hs (by omega) (stop_sub_one_lt hg hib)⟩

end ThreeSum.BandPartition
