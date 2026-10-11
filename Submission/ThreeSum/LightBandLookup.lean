import Submission.ThreeSum.BinarySearch
import Submission.ThreeSum.LightSubsetAddress

/-!
# Division-free binary interval lookup in actual machine syntax

The search descends a constructed powers-of-two table and extends a known
prefix by one power at a time. Every tested endpoint is an explicit bounded
memory load. Neither natural-number division nor a function-valued memory
oracle is a machine operation. `search_meets` identifies its returned prefix
with any valid sorted partition, and hence with `BinarySearch.upperBound`.
-/

namespace ThreeSum.LightBandLookup

open Light ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

/-- Arguments: lower-endpoint base, length, query, powers base, remaining
width, accepted prefix. Locals 6 and 7 hold the next bit and candidate. -/
def searchBody (pSelf : ℕ) : Stmt :=
  .ite (k 0 <' v 4)
    (.set 6 (v 4 -' k 1) ;;
      .set 7 (v 5 +' M (v 3 +' v 6)) ;;
      .ite (v 7 ≤' v 1)
        (.ite (v 2 <' M (v 0 +' v 7 -' k 1))
          (.call pSelf [v 0,v 1,v 2,v 3,v 6,v 5] 0)
          (.call pSelf [v 0,v 1,v 2,v 3,v 6,v 7] 0))
        (.call pSelf [v 0,v 1,v 2,v 3,v 6,v 5] 0))
    (.set 0 (v 5))

def searchTime (L : ℕ) : ℕ := 120*L+30

theorem search_meets {pSearch a n powers W : ℕ} {x : ℤ}
    (hprog : P[pSearch]? = some (searchBody pSearch))
    (μ : ℕ → ℤ) (f : ℕ → ℤ) (K : ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n ≤ lim.space) (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((n+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (a+i) = f i)
    (hpowers : Powers μ powers W)
    (hpart : BinarySearch.Partition f x n K) :
    ∀ L k : ℕ, L ≤ W → k ≤ K → K < k+2^L →
      ∀ d, d+L ≤ lim.depth →
      Meets lim P pSearch d [a,n,x,powers,L,k] μ (searchTime L)
        (fun r μ' => r = (K : ℤ) ∧ μ' = μ) := by
  obtain ⟨hKn,hpre,hpost⟩ := hpart
  have hnWord : (n : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (by omega : n ≤ lim.space)).trans hw
  intro L
  induction L with
  | zero =>
      intro k hL hk hgap d hd
      have heq : k = K := by simp only [Nat.pow_zero] at hgap; omega
      apply Meets.of_body hprog
      unfold searchBody searchTime
      refine Ends.iteLast (fun h => False.elim (by simp at h)) (fun _ => ?_)
      light_set (k : ℕ)
      exact ⟨by simp [heq],rfl⟩
  | succ L ih =>
      intro k hL hk hgap d hd
      have hLW : L ≤ W := by omega
      have hpower := hpowers L hLW
      have hpPos : 0 < (2 : ℕ)^L := Nat.two_pow_pos _
      have hpLe : 2^L ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) (by omega)
      have hmidWord : ((k+2^L : ℕ) : ℤ) ≤ lim.word := by
        exact (Int.ofNat_le.mpr (by omega : k+2^L ≤ n+2^(W+1)+16)).trans hword
      have hmidCast : (k : ℤ)+μ (powers+L) = ((k+2^L : ℕ) : ℤ) := by
        rw [hpower]
        push_cast
        rfl
      have hpowerNonneg : (0 : ℤ) ≤ μ (powers+L) := by
        rw [hpower]
        exact Int.natCast_nonneg _
      have hpowerWord : μ (powers+L) ≤ lim.word := by
        rw [hpower]
        exact (Int.ofNat_le.mpr (by omega : 2^L ≤ n+2^(W+1)+16)).trans hword
      have hmidNonneg : (0 : ℤ) ≤ (k : ℤ)+μ (powers+L) := by omega
      have hmidBound : (k : ℤ)+μ (powers+L) ≤ lim.word := by
        rw [hmidCast]
        exact hmidWord
      have hpowerIntNonneg : (0 : ℤ) ≤ (2 : ℤ)^L := by positivity
      have hmidIntBound : (k : ℤ)+(2 : ℤ)^L ≤ lim.word := by exact_mod_cast hmidWord
      have hdouble : 2^(L+1) = 2^L+2^L := by ring
      rw [hdouble] at hgap
      apply Meets.of_body hprog
      unfold searchBody searchTime
      refine Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simp at h))
      light_set (L : ℕ) using searchTime
      light_set (k+2^L : ℕ) using hmidCast,searchTime
      light_if hmnZ hmnZ : ((k+2^L : ℕ) : ℤ) ≤ (n : ℤ) using searchTime
      · have hmn : k+2^L ≤ n := by exact_mod_cast hmnZ
        have hmRead := hread (k+2^L-1) (by omega)
        have hmAddr : (a : ℤ)+((k+2^L : ℕ) : ℤ)-1 =
            ((a+(k+2^L-1) : ℕ) : ℤ) := by omega
        have hmNat : ((a : ℤ)+((k+2^L : ℕ) : ℤ)-1).toNat =
            a+(k+2^L-1) := by rw [hmAddr,Int.toNat_natCast]
        have hmNat' : ((a : ℤ)+((k : ℤ)+(2 : ℤ)^L)-1).toNat =
            a+(k+2^L-1) := by simpa only [Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat] using hmNat
        have hmIntBound : (a : ℤ)+((k : ℤ)+(2 : ℤ)^L) ≤ lim.word := by
          have hn : a+(k+2^L) ≤ lim.space := by omega
          exact (by exact_mod_cast hn : (a : ℤ)+((k : ℤ)+(2 : ℤ)^L) ≤ (lim.space : ℤ)).trans hw
        have hmIntLower : 1 ≤ (a : ℤ)+((k : ℤ)+(2 : ℤ)^L) := by
          have hp : 0 < (2 : ℤ)^L := by positivity
          omega
        have hmIntSpace : (a : ℤ)+((k : ℤ)+(2 : ℤ)^L) ≤ (lim.space : ℤ) := by
          exact_mod_cast (show a+(k+2^L) ≤ lim.space by omega)
        light_if htest htest : x < f (k+2^L-1) using hmNat',hmRead,searchTime
        · have hkm : K < k+2^L := by
            by_contra h
            have hh := hpre (k+2^L-1) (by omega)
            omega
          light_call (ih k hLW hk hkm (d+1) (by omega))
            using searchTime with r μ' ⟨hr,hmem⟩
          exact ⟨hr,hmem⟩
        · have hmk : k+2^L ≤ K := by
            by_contra h
            exact htest (hpost (k+2^L-1) (by omega) (by omega))
          light_call (ih (k+2^L) hLW hmk (by omega) (d+1) (by omega))
            using searchTime with r μ' ⟨hr,hmem⟩
          exact ⟨hr,hmem⟩
      · have hkm : K < k+2^L := by omega
        light_call (ih k hLW hk hkm (d+1) (by omega))
          using searchTime with r μ' ⟨hr,hmem⟩
        exact ⟨hr,hmem⟩

/-- `0` represents a miss; `i+1` represents interval number `i`. -/
def result (lo hi : ℕ → ℤ) (n : ℕ) (x : ℤ) : ℕ :=
  ((BinarySearch.locate lo hi n x).map Nat.succ).getD 0

theorem result_le (lo hi : ℕ → ℤ) (n : ℕ) (x : ℤ)
    (hsorted : ∀ i j, i ≤ j → j < n → lo i ≤ lo j) : result lo hi n x ≤ n := by
  unfold result
  cases h : BinarySearch.locate lo hi n x with
  | none => simp
  | some i =>
      have hh := BinarySearch.locate_sound lo hi n x hsorted h
      simp only [Option.map_some,Option.getD_some]
      omega

/-- Arguments: lower base, upper base, size, query, powers base, width. -/
def body (pSearch : ℕ) : Stmt :=
  .call pSearch [v 0,v 2,v 3,v 4,v 5,k 0] 6 ;;
  .ite (k 0 <' v 6)
    (.ite (M (v 1 +' v 6 -' k 1) <' v 3)
      (.set 0 (k 0)) (.set 0 (v 6)))
    (.set 0 (k 0))

def time (L : ℕ) : ℕ := searchTime L+100

theorem meets {pMain pSearch a b n powers W L d : ℕ} {x : ℤ}
    (hmain : P[pMain]? = some (body pSearch))
    (hsearch : P[pSearch]? = some (searchBody pSearch))
    (μ : ℕ → ℤ) (lo hi : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n ≤ lim.space) (hb : b+n ≤ lim.space)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((n+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hreadLo : ∀ i < n, μ (a+i) = lo i)
    (hreadHi : ∀ i < n, μ (b+i) = hi i)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i j, i ≤ j → j < n → lo i ≤ lo j)
    (hL : L ≤ W) (hn : n < 2^L) (hd : d+L+1 ≤ lim.depth) :
    Meets lim P pMain d [a,b,n,x,powers,L] μ (time L)
      (fun r μ' => r = (result lo hi n x : ℤ) ∧ μ' = μ) := by
  have hpart := BinarySearch.upperBound_correct lo n x hsorted
  have hkn := hpart.1
  have hcall := search_meets hsearch μ lo (BinarySearch.upperBound lo n x)
    hw ha hspace hword hreadLo hpowers hpart L 0 hL (by omega) (by omega)
    (d+1) (by omega)
  apply Meets.of_body hmain
  unfold body time
  light_call hcall using searchTime with count μ' ⟨hcount,hmem⟩
  subst μ'
  subst count
  light_if hkZ hkZ : (0 : ℤ) < (BinarySearch.upperBound lo n x : ℤ) using searchTime
  · have hk : 0 < BinarySearch.upperBound lo n x := by exact_mod_cast hkZ
    have hread := hreadHi (BinarySearch.upperBound lo n x-1) (by omega)
    have haddr : (b : ℤ)+(BinarySearch.upperBound lo n x : ℤ)-1 =
        ((b+(BinarySearch.upperBound lo n x-1) : ℕ) : ℤ) := by omega
    have hnat : ((b : ℤ)+(BinarySearch.upperBound lo n x : ℤ)-1).toNat =
        b+(BinarySearch.upperBound lo n x-1) := by rw [haddr,Int.toNat_natCast]
    light_if hh hh : hi (BinarySearch.upperBound lo n x-1) < x using hnat,hread,searchTime
    · light_set (0 : ℕ) using searchTime
      exact ⟨by simp [result,BinarySearch.locate,hk,not_le.mpr hh],rfl⟩
    · light_set (BinarySearch.upperBound lo n x : ℕ) using searchTime
      refine ⟨?_,rfl⟩
      simp [result,BinarySearch.locate,hk,le_of_not_gt hh]
  · have hk : ¬0 < BinarySearch.upperBound lo n x := by exact_mod_cast hkZ
    light_set (0 : ℕ) using searchTime
    exact ⟨by simp [result,BinarySearch.locate,hk],rfl⟩

def program : Program := [body 1,searchBody 1]

theorem program_meets {a b n powers W L d : ℕ} {x : ℤ}
    (μ : ℕ → ℤ) (lo hi : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n ≤ lim.space) (hb : b+n ≤ lim.space)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((n+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hreadLo : ∀ i < n, μ (a+i) = lo i)
    (hreadHi : ∀ i < n, μ (b+i) = hi i)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i j, i ≤ j → j < n → lo i ≤ lo j)
    (hL : L ≤ W) (hn : n < 2^L) (hd : d+L+1 ≤ lim.depth) :
    Meets lim program 0 d [a,b,n,x,powers,L] μ (time L)
      (fun r μ' => r = (result lo hi n x : ℤ) ∧ μ' = μ) :=
  meets rfl rfl μ lo hi hw ha hb hspace hword hreadLo hreadHi hpowers hsorted hL hn hd

end ThreeSum.LightBandLookup
