import Submission.ThreeSum.ReportingHostPrefixOrder
import Submission.ThreeSum.BinarySearch
import Submission.ThreeSum.LightReportingPrefixCatalog

/-!
# Exact sorted lookup of a prefix catalog record

Each original catalog position is retained as the low digit of a packed
integer. A sorted search uses the upper end of the requested key's interval;
the unique prefix-key proof forces that hit to be the original record, and
remainder recovers its unchanged catalog index.
-/

namespace ThreeSum.ReportingHostPackedCatalog

open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPrefixOrder

set_option maxHeartbeats 600000

def pairKey (radix left right : ℕ) : ℕ := left+radix*right

def packed (key : ℕ → ℕ) (n i : ℕ) : ℕ := key i*(n+1)+i

def codes (key : ℕ → ℕ) (n : ℕ) : List ℤ := List.ofFn fun i : Fin n => (packed key n i.val : ℤ)

theorem codes_length (key : ℕ → ℕ) (n : ℕ) : (codes key n).length=n := by simp [codes]

theorem pairKey_lt {radix left right : ℕ} (hl : left < radix) (hr : right < radix) :
    pairKey radix left right < radix^2 := by unfold pairKey; nlinarith

theorem pairKey_injective {radix l r l' r' : ℕ} (hl : l < radix) (hl' : l' < radix)
    (he : pairKey radix l r = pairKey radix l' r') : l=l' ∧ r=r' := by
  have hm := congrArg (fun x => x%radix) he
  have hlr : l=l' := by simpa [pairKey,Nat.add_mod,Nat.mod_eq_of_lt hl,Nat.mod_eq_of_lt hl'] using hm
  refine ⟨hlr,?_⟩
  unfold pairKey at he
  rw [hlr] at he
  nlinarith

theorem packed_lt {key : ℕ → ℕ} {n i U : ℕ} (hi : i < n) (hk : key i < U) :
    packed key n i < U*(n+1) := by unfold packed; nlinarith

theorem packed_mod {key : ℕ → ℕ} {n i : ℕ} (hi : i < n) : packed key n i%(n+1)=i := by
  simp [packed,Nat.add_mod,Nat.mod_eq_of_lt (show i < n+1 by omega)]

theorem packed_emod {key : ℕ → ℕ} {n i : ℕ} (hi : i < n) :
    ((packed key n i : ℕ) : ℤ)%((n+1 : ℕ) : ℤ) = (i : ℤ) := by
  exact_mod_cast packed_mod (key := key) hi

theorem packed_interval_unique {key : ℕ → ℕ} {n i j : ℕ}
    (hi : i < n) (hj : j < n)
    (hunique : ∀ a < n, ∀ b < n, key a=key b → a=b)
    (hlo : packed key n i ≤ packed key n j)
    (hhi : packed key n j ≤ key i*(n+1)+n) : i=j := by
  have hle : key i ≤ key j := by
    by_contra hh
    have hh' : key j+1 ≤ key i := by omega
    unfold packed at hlo
    nlinarith
  have hge : key j ≤ key i := by
    by_contra hh
    have hh' : key i+1 ≤ key j := by omega
    unfold packed at hhi
    nlinarith
  exact hunique i hi j hj (Nat.le_antisymm hle hge)

theorem sorted_getD_le {S : List ℤ} (hs : S.Pairwise (· ≤ ·)) :
    ∀ i j, i ≤ j → j < S.length → S.getD i 0 ≤ S.getD j 0 := by
  intro i j hij hj
  by_cases he : i=j
  · subst j; exact le_rfl
  · rw [List.getD_eq_getElem _ _ (by omega),List.getD_eq_getElem _ _ hj]
    exact List.pairwise_iff_getElem.mp hs i j (by omega) hj (by omega)

theorem upperBound_hit {key : ℕ → ℕ} {n i : ℕ} {S : List ℤ}
    (hi : i < n) (hunique : ∀ a < n, ∀ b < n, key a=key b → a=b)
    (hperm : S.Perm (codes key n)) (hs : S.Pairwise (· ≤ ·)) :
    let K := BinarySearch.upperBound (fun j => S.getD j 0) n ((key i*(n+1)+n : ℕ) : ℤ)
    0 < K ∧ K ≤ n ∧ S.getD (K-1) 0 = (packed key n i : ℤ) := by
  dsimp only
  have hlen : S.length=n := hperm.length_eq.trans (codes_length key n)
  have hsorted : ∀ a b, a ≤ b → b < n → S.getD a 0 ≤ S.getD b 0 := by
    simpa only [hlen] using sorted_getD_le hs
  have hpart := BinarySearch.upperBound_correct (fun j => S.getD j 0) n
    ((key i*(n+1)+n : ℕ) : ℤ) hsorted
  rcases hpart with ⟨hKn,hbelow,habove⟩
  have htarget : (packed key n i : ℤ) ∈ S := by
    apply hperm.mem_iff.mpr
    exact List.mem_ofFn.mpr ⟨⟨i,hi⟩,rfl⟩
  obtain ⟨j,hj,hjRead⟩ := List.mem_iff_getElem.mp htarget
  have hjn : j < n := by omega
  have hjRead' : S.getD j 0 = (packed key n i : ℤ) := by
    simpa only [List.getD_eq_getElem _ _ hj] using hjRead
  have htargetUpper : (packed key n i : ℤ) ≤ ((key i*(n+1)+n : ℕ) : ℤ) := by
    exact_mod_cast (show packed key n i ≤ key i*(n+1)+n by unfold packed; omega)
  have hjK : j < BinarySearch.upperBound (fun j => S.getD j 0) n ((key i*(n+1)+n : ℕ) : ℤ) := by
    by_contra hh
    have hx := habove j (by omega) hjn
    dsimp only at hx
    rw [hjRead'] at hx
    omega
  refine ⟨by omega,hKn,?_⟩
  have hlast : BinarySearch.upperBound (fun j => S.getD j 0) n ((key i*(n+1)+n : ℕ) : ℤ)-1 < n := by omega
  have hlast' : BinarySearch.upperBound (fun j => S.getD j 0) n ((key i*(n+1)+n : ℕ) : ℤ)-1 < S.length := by omega
  have hmem : S.getD (BinarySearch.upperBound (fun j => S.getD j 0) n
      ((key i*(n+1)+n : ℕ) : ℤ)-1) 0 ∈ S := by
    rw [List.getD_eq_getElem _ _ hlast']
    exact List.getElem_mem _
  obtain ⟨b,hb⟩ := List.mem_ofFn.mp (hperm.mem_iff.mp hmem)
  have hlo := hsorted j _ (by omega) hlast
  rw [hjRead',← hb] at hlo
  have hhi := hbelow _ (by omega : BinarySearch.upperBound (fun j => S.getD j 0) n
    ((key i*(n+1)+n : ℕ) : ℤ)-1 <
      BinarySearch.upperBound (fun j => S.getD j 0) n ((key i*(n+1)+n : ℕ) : ℤ))
  dsimp only at hhi
  rw [← hb] at hhi
  have he : i=b.val := packed_interval_unique hi b.isLt hunique (by exact_mod_cast hlo) (by exact_mod_cast hhi)
  exact hb.symm.trans (by rw [he])

def prefixKey (h J k i : ℕ) : ℕ :=
  pairKey (2^(J*(512*h))) (subsetMask (preL h J k i)) (subsetMask (preR h J k i))

theorem prefixKey_lt (h J k i : ℕ) : prefixKey h J k i < 2^(2*(J*(512*h))) := by
  have hh := pairKey_lt (subsetMask_isMask (preL h J k i)).1 (subsetMask_isMask (preR h J k i)).1
  simpa only [prefixKey,← pow_mul,Nat.mul_comm] using hh

theorem prefixKey_unique {h J k : ℕ} (hk : k ≤ J) :
    ∀ i < LightReportingPrefixCatalog.count h k,
    ∀ j < LightReportingPrefixCatalog.count h k,
      prefixKey h J k i=prefixKey h J k j → i=j := by
  intro i hi j hj he
  have hp := pairKey_injective (subsetMask_isMask (preL h J k i)).1
    (subsetMask_isMask (preL h J k j)).1 he
  exact maskPair_unique hk (by rwa [← LightReportingPrefixCatalog.count_eq_length])
    (by rwa [← LightReportingPrefixCatalog.count_eq_length]) hp.1 hp.2

theorem prefix_count_le_pow {h J k : ℕ} (hk : k ≤ J) :
    LightReportingPrefixCatalog.count h k ≤ 2^(2*(J*(512*h))) := by
  have hhalf : 2*h ≤ 512*h := by omega
  have he : LightReportingPrefixArrays.localCount (512*h) h ≤ 2^(2*(512*h)) := by
    calc
      _ ≤ 2^(512*h)*2^(2*h) := Nat.mul_le_mul (Nat.choose_le_two_pow _ _) (Nat.choose_le_two_pow _ _)
      _ ≤ 2^(512*h)*2^(512*h) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hhalf)
      _ = 2^(2*(512*h)) := by rw [← pow_add]; congr 1; omega
  calc
    _ ≤ (2^(2*(512*h)))^k := Nat.pow_le_pow_left he k
    _ = 2^(2*(k*(512*h))) := by rw [← pow_mul]; congr 1; ring
    _ ≤ 2^(2*(J*(512*h))) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hk))

end ThreeSum.ReportingHostPackedCatalog
