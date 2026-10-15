import Submission.ThreeSum.LightTernaryFrozenQueryPrepare
import Submission.ThreeSum.TernaryFrozenQueryCost

namespace ThreeSum.LightTernaryFrozenQuery
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryFrozenQueryCost
set_option maxHeartbeats 3000000

def queryTime {N : ℕ} (L T K : ℕ) (R : TritWord N) : ℕ :=
  10000*(N+L+1)*work T (coords N K) R

@[simp] theorem queryTime_zero {N : ℕ} (L T : ℕ) (R : TritWord N) :
    queryTime L T 0 R=10000*(N+L+1) := by simp [queryTime,work]

theorem work_bank {N : ℕ} (T : ℕ) (is : List (Fin N)) (R : TritWord N)
    (h : rank R≤T) : work T is R=1 := by cases is <;> simp [work,h]

theorem queryTime_bank {N : ℕ} (L T K : ℕ) (R : TritWord N) (h : rank R≤T) :
    queryTime L T K R=10000*(N+L+1) := by simp [queryTime,work_bank T _ R h]

theorem queryTime_lookup {N : ℕ} (L T K : ℕ) (R : TritWord N) :
    LightTernaryQueryLookup.time L+100≤queryTime L T K R := by
  have hw : 1≤work T (coords N K) R := by
    cases h : coords N K with
    | nil => simp [work]
    | cons i rest => simp only [work]; split_ifs <;> omega
  have hl := LightTernaryQueryLookup.time_bound L
  unfold queryTime
  nlinarith

theorem queryTime_step {N K : ℕ} (L T : ℕ) (R : TritWord N) (hK : K<N)
    (hbank : T<rank R) :
    let i : Fin N :=⟨K,hK⟩
    let t := fun d : Fin 3 => if d≤R i then queryTime L T K (Function.update R i d) else 0
    prepTime N+(t 0+t 1+t 2+200)≤queryTime L T (K+1) R := by
  dsimp only
  have hsum :
      (if (0 : Fin 3)≤R ⟨K,hK⟩ then queryTime L T K (Function.update R ⟨K,hK⟩ 0) else 0)+
      (if (1 : Fin 3)≤R ⟨K,hK⟩ then queryTime L T K (Function.update R ⟨K,hK⟩ 1) else 0)+
      (if (2 : Fin 3)≤R ⟨K,hK⟩ then queryTime L T K (Function.update R ⟨K,hK⟩ 2) else 0) =
      10000*(N+L+1)*(∑ d : Fin 3, if d≤R ⟨K,hK⟩ then
        work T (coords N K) (Function.update R ⟨K,hK⟩ d) else 0) := by
    simp [queryTime,Fin.sum_univ_succ,mul_ite,Nat.mul_add,Nat.add_assoc]
  rw [hsum,queryTime,coords_succ hK,work,if_neg (by omega : ¬rank R≤T)]
  unfold prepTime LightTernaryCodes.digitTime LightTernaryCodes.zeroTime LightMaskErase.time
  simp only [Nat.mul_add,Nat.mul_one]
  omega

theorem queryTime_near_card {N : ℕ} (L T K : ℕ) (hK : K≤N) (R : TritWord N) :
    queryTime L T K R≤10000*(N+L+1)*(K+1)*
      (nearWords (capWord (coords N K) R) (rank R+1-T)).card := by
  have hw := work_le_capWord_card T (coords N K) (coords_nodup N K) R
  have h := Nat.mul_le_mul_left (10000*(N+L+1)) hw
  simpa [queryTime,coords_length hK,Nat.mul_assoc] using h

theorem digitCount_wordList {N : ℕ} (R : TritWord N) (d : Fin 3) :
    digitCount R d=((TernaryBankEnumeration.wordList R).map
      (fun a : ℕ => if a=d.val then 1 else 0)).sum := by
  simp [TernaryBankEnumeration.wordList,List.map_ofFn,List.sum_ofFn,digitCount,Fin.ext_iff]

theorem full_capWord_list {N : ℕ} (R : TritWord N) :
    TernaryBankEnumeration.wordList (capWord (coords N N) R)=
      (TernaryBankEnumeration.wordList R).reverse := by
  have ht : (List.finRange N).take N=List.finRange N := List.take_of_length_le (by simp)
  rw [wordList_capWord]
  simp [caps,coords,ht,TernaryBankEnumeration.wordList,List.ofFn_eq_map]

theorem full_capWord_digitCount {N : ℕ} (R : TritWord N) (d : Fin 3) :
    digitCount (capWord (coords N N) R) d=digitCount R d := by
  rw [digitCount_wordList,full_capWord_list]
  simp [List.map_reverse,←digitCount_wordList]

theorem queryTime_gibbs {N : ℕ} (L T : ℕ) (R : TritWord N)
    (z : ℝ) (hz : 0≤z) (hz1 : z≤1) :
    (queryTime L T N R : ℝ)*z^(rank R+1-T)≤
      10000*(N+L+1)*(N+1)*(1+z)^digitCount R 1*(1+z+z^2)^digitCount R 2 := by
  have hg := work_gibbs_counts T (coords N N) (coords_nodup N N) R z hz hz1
  have hm := mul_le_mul_of_nonneg_left hg
    (by positivity : (0 : ℝ)≤10000*(N+L+1))
  simpa [queryTime,Nat.cast_mul,Nat.cast_add,coords_length (le_refl N),
    full_capWord_digitCount,mul_assoc] using hm

end ThreeSum.LightTernaryFrozenQuery
