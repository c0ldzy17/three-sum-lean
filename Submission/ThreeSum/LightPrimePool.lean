import Submission.ThreeSum.LightPrimality
import Submission.ThreeSum.PrimeDensity
import Submission.ThreeSum.WeightedScore
import Mathlib.NumberTheory.Bertrand

/-!
# Executing the candidate prime pool

This fixed program scans the integers in `(y,4*y]`, invokes the concrete
trial-division procedure, and writes every prime exactly once in increasing
order. The returned length and written array are the exact candidate pool
used by the contraction and auxiliary-weight theorems.
-/

namespace ThreeSum.LightPrimePool

open Light

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def scanned (y : ℕ) : ℕ → List ℕ
  | 0 => []
  | i+1 =>
    if Nat.Prime (y+i+1) then scanned y i ++ [y+i+1] else scanned y i

theorem prefix_length_le (y i : ℕ) : (scanned y i).length ≤ i := by
  induction i with
  | zero => simp [scanned]
  | succ i ih =>
      unfold scanned
      split
      · simp only [List.length_append,List.length_singleton]
        omega
      · omega

theorem mem_prefix {y i p : ℕ} :
    p ∈ scanned y i ↔ Nat.Prime p ∧ y < p ∧ p ≤ y+i := by
  induction i with
  | zero => simp only [scanned,List.not_mem_nil,false_iff]; omega
  | succ i ih =>
      by_cases hp : Nat.Prime (y+i+1)
      · simp only [scanned,if_pos hp,List.mem_append,List.mem_singleton,ih]
        constructor
        · rintro (⟨hpr,hlo,hhi⟩ | rfl)
          · exact ⟨hpr,hlo,by omega⟩
          · exact ⟨hp,by omega,by omega⟩
        · rintro ⟨hpr,hlo,hhi⟩
          by_cases heq : p = y+i+1
          · exact Or.inr heq
          · exact Or.inl ⟨hpr,hlo,by omega⟩
      · simp only [scanned,if_neg hp,ih]
        constructor
        · rintro ⟨hpr,hlo,hhi⟩
          exact ⟨hpr,hlo,by omega⟩
        · rintro ⟨hpr,hlo,hhi⟩
          have hne : p ≠ y+i+1 := fun heq => hp (heq ▸ hpr)
          exact ⟨hpr,hlo,by omega⟩

theorem prefix_increasing (y i : ℕ) : (scanned y i).Pairwise (· < ·) := by
  induction i with
  | zero => simp [scanned]
  | succ i ih =>
      unfold scanned
      split
      · rw [List.pairwise_append]
        refine ⟨ih,by simp,?_⟩
        intro a ha b hb
        have hb' : b = y+i+1 := by simpa using hb
        have ha' := (mem_prefix.mp ha).2.2
        omega
      · exact ih

theorem prefix_nodup (y i : ℕ) : (scanned y i).Nodup :=
  (prefix_increasing y i).imp (fun h => Nat.ne_of_lt h)

def values (y : ℕ) : List ℕ := scanned y (3*y)
def size (y : ℕ) : ℕ := (values y).length
def prime (y i : ℕ) : ℕ := (values y).getD i 0

theorem values_increasing (y : ℕ) : (values y).Pairwise (· < ·) := prefix_increasing y (3*y)
theorem values_nodup (y : ℕ) : (values y).Nodup := prefix_nodup y (3*y)
theorem size_le (y : ℕ) : size y ≤ 3*y := prefix_length_le y (3*y)

theorem mem_values {y p : ℕ} :
    p ∈ values y ↔ Nat.Prime p ∧ y < p ∧ p ≤ 4*y := by
  rw [values,mem_prefix]
  constructor
  · rintro ⟨hp,hlo,hhi⟩
    exact ⟨hp,hlo,by omega⟩
  · rintro ⟨hp,hlo,hhi⟩
    exact ⟨hp,hlo,by omega⟩

theorem values_toFinset (y : ℕ) : (values y).toFinset = PrimeDensity.candidates y := by
  ext p
  simp only [List.mem_toFinset,mem_values,PrimeDensity.mem_candidates]

theorem size_eq_card (y : ℕ) : size y = (PrimeDensity.candidates y).card := by
  rw [← values_toFinset,List.toFinset_card_of_nodup (values_nodup y)]
  rfl

theorem prime_mem {y i : ℕ} (hi : i < size y) : prime y i ∈ values y := by
  unfold prime
  rw [List.getD_eq_getElem _ _ hi]
  exact List.mem_of_getElem rfl

theorem prime_spec {y i : ℕ} (hi : i < size y) :
    Nat.Prime (prime y i) ∧ y < prime y i ∧ prime y i ≤ 4*y :=
  mem_values.mp (prime_mem hi)

theorem prime_injective {y i j : ℕ} (hi : i < size y) (hj : j < size y)
    (heq : prime y i = prime y j) : i = j :=
  (List.getD_inj hi hj (values_nodup y)).mp heq

theorem prime_strictly_increasing {y i j : ℕ}
    (hi : i < size y) (hj : j < size y) (hij : i < j) : prime y i < prime y j := by
  unfold prime
  rw [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj]
  exact List.pairwise_iff_getElem.mp (values_increasing y) i j hi hj hij

theorem values_nonempty {y : ℕ} (hy : 0 < y) : values y ≠ [] := by
  obtain ⟨p,hp,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul y hy.ne'
  have hmem : p ∈ values y := mem_values.mpr ⟨hp,hlo,by omega⟩
  intro heq
  simpa only [heq,List.not_mem_nil] using hmem

theorem size_pos {y : ℕ} (hy : 0 < y) : 0 < size y :=
  List.length_pos_iff.mpr (values_nonempty hy)

theorem prime_zero_le {y i : ℕ} (hi : i < size y) : prime y 0 ≤ prime y i := by
  by_cases heq : i = 0
  · simp [heq]
  · exact (prime_strictly_increasing (by omega) hi (by omega)).le

theorem prime_zero_le_mem {y p : ℕ} (hp : p ∈ values y) : prime y 0 ≤ p := by
  obtain ⟨i,hi,heq⟩ := List.mem_iff_getElem.mp hp
  have hm := prime_zero_le (y := y) (i := i) hi
  simpa only [prime,List.getD_eq_getElem _ _ hi,heq] using hm

theorem prime_zero_spec {y : ℕ} (hy : 0 < y) :
    Nat.Prime (prime y 0) ∧ y < prime y 0 ∧ prime y 0 ≤ 2*y := by
  have hp := prime_spec (size_pos hy)
  obtain ⟨p,hpr,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul y hy.ne'
  have hmem : p ∈ values y := mem_values.mpr ⟨hpr,hlo,by omega⟩
  exact ⟨hp.1,hp.2.1,(prime_zero_le_mem hmem).trans hhi⟩

theorem auxiliarySet_eq_candidates (y : ℕ) :
    WeightedScore.auxiliarySet (prime y) (size y) = PrimeDensity.candidates y := by
  rw [← values_toFinset]
  ext p
  simp only [WeightedScore.auxiliarySet,Finset.mem_image,Finset.mem_range,List.mem_toFinset]
  constructor
  · rintro ⟨i,hi,rfl⟩
    exact prime_mem hi
  · intro hp
    obtain ⟨i,hi,heq⟩ := List.mem_iff_getElem.mp hp
    refine ⟨i,hi,?_⟩
    simpa only [prime,List.getD_eq_getElem _ _ hi] using heq

/-- Arguments: lower endpoint and first free address. The output occupies
at most `3*y` cells; the primality helper reuses the scratch beyond them. -/
def body (pTest : ℕ) : Stmt :=
  .set 2 (k 0) ;;
  .set 6 (v 1 +' k 3 *' v 0) ;;
  .for 3 (k 3 *' v 0) (
    .set 4 (v 0 +' v 3 +' k 1) ;;
    .call pTest [v 4,v 6] 5 ;;
    .ite (v 5 =' k 1) (
      .store (v 1 +' v 2) (v 4) ;;
      .set 2 (v 2 +' k 1)) .skip) ;;
  .set 0 (v 2)

def time (y : ℕ) : ℕ := 3*y*(LightPrimality.time (4*y) (4*y)+100)+100
def space (free y : ℕ) : ℕ := free+3*y+(Nat.log 2 (4*y+1)+2)
def word (y : ℕ) : ℕ := 32*y+16

def Inv (μ : ℕ → ℤ) (y free i : ℕ) (σ : State) : Prop :=
  ∃ (cval rval : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [(y : ℤ),free,(scanned y i).length,i,cval,rval,free+3*y],ν⟩ ∧
      SegN ν free (scanned y i) ∧ Kept μ ν free

structure Procs (P : Program) (pMain : ℕ) where
  pTest : ℕ
  test : LightPrimality.Procs P pTest
  main : P[pMain]? = some (body pTest)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {y free : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hy : 0 < y) (hspace : space free y ≤ lim.space)
    (hword : (word y : ℤ) ≤ lim.word) :
    Meets lim P pMain d [y,free] μ (time y)
      (fun r μ' => r = (size y : ℤ) ∧ SegN μ' free (values y) ∧ Kept μ μ' free) := by
  let ct := LightPrimality.time (4*y) (4*y)
  have hwork : free+3*y ≤ lim.space := by unfold space at hspace; omega
  have hwordZ : 32*(y : ℤ)+16 ≤ lim.word := by exact_mod_cast hword
  have htestword : (8*(4*y)+16 : ℕ) ≤ lim.word := by
    have hh : 8*(4*y)+16 = word y := by unfold word; ring
    rw [hh]
    exact hword
  apply Meets.of_body S.main
  unfold body time
  light_set 0
  light_set (free+3*y)
  refine Ends.pieceThen (Ends.for (T := 3*y*(ct+100)+20)
    (Q := Inv μ y free (3*y)) (Inv μ y free) (3*y) (ct+80)
    ?_ ?_ ?_ ?_ (hT := by light_time [ct])) ?_ (hT := by light_time [ct])
  · refine ⟨0,0,μ,?_,?_,fun _ _ => rfl⟩
    · simp [scanned,update_frame_setLocal]
    · simp [scanned,SegN]
  · rintro i _ hi _ ⟨cval,rval,ν,rfl,hseg,hkept⟩
    have hlen := prefix_length_le y i
    have hcmin : 2 ≤ y+i+1 := by omega
    have hcmax : y+i+1 ≤ 4*y := by omega
    have hcword : ((y+i+1 : ℕ) : ℤ) ≤ lim.word := by omega
    light_set (y+i+1) using ct
    light_call (S.test.meets (d := d+1) (n := y+i+1) (free := free+3*y)
      hw hd hcmin hcmax hspace htestword) using ct
      with result ν₁ ⟨hresult,hkeep₁⟩
    subst result
    have hseg₁ : SegN ν₁ free (scanned y i) := by
      apply hseg.congr
      intro j hj
      simp only [List.length_map] at hj
      exact hkeep₁ _ (by omega)
    have hkept₁ : Kept μ ν₁ free := fun j hj => (hkeep₁ j (by omega)).trans (hkept j hj)
    refine Ends.iteLast (fun ht => ?_) (fun hf => ?_) (by light_side)
      (hT := by light_time [ct])
    · have hp : Nat.Prime (y+i+1) := by
        by_contra hn
        simpa [LightPrimality.answer,hn] using ht
      light_store (free+(scanned y i).length) (y+i+1) using ct
      light_set ((scanned y i).length+1) using ct
      refine ⟨by simp,y+i+1,LightPrimality.answer (y+i+1),
        Function.update ν₁ (free+(scanned y i).length) ((y+i+1 : ℕ) : ℤ),?_,?_,?_⟩
      · simp [scanned,hp,update_frame_setLocal]
      · simpa only [scanned,if_pos hp] using hseg₁.snoc (y+i+1)
      · intro j hj
        rw [Function.update_of_ne (by omega)]
        exact hkept₁ j hj
    · have hp : ¬ Nat.Prime (y+i+1) := by
        intro hp
        apply hf
        simp [LightPrimality.answer,hp]
      apply Ends.skip
      refine ⟨by simp,y+i+1,LightPrimality.answer (y+i+1),ν₁,?_,?_,hkept₁⟩
      · simp [scanned,hp,update_frame_setLocal]
      · simpa only [scanned,if_neg hp] using hseg₁
  · intro σ _ hI
    exact hI
  · rintro i _ hi _ ⟨cval,rval,ν,rfl,hseg,hkept⟩
    light_side
  · rintro σ ⟨cval,rval,ν,rfl,hseg,hkept⟩
    have hlen := prefix_length_le y (3*y)
    light_set ((scanned y (3*y)).length) using ct
    exact ⟨by simp [size,values],hseg,hkept⟩

def program : Program := [body 1,LightPrimality.body 2,emodBody]

def program_procs : Procs program 0 where
  pTest := 1
  test := ⟨2,rfl,rfl⟩
  main := rfl

theorem program_meets
    {μ : ℕ → ℤ} {y free : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hy : 0 < y) (hspace : space free y ≤ lim.space)
    (hword : (word y : ℤ) ≤ lim.word) :
    Meets lim program 0 d [y,free] μ (time y)
      (fun r μ' => r = (size y : ℤ) ∧ SegN μ' free (values y) ∧ Kept μ μ' free) :=
  program_procs.meets hw hd hy hspace hword

end ThreeSum.LightPrimePool
