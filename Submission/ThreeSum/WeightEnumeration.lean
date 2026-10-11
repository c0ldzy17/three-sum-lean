import Submission.ThreeSum.LocalHashMoments
import Mathlib.Data.List.Range

/-!
# Ordered radix enumeration of local hash coefficients

The Cartesian-product list used by `allWeights` enumerates the first
coordinate most slowly. The radix index consequently stores that coordinate
in its most significant digit. The equality below is equality of lists,
including their order and repetitions, rather than a membership equivalence.
-/

namespace ThreeSum.WeightEnumeration

open LocalHashMoments

variable {ι K : Type*} [DecidableEq ι] [NatCast K]

/-- Flattening consecutive fixed-width blocks gives the ordinary range. -/
theorem range_blocks (m q : ℕ) :
    (List.range m).flatMap (fun b => (List.range q).map (fun r => b*q+r)) =
      List.range (m*q) := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [List.range_succ,List.flatMap_append,List.flatMap_singleton,ih,Nat.succ_mul]
    exact List.range_add.symm

/-- A dependent-list decoder matching `List.pi` exactly. The remaining
digits are decoded after removing the current most significant digit. -/
def decode (p : ℕ) : (l : List ι) → ℕ → (∀ i, i ∈ l → K)
  | [], _ => List.Pi.nil (fun _ => K)
  | i::l, k => List.Pi.cons i l ((k/p^l.length%p : ℕ) : K) (decode p l (k%p^l.length))

theorem pi_eq_range (p : ℕ) (l : List ι) :
    List.pi l (fun _ => (List.range p).map (fun n : ℕ => (n : K))) =
      (List.range (p^l.length)).map (decode (K := K) p l) := by
  induction l with
  | nil => simp [decode]
  | cons i l ih =>
    rw [List.pi_cons,ih]
    simp only [List.flatMap_map,List.map_map,List.length_cons,pow_succ',← range_blocks,
      List.map_flatMap]
    apply List.flatMap_congr
    intro b hb
    have hbp : b < p := List.mem_range.mp hb
    apply List.map_congr_left
    intro r hr
    have hrq : r < p^l.length := List.mem_range.mp hr
    have hq : 0 < p^l.length := by omega
    have hdiv : (b*p^l.length+r)/p^l.length = b := by
      rw [Nat.add_comm,Nat.add_mul_div_right _ _ hq,Nat.div_eq_of_lt hrq]
      simp
    simp only [Function.comp_apply,decode,hdiv,Nat.mod_eq_of_lt hbp,
      Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hrq]

theorem low_digit (p n e t : ℕ) (he : e < t) :
    (n%p^t)/p^e%p = n/p^e%p := by
  have hpow : p^t = p^e*p^(t-e) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow,Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (dvd_pow_self p (by omega : t-e ≠ 0))]

/-- Each coordinate is the digit at its first occurrence in the list. -/
theorem decode_eq_digit (p : ℕ) (l : List ι) (k : ℕ) (i : ι) (hi : i ∈ l) :
    decode (K := K) p l k i hi = ((k/p^(l.length-1-l.idxOf i)%p : ℕ) : K) := by
  induction l generalizing k i with
  | nil => simp at hi
  | cons a l ih =>
    by_cases hia : i = a
    · subst i
      simp [decode,List.Pi.cons_def]
    · have hil : i ∈ l := (List.mem_cons.mp hi).resolve_left hia
      have hidx : l.idxOf i < l.length := List.idxOf_lt_length_of_mem hil
      simp only [decode,List.Pi.cons_def,dif_neg hia]
      rw [ih (k%p^l.length) i hil,List.idxOf_cons_ne _ (Ne.symm hia)]
      simp only [List.length_cons,Nat.succ_sub_one]
      rw [show l.length-(l.idxOf i+1) = l.length-1-l.idxOf i by omega]
      exact congrArg (fun n : ℕ => (n : K)) (low_digit p k _ _ (by omega))

def liftCoordinate {L : ℕ} (i : Fin L × Bool) : Fin (L+1) × Bool := (i.1.succ,i.2)

theorem liftCoordinate_injective (L : ℕ) :
    Function.Injective (@liftCoordinate L) := by
  intro i j hij
  apply Prod.ext
  · exact Fin.succ_injective L (congrArg Prod.fst hij)
  · exact congrArg (fun z : Fin (L+1) × Bool => z.2) hij

theorem coordinates_succ (L : ℕ) :
    coordinates (L+1) = (0,false)::(0,true)::(coordinates L).map liftCoordinate := by
  simp only [coordinates,List.finRange_succ,List.flatMap_cons,List.flatMap_map,
    List.map_flatMap,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    liftCoordinate]

theorem coordinates_length (L : ℕ) : (coordinates L).length = 2*L := by
  induction L with
  | zero => simp [coordinates]
  | succ L ih =>
    rw [coordinates_succ]
    simp only [List.length_cons,List.length_map,ih]
    omega

theorem idxOf_map_injective {κ : Type*} [DecidableEq κ] (f : ι → κ)
    (hf : Function.Injective f) (l : List ι) (x : ι) :
    (l.map f).idxOf (f x) = l.idxOf x := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.idxOf_cons,hf.beq_eq,ih]

/-- The list order is `(0,false),(0,true),(1,false),(1,true),...`. -/
def coordinateIndex {L : ℕ} (i : Fin L × Bool) : ℕ :=
  2*i.1.val+(if i.2 then 1 else 0)

theorem coordinates_idxOf {L : ℕ} (i : Fin L × Bool) :
    (coordinates L).idxOf i = coordinateIndex i := by
  rcases i with ⟨i,b⟩
  induction L with
  | zero => exact Fin.elim0 i
  | succ L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · cases b <;> simp [coordinates_succ,coordinateIndex]
    · have hmap : ((coordinates L).map liftCoordinate).idxOf (j.succ,b) =
          (coordinates L).idxOf (j,b) := by
        change ((coordinates L).map liftCoordinate).idxOf (liftCoordinate (j,b)) = _
        simp only [List.idxOf,List.findIdx_map,Function.comp_def,
          (liftCoordinate_injective L).beq_eq]
      have hne : (0 : Fin (L+1)) ≠ j.succ := by
        intro he
        have hh := congrArg Fin.val he
        simp only [Fin.val_zero,Fin.val_succ] at hh
        omega
      rw [coordinates_succ]
      simp only [List.idxOf_cons,cond_eq_ite,beq_iff_eq,Prod.mk.injEq,hne,false_and,
        ite_false,hmap,ih j]
      unfold coordinateIndex
      simp only [Fin.val_succ]
      omega

theorem coordinateIndex_lt {L : ℕ} (i : Fin L × Bool) : coordinateIndex i < 2*L := by
  have hi := i.1.isLt
  unfold coordinateIndex
  split <;> omega

def digit (p width k coordinate : ℕ) : ℕ := k/p^(width-1-coordinate)%p

/-- The coefficient function obtained from one ordinary range index. -/
def decodedWeight (L p k : ℕ) : Weight L K :=
  fun i => (digit p (2*L) k (coordinateIndex i) : K)

/-- Exact ordered equality, preserving the occurrence indices used by the
greedy schedule and global hash encoding. -/
theorem allWeights_eq_range (L p : ℕ) :
    allWeights L ((List.range p).map (fun n : ℕ => (n : K))) =
      (List.range (p^(2*L))).map (decodedWeight (K := K) L p) := by
  unfold allWeights
  rw [pi_eq_range,List.map_map,coordinates_length]
  apply List.map_congr_left
  intro k hk
  funext i
  have hidx := coordinates_idxOf i
  simp only [List.idxOf,Bool.beq_eq_decide_eq] at hidx
  simp only [Function.comp_apply,decode_eq_digit,coordinates_length,
    decodedWeight,digit,List.idxOf,Bool.beq_eq_decide_eq,hidx]

theorem allWeights_length (L p : ℕ) :
    (allWeights L ((List.range p).map (fun n : ℕ => (n : K)))).length = p^(2*L) := by
  rw [allWeights_eq_range,List.length_map,List.length_range]

theorem digit_lt {p width k coordinate : ℕ} (hp : 0 < p) : digit p width k coordinate < p :=
  Nat.mod_lt _ hp

theorem decodedWeight_val (L p k : ℕ) (i : Fin L × Bool) :
    (decodedWeight (K := ZMod p) L p k i).val = digit p (2*L) k (coordinateIndex i) := by
  simp [decodedWeight,digit,ZMod.val_natCast]

theorem getElem_allWeights (L p k : ℕ) (hk : k < p^(2*L)) :
    (allWeights L ((List.range p).map (fun n : ℕ => (n : K))))[k]'(by
      rw [allWeights_length]; exact hk) = decodedWeight (K := K) L p k := by
  simp only [allWeights_eq_range,List.getElem_map,List.getElem_range]

theorem getD_allWeights (L p k : ℕ) (fallback : Weight L K) (hk : k < p^(2*L)) :
    (allWeights L ((List.range p).map (fun n : ℕ => (n : K)))).getD k fallback =
      decodedWeight (K := K) L p k := by
  rw [List.getD_eq_getElem _ _ (by rw [allWeights_length]; exact hk)]
  exact getElem_allWeights L p k hk

theorem localWeights_eq_range (h : ℕ) :
    allWeights (512*h) (localValues h) =
      (List.range ((LocalCoverBounds.localPrime h)^(2*(512*h)))).map
        (decodedWeight (K := LocalField h) (512*h) (LocalCoverBounds.localPrime h)) := by
  exact allWeights_eq_range _ _

/-- Rewriting the schedule preserves its precise tie rule and every chosen
map occurrence because the candidate lists are equal in order. -/
theorem localSchedule_eq_radix (h : ℕ) :
    localSchedule h =
      Cover.greedyChoices
        ((List.range ((LocalCoverBounds.localPrime h)^(2*(512*h)))).map
          (decodedWeight (K := LocalField h) (512*h) (LocalCoverBounds.localPrime h)))
        (Covers (512*h) h (bucketBound (512*h) h (Fintype.card (LocalField h))))
        (Finset.univ : Finset (LocalField h × LocalField h))
        (scheduleLength h (Fintype.card (LocalField h))) := by
  unfold localSchedule schedule
  rw [localWeights_eq_range]

end ThreeSum.WeightEnumeration
