import Submission.ThreeSum.TernaryReconstruction
import Submission.ThreeSum.TernaryNearEnumeration
import Submission.ThreeSum.TernaryNearBankEnumeration

/-! The frozen query tree is bounded by the genuine deficit-neighborhood tree. -/

namespace ThreeSum.TernaryFrozenQueryCost

open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery

set_option maxHeartbeats 2000000

def caps {N : ℕ} (coords : List (Fin N)) (R : TritWord N) : List ℕ :=
  coords.map (fun i => (R i).val)

def work {N : ℕ} (T : ℕ) : List (Fin N)→TritWord N→ℕ
  | [], _ => 1
  | i::rest, R => if rank R≤T then 1 else
      1+∑ d : Fin 3, if d≤R i then work T rest (Function.update R i d) else 0

theorem visits_pos (qs : List ℕ) (D : ℕ) : 1≤TernaryNearEnumeration.visits qs D := by
  cases qs <;> simp [TernaryNearEnumeration.visits]

theorem rank_update_loss {N : ℕ} (R : TritWord N) (i : Fin N) (d : Fin 3)
    (hd : d≤R i) : rank (Function.update R i d)+((R i).val-d.val)=rank R := by
  have hh := rank_add_deficit (update_below R i d hd)
  have hdef : deficit R (Function.update R i d)=(R i).val-d.val := by
    unfold deficit
    have hterm (j : Fin N) : (R j).val-(Function.update R i d j).val =
        if j=i then (R i).val-d.val else 0 := by
      by_cases hj : j=i
      · subst j; simp
      · simp [Function.update_of_ne hj,hj]
    simp_rw [hterm]
    simp
  simpa [hdef] using hh

theorem caps_update_of_not_mem {N : ℕ} (coords : List (Fin N)) (R : TritWord N)
    (i : Fin N) (d : Fin 3) (hi : i∉coords) :
    caps coords (Function.update R i d)=caps coords R := by
  unfold caps
  apply List.map_congr_left
  intro j hj
  have hn : j≠i := by intro h; subst j; exact hi hj
  simp [Function.update_of_ne hn]

theorem visits_cons_all (q : Fin 3) (qs : List ℕ) (D : ℕ) (hD : 2≤D) :
    TernaryNearEnumeration.visits (q.val::qs) D=
      1+∑ d : Fin 3, if d≤q then
        TernaryNearEnumeration.visits qs (D-(q.val-d.val)) else 0 := by
  have hD1 : 1≤D := by omega
  fin_cases q <;> simp [TernaryNearEnumeration.visits,TernaryNearEnumeration.digits,
    List.range_succ,Fin.sum_univ_succ,Fin.le_def,hD,hD1,Nat.add_assoc]

/-- One extra deficit unit permits the final trit-2 jump across the bank cutoff. -/
theorem work_le_visits {N : ℕ} (T : ℕ) (coords : List (Fin N))
    (hcoords : coords.Nodup) (R : TritWord N) :
    work T coords R≤TernaryNearEnumeration.visits (caps coords R) (rank R+1-T) := by
  induction coords generalizing R with
  | nil => simp [work,caps,TernaryNearEnumeration.visits]
  | cons i rest ih =>
    obtain ⟨hi,hn⟩ := List.nodup_cons.mp hcoords
    by_cases hbank : rank R≤T
    · simpa [work,hbank] using visits_pos (caps (i::rest) R) (rank R+1-T)
    · have hD : 2≤rank R+1-T := by omega
      simp only [work,hbank,↓reduceIte,caps,List.map_cons]
      rw [visits_cons_all (R i) _ _ hD]
      apply Nat.add_le_add_left
      apply Finset.sum_le_sum
      intro d hd
      by_cases hlow : d≤R i
      · simp only [hlow,↓reduceIte]
        have hr := rank_update_loss R i d hlow
        have hbudget : rank (Function.update R i d)+1-T=
            (rank R+1-T)-((R i).val-d.val) := by omega
        have hc := ih hn (Function.update R i d)
        rw [hbudget,caps_update_of_not_mem rest R i d hi] at hc
        exact hc
      · simp [hlow]

theorem work_le_near_count {N : ℕ} (T : ℕ) (coords : List (Fin N))
    (hcoords : coords.Nodup) (R : TritWord N) :
    work T coords R≤(coords.length+1)*
      (TernaryNearEnumeration.words (caps coords R) (rank R+1-T)).length := by
  have hw := work_le_visits T coords hcoords R
  have hn := TernaryNearEnumeration.visits_le (caps coords R) (rank R+1-T)
  simpa [caps] using hw.trans hn

theorem caps_digits {N : ℕ} (coords : List (Fin N)) (R : TritWord N) :
    ∀ d∈caps coords R, d<3 := by
  intro d hd
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hd
  exact (R i).isLt

def capWord {N : ℕ} (coords : List (Fin N)) (R : TritWord N) : TritWord coords.length :=
  TernaryBankEnumeration.fromList (caps coords R) (by simp [caps]) (caps_digits coords R)

theorem wordList_capWord {N : ℕ} (coords : List (Fin N)) (R : TritWord N) :
    TernaryBankEnumeration.wordList (capWord coords R)=caps coords R :=
  TernaryBankEnumeration.wordList_fromList _ _ _

theorem work_le_capWord_card {N : ℕ} (T : ℕ) (coords : List (Fin N))
    (hcoords : coords.Nodup) (R : TritWord N) :
    work T coords R≤(coords.length+1)*(nearWords (capWord coords R) (rank R+1-T)).card := by
  have hw := work_le_near_count T coords hcoords R
  have hcard : (TernaryNearEnumeration.words (caps coords R) (rank R+1-T)).length =
      (nearWords (capWord coords R) (rank R+1-T)).card := by
    rw [←wordList_capWord coords R,←TernaryNearEnumeration.codes_length,
      TernaryNearBankEnumeration.codes_length_eq_nearWords_card]
  simpa [hcard] using hw

theorem work_gibbs_counts {N : ℕ} (T : ℕ) (coords : List (Fin N))
    (hcoords : coords.Nodup) (R : TritWord N) (z : ℝ) (hz : 0≤z) (hz1 : z≤1) :
    (work T coords R : ℝ)*z^(rank R+1-T) ≤
      (coords.length+1)*(1+z)^digitCount (capWord coords R) 1 *
        (1+z+z^2)^digitCount (capWord coords R) 2 := by
  have hw : (work T coords R : ℝ)≤
      (coords.length+1)*(nearWords (capWord coords R) (rank R+1-T)).card := by
    exact_mod_cast work_le_capWord_card T coords hcoords R
  have hg := nearWords_card_gibbs_counts (capWord coords R) (rank R+1-T) z hz hz1
  calc
    (work T coords R : ℝ)*z^(rank R+1-T) ≤
        ((coords.length+1)*(nearWords (capWord coords R) (rank R+1-T)).card)*z^(rank R+1-T) :=
      mul_le_mul_of_nonneg_right hw (pow_nonneg hz _)
    _ = (coords.length+1)*((nearWords (capWord coords R) (rank R+1-T)).card*z^(rank R+1-T)) := by ring
    _ ≤ (coords.length+1)*((1+z)^digitCount (capWord coords R) 1 *
        (1+z+z^2)^digitCount (capWord coords R) 2) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ = (coords.length+1)*(1+z)^digitCount (capWord coords R) 1 *
        (1+z+z^2)^digitCount (capWord coords R) 2 := by ring

end ThreeSum.TernaryFrozenQueryCost
