import Submission.ThreeSum.TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma

/-! Exact finite cardinality of genuine typed ternary words. -/

noncomputable section
namespace ThreeSum.TernaryTypeCardinality

open Finset ThreeSum.TernaryJointType ThreeSum.TernaryCoverLocal

set_option maxHeartbeats 2000000

def positions {L : ℕ} (w : TritWord L) (d : Fin 3) : Finset (Fin L) :=
  univ.filter (fun i => w i=d)

theorem positions_card {L : ℕ} (w : TritWord L) (d : Fin 3) :
    (positions w d).card=digitCount w d := by
  simp only [positions,digitCount,Finset.sum_boole,Nat.cast_id]

theorem positions_disjoint {L : ℕ} (w : TritWord L) :
    Disjoint (positions w 2) (positions w 1) := by
  apply Finset.disjoint_left.mpr
  intro i hi2 hi1
  have h2 : w i=2 := (mem_filter.mp hi2).2
  have h1 : w i=1 := (mem_filter.mp hi1).2
  have hh : (2 : Fin 3)=1 := h2.symm.trans h1
  norm_num [Fin.ext_iff] at hh

theorem digitCount_total {L : ℕ} (w : TritWord L) :
    digitCount w 0+digitCount w 1+digitCount w 2=L := by
  unfold digitCount
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  have hlocal (d : Fin 3) : (if d=0 then 1 else 0)+
      (if d=1 then 1 else 0)+(if d=2 then 1 else 0 : ℕ)=1 := by
    fin_cases d <;> norm_num [Fin.ext_iff]
  simp_rw [hlocal]
  simp

abbrev Pair (L : ℕ) := Σ _t : Finset (Fin L), Finset (Fin L)

/-- Choose the two-digit positions first, then one-digit positions in their complement. -/
def digitPairs (L a b : ℕ) : Finset (Pair L) :=
  (univ.powersetCard b).sigma (fun t => (univ\t).powersetCard a)

def encode {L : ℕ} (w : TritWord L) : Pair L :=
  ⟨positions w 2,positions w 1⟩

def decode {L : ℕ} (p : Pair L) : TritWord L := fun i =>
  if i∈p.1 then 2 else if i∈p.2 then 1 else 0

theorem decode_encode {L : ℕ} (w : TritWord L) : decode (encode w)=w := by
  funext i
  unfold decode encode positions
  simp only [mem_filter,mem_univ,true_and]
  generalize h : w i=d
  fin_cases d <;> norm_num [Fin.ext_iff]

theorem encode_injective (L : ℕ) : Function.Injective (@encode L) := by
  intro w v h
  have hh := congrArg decode h
  simpa [decode_encode] using hh

theorem mem_digitPairs {L a b : ℕ} (p : Pair L) :
    p∈digitPairs L a b ↔ p.1.card=b ∧ p.2.card=a ∧ Disjoint p.1 p.2 := by
  classical
  simp only [digitPairs,mem_sigma,mem_powersetCard]
  constructor
  · rintro ⟨⟨ht,hb⟩,⟨ho,ha⟩⟩
    refine ⟨hb,ha,Finset.disjoint_left.mpr ?_⟩
    intro i hiT hiO
    exact (mem_sdiff.mp (ho hiO)).2 hiT
  · rintro ⟨hb,ha,hd⟩
    refine ⟨⟨subset_univ _,hb⟩,⟨?_,ha⟩⟩
    intro i hiO
    exact mem_sdiff.mpr ⟨mem_univ _,fun hiT => Finset.disjoint_left.mp hd hiT hiO⟩

theorem encode_mem {L : ℕ} (π : DigitType) {w : TritWord L} (hw : HasType w π) :
    encode w∈digitPairs L (π 1) (π 2) := by
  rw [mem_digitPairs]
  refine ⟨?_,?_,positions_disjoint w⟩
  · change (positions w 2).card=π 2
    rw [positions_card]
    exact hw 2
  · change (positions w 1).card=π 1
    rw [positions_card]
    exact hw 1

theorem positions_decode_two {L : ℕ} (p : Pair L) : positions (decode p) 2=p.1 := by
  ext i
  simp only [positions,mem_filter,mem_univ,true_and,decode]
  by_cases ht : i∈p.1 <;> by_cases ho : i∈p.2 <;> simp [ht,ho,Fin.ext_iff]

theorem positions_decode_one {L : ℕ} (p : Pair L) (hd : Disjoint p.1 p.2) :
    positions (decode p) 1=p.2 := by
  ext i
  simp only [positions,mem_filter,mem_univ,true_and,decode]
  by_cases ht : i∈p.1
  · have ho : i∉p.2 := fun hi => Finset.disjoint_left.mp hd ht hi
    simp [ht,ho,Fin.ext_iff]
  · by_cases ho : i∈p.2 <;> simp [ht,ho,Fin.ext_iff]

theorem encode_decode {L : ℕ} (p : Pair L) (hd : Disjoint p.1 p.2) :
    encode (decode p)=p := by
  cases p with
  | mk t o =>
    have h2 := positions_decode_two (⟨t,o⟩ : Pair L)
    have h1 := positions_decode_one (⟨t,o⟩ : Pair L) hd
    simp only [encode,h2,h1]

theorem decode_hasType {L : ℕ} (π : DigitType) (htotal : π 0+π 1+π 2=L)
    (p : Pair L) (hp : p∈digitPairs L (π 1) (π 2)) : HasType (decode p) π := by
  obtain ⟨h2,h1,hd⟩ := (mem_digitPairs p).mp hp
  have htwo : digitCount (decode p) 2=π 2 := by
    rw [←positions_card,positions_decode_two,h2]
  have hone : digitCount (decode p) 1=π 1 := by
    rw [←positions_card,positions_decode_one p hd,h1]
  have hz := digitCount_total (decode p)
  have hzero : digitCount (decode p) 0=π 0 := by omega
  intro d
  fin_cases d
  · exact hzero
  · exact hone
  · exact htwo

theorem vertices_card_eq_pairs {L : ℕ} (π : DigitType) (htotal : π 0+π 1+π 2=L) :
    (vertices L π).card=(digitPairs L (π 1) (π 2)).card := by
  classical
  apply Finset.card_bij (fun w _ => encode w)
  · intro w hw
    exact encode_mem π (mem_filter.mp hw).2
  · intro w hw v hv he
    exact encode_injective L he
  · intro p hp
    have hh := (mem_digitPairs p).mp hp
    exact ⟨decode p,mem_filter.mpr ⟨mem_univ _,decode_hasType π htotal p hp⟩,
      encode_decode p hh.2.2⟩

theorem digitPairs_card (L a b : ℕ) :
    (digitPairs L a b).card=L.choose b*(L-b).choose a := by
  classical
  unfold digitPairs
  rw [Finset.card_sigma]
  have hlocal (t : Finset (Fin L)) (ht : t∈(univ : Finset (Fin L)).powersetCard b) :
      ((univ\t).powersetCard a).card=(L-b).choose a := by
    obtain ⟨hs,hc⟩ := mem_powersetCard.mp ht
    rw [card_powersetCard,card_sdiff_of_subset hs]
    simp [hc]
  rw [Finset.sum_congr rfl hlocal]
  simp [card_powersetCard,Nat.mul_comm]

/-- Exact cardinality of the actual fixed-type vertex table used by the cover. -/
theorem vertices_card_eq_choose {L : ℕ} (π : DigitType) (htotal : π 0+π 1+π 2=L) :
    (vertices L π).card=L.choose (π 2)*(L-π 2).choose (π 1) := by
  rw [vertices_card_eq_pairs π htotal,digitPairs_card]

end ThreeSum.TernaryTypeCardinality
