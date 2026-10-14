import Submission.ThreeSum.TernaryAddresses

/-!
# Pruned enumeration below one query word

This is the exact finite list used for a query's bounded deficit neighborhood.
Every recursive node has a completion, so the recursion tree is bounded by
the output count times the word length plus one.
-/

namespace ThreeSum.TernaryNearEnumeration

open ThreeSum.TernaryAddresses

def digits (q D : ℕ) : List ℕ :=
  (List.range (q+1)).filter (fun r => q-r ≤ D)

@[simp] theorem mem_digits {q D r : ℕ} :
    r ∈ digits q D ↔ r ≤ q ∧ q-r ≤ D := by
  simp [digits]

def words : List ℕ → ℕ → List (List ℕ)
  | [], _ => [[]]
  | q :: qs, D => (digits q D).flatMap fun r =>
      (words qs (D-(q-r))).map (List.cons r)

def visits : List ℕ → ℕ → ℕ
  | [], _ => 1
  | q :: qs, D => 1+((digits q D).map fun r => visits qs (D-(q-r))).sum

def Admitted : List ℕ → List ℕ → ℕ → Prop
  | [], [], _ => True
  | q :: qs, r :: rs, D => r ≤ q ∧ q-r ≤ D ∧ Admitted qs rs (D-(q-r))
  | _, _, _ => False

theorem mem_words (qs rs : List ℕ) (D : ℕ) : rs ∈ words qs D ↔ Admitted qs rs D := by
  induction qs generalizing rs D with
  | nil => cases rs <;> simp [words,Admitted]
  | cons q qs ih =>
    cases rs with
    | nil => simp [words,Admitted]
    | cons r rs =>
      simp only [words,List.mem_flatMap,List.mem_map]
      constructor
      · rintro ⟨d,hd,xs,hxs,he⟩
        obtain ⟨rfl,rfl⟩ := List.cons.inj he
        exact ⟨(mem_digits.mp hd).1,(mem_digits.mp hd).2,(ih _ _).mp hxs⟩
      · rintro ⟨hr,hD,hrest⟩
        exact ⟨r,mem_digits.mpr ⟨hr,hD⟩,rs,(ih _ _).mpr hrest,rfl⟩

theorem self_admitted (qs : List ℕ) (D : ℕ) : Admitted qs qs D := by
  induction qs generalizing D with
  | nil => trivial
  | cons q qs ih => simpa [Admitted] using ih D

theorem words_nonempty (qs : List ℕ) (D : ℕ) : 0 < (words qs D).length :=
  List.length_pos_of_mem ((mem_words qs qs D).mpr (self_admitted qs D))

theorem admitted_length {qs rs : List ℕ} {D : ℕ} (h : Admitted qs rs D) :
    rs.length = qs.length := by
  induction qs generalizing rs D with
  | nil => cases rs <;> simp_all [Admitted]
  | cons q qs ih =>
    cases rs with
    | nil => simp [Admitted] at h
    | cons r rs => simpa only [List.length_cons] using congrArg Nat.succ (ih h.2.2)

theorem admitted_forall₂ {qs rs : List ℕ} {D : ℕ} (h : Admitted qs rs D) :
    List.Forall₂ (· ≤ ·) rs qs := by
  induction qs generalizing rs D with
  | nil => cases rs <;> simp_all [Admitted]
  | cons q qs ih =>
    cases rs with
    | nil => simp [Admitted] at h
    | cons r rs => exact List.Forall₂.cons h.1 (ih h.2.2)

theorem admitted_deficit {qs rs : List ℕ} {D : ℕ} (h : Admitted qs rs D) :
    (List.zipWith Nat.sub qs rs).sum ≤ D := by
  induction qs generalizing rs D with
  | nil => cases rs <;> simp_all [Admitted]
  | cons q qs ih =>
    cases rs with
    | nil => simp [Admitted] at h
    | cons r rs =>
      have ht := ih h.2.2
      simp only [List.zipWith_cons_cons,List.sum_cons]
      change q-r+(List.zipWith Nat.sub qs rs).sum ≤ D
      have hd := h.2.1
      omega

theorem admitted_iff (qs rs : List ℕ) (D : ℕ) :
    Admitted qs rs D ↔ List.Forall₂ (· ≤ ·) rs qs ∧
      (List.zipWith Nat.sub qs rs).sum ≤ D := by
  constructor
  · intro h
    exact ⟨admitted_forall₂ h,admitted_deficit h⟩
  · induction qs generalizing rs D with
    | nil =>
      cases rs <;> simp [Admitted]
    | cons q qs ih =>
      cases rs with
      | nil => simp [List.forall₂_cons]
      | cons r rs =>
        rintro ⟨hpair,hsum⟩
        have hp := List.forall₂_cons.mp hpair
        simp only [List.zipWith_cons_cons,List.sum_cons,Nat.sub_eq] at hsum
        refine ⟨hp.1,by omega,?_⟩
        apply ih
        exact ⟨hp.2,by omega⟩

theorem admitted_digits {qs rs : List ℕ} {D : ℕ}
    (hq : ∀ q ∈ qs, q < 3) (h : Admitted qs rs D) : ∀ r ∈ rs, r < 3 := by
  induction qs generalizing rs D with
  | nil => cases rs <;> simp_all [Admitted]
  | cons q qs ih =>
    cases rs with
    | nil => simp [Admitted] at h
    | cons r rs =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h.1.trans_lt (hq q (by simp))
      · exact ih (fun y hy => hq y (by simp [hy])) h.2.2 x hx

def codes : List ℕ → ℕ → List ℕ
  | [], _ => [0]
  | q :: qs, D => (digits q D).flatMap fun r =>
      (codes qs (D-(q-r))).map (fun a => digitCode r*4^qs.length+a)

theorem codes_eq_map (qs : List ℕ) (D : ℕ) : codes qs D = (words qs D).map code := by
  induction qs generalizing D with
  | nil => simp [codes,words,code]
  | cons q qs ih =>
    simp only [codes,words,List.map_flatMap]
    congr 1
    funext r
    rw [ih]
    simp only [List.map_map]
    apply List.map_congr_left
    intro rs hrs
    have hl := admitted_length ((mem_words qs rs (D-(q-r))).mp hrs)
    simp [code,hl]

@[simp] theorem codes_length (qs : List ℕ) (D : ℕ) :
    (codes qs D).length = (words qs D).length := by simp [codes_eq_map]

theorem mem_codes_lt {qs : List ℕ} {D a : ℕ}
    (hq : ∀ q ∈ qs, q < 3) (ha : a ∈ codes qs D) : a < 4^qs.length := by
  rw [codes_eq_map] at ha
  obtain ⟨rs,hrs,rfl⟩ := List.mem_map.mp ha
  have had := (mem_words qs rs D).mp hrs
  simpa only [admitted_length had] using code_lt rs (admitted_digits hq had)

theorem codes_strictly_sorted (qs : List ℕ) (D : ℕ) (hq : ∀ q ∈ qs, q < 3) :
    (codes qs D).Pairwise (· < ·) := by
  induction qs generalizing D with
  | nil => simp [codes]
  | cons q qs ih =>
    have hq0 := hq q (by simp)
    have htail : ∀ q ∈ qs, q < 3 := fun r hr => hq r (by simp [hr])
    rw [codes,List.pairwise_flatMap]
    constructor
    · intro r hr
      rw [List.pairwise_map]
      exact (ih _ htail).imp (fun h => Nat.add_lt_add_left h _)
    · have hdigits : (digits q D).Pairwise (· < ·) := List.pairwise_lt_range.filter _
      apply hdigits.imp_of_mem
      intro r s hr hs hrs a ha b hb
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hb
      have hr3 := ((mem_digits.mp hr).1).trans_lt hq0
      have hs3 := ((mem_digits.mp hs).1).trans_lt hq0
      have hdc := digitCode_strict hr3 hs3 hrs
      have hx4 := mem_codes_lt htail hx
      have hp : 0 < 4^qs.length := by positivity
      nlinarith

theorem words_nodup (qs : List ℕ) (D : ℕ) (hq : ∀ q ∈ qs, q < 3) :
    (words qs D).Nodup := by
  have hn : (codes qs D).Nodup := (codes_strictly_sorted qs D hq).imp (fun h => Nat.ne_of_lt h)
  rw [codes_eq_map] at hn
  exact List.Nodup.of_map code hn

private theorem sum_map_mono (l : List ℕ) (f g : ℕ → ℕ)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons]
    exact Nat.add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

private theorem sum_map_mul (l : List ℕ) (c : ℕ) (f : ℕ → ℕ) :
    (l.map (fun x => c*f x)).sum = c*(l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.mul_add]

theorem visits_le (qs : List ℕ) (D : ℕ) :
    visits qs D ≤ (qs.length+1)*(words qs D).length := by
  induction qs generalizing D with
  | nil => simp [visits,words]
  | cons q qs ih =>
    have hs := sum_map_mono (digits q D)
      (fun r => visits qs (D-(q-r)))
      (fun r => (qs.length+1)*(words qs (D-(q-r))).length)
      (fun r _ => ih (D-(q-r)))
    rw [sum_map_mul] at hs
    have hlen : (words (q::qs) D).length =
      ((digits q D).map fun r => (words qs (D-(q-r))).length).sum := by
      simp [words,List.length_flatMap]
    rw [← hlen] at hs
    have hp := words_nonempty (q::qs) D
    simp only [visits,List.length_cons]
    nlinarith

theorem visits_le_codes (qs : List ℕ) (D : ℕ) :
    visits qs D ≤ (qs.length+1)*(codes qs D).length := by
  simpa only [codes_length] using visits_le qs D

end ThreeSum.TernaryNearEnumeration
