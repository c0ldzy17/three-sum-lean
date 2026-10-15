import Submission.ThreeSum.TernaryArenaSeedCandidate

noncomputable section
namespace ThreeSum.TernaryArenaScoreScan
open LightTernaryControllerFactory LightTernarySeedScoreFactory
open TernaryArenaLayout TernaryArenaSourceSetup TernaryArenaSeedCandidate
set_option maxHeartbeats 2000000

/-- The immutable prefix inputs exclude the four result arrays and the
one header cell updated by the wanted-row emitter. -/
def Protected (I : Input) (x : ℕ) : Prop :=
  (x < addr I.free I.capacity 9 ∨ addr I.free I.capacity 13 ≤ x) ∧
  x < addr I.free I.capacity 16 ∧ x ≠ addr I.free I.capacity 1+104

def KeepInputs (I : Input) (μ ν : ℕ→ℤ) : Prop :=
  ∀x, Protected I x → ν x=μ x

theorem KeepInputs.refl (I : Input) (μ : ℕ→ℤ) : KeepInputs I μ μ := fun _ _ => rfl

theorem KeepInputs.trans {I : Input} {μ ν ξ : ℕ→ℤ}
    (h : KeepInputs I μ ν) (g : KeepInputs I ν ξ) : KeepInputs I μ ξ :=
  fun x hx => (g x hx).trans (h x hx)

theorem protected_low {I : Input} {x : ℕ} (hx : x < addr I.free I.capacity 9)
    (hh : x≠addr I.free I.capacity 1+104) : Protected I x := by
  have hm := Nat.mul_le_mul_right I.capacity (show 9≤16 by omega)
  refine ⟨Or.inl hx,?_,hh⟩
  unfold addr at *
  omega

theorem protected_bank {I : Input} {x : ℕ} (hx : addr I.free I.capacity 13≤x)
    (hy : x < addr I.free I.capacity 16) (hc : 106≤I.capacity) : Protected I x := by
  refine ⟨Or.inr hx,hy,?_⟩
  unfold addr at *
  nlinarith

def cell (I : Input) (channel seed : ℕ) : ℕ :=
  addr I.free I.capacity (9+channel)+seed

theorem cell_lt {I : Input} {c i : ℕ} (hi : i < I.capacity) :
    cell I c i < addr I.free I.capacity (10+c) := by
  have hh := offset_lt (free:=I.free) (C:=I.capacity) (slot:=9+c) (len:=I.capacity) hi le_rfl
  rw [show 9+c+1=10+c by omega] at hh
  exact hh

theorem cell_ge (I : Input) (c i : ℕ) :
    addr I.free I.capacity (9+c) ≤ cell I c i := Nat.le_add_right _ _

theorem cell_ne {I : Input} {c d i j : ℕ}
    (hi : i < I.capacity) (hj : j < I.capacity) (h : c≠d ∨ i≠j) :
    cell I c i ≠ cell I d j := by
  rcases lt_trichotomy c d with hcd|hcd|hcd
  · have hm := Nat.mul_le_mul_right I.capacity (show 10+c ≤ 9+d by omega)
    have ha := cell_lt (I:=I) (c:=c) hi
    have hb := cell_ge I d j
    unfold addr at *
    omega
  · subst d
    intro heq
    have heq' : i=j := Nat.add_left_cancel heq
    exact (h.resolve_left (by simp)) heq'
  · have hm := Nat.mul_le_mul_right I.capacity (show 10+d ≤ 9+c by omega)
    have ha := cell_lt (I:=I) (c:=d) hj
    have hb := cell_ge I c i
    unfold addr at *
    omega

theorem cell_protected_ne {I : Input} {c i x : ℕ}
    (hc : c < 4) (hi : i < I.capacity) (hx : Protected I x) : x≠cell I c i := by
  have hlo := Nat.mul_le_mul_right I.capacity (show 9 ≤ 9+c by omega)
  have hhi := Nat.mul_le_mul_right I.capacity (show 10+c ≤ 13 by omega)
  have ha := cell_lt (I:=I) (c:=c) hi
  have hb := cell_ge I c i
  rcases hx with ⟨hx,_,_⟩
  unfold addr at *
  omega

def store (I : Input) (i : ℕ) (v : Fin 4→ℤ) (μ : ℕ→ℤ) : ℕ→ℤ :=
  Function.update (Function.update (Function.update (Function.update μ
    (cell I 0 i) (v 0)) (cell I 1 i) (v 1)) (cell I 2 i) (v 2)) (cell I 3 i) (v 3)

theorem store_other {I : Input} {i x : ℕ} {v : Fin 4→ℤ} {μ : ℕ→ℤ}
    (hx : ∀c < 4, x≠cell I c i) : store I i v μ x=μ x := by
  simp [store, Function.update_of_ne, hx 0 (by omega), hx 1 (by omega),
    hx 2 (by omega), hx 3 (by omega)]

theorem store_read {I : Input} {i : ℕ} (hi : i < I.capacity)
    (v : Fin 4→ℤ) (μ : ℕ→ℤ) (c : Fin 4) : store I i v μ (cell I c i)=v c := by
  have h01 := cell_ne (I:=I) (c:=0) (d:=1) hi hi (Or.inl (by omega))
  have h02 := cell_ne (I:=I) (c:=0) (d:=2) hi hi (Or.inl (by omega))
  have h03 := cell_ne (I:=I) (c:=0) (d:=3) hi hi (Or.inl (by omega))
  have h12 := cell_ne (I:=I) (c:=1) (d:=2) hi hi (Or.inl (by omega))
  have h13 := cell_ne (I:=I) (c:=1) (d:=3) hi hi (Or.inl (by omega))
  have h23 := cell_ne (I:=I) (c:=2) (d:=3) hi hi (Or.inl (by omega))
  fin_cases c <;> simp [store, h01, h02, h03, h12, h13, h23]

def Scores (I : Input) (values : ℕ→Fin 4→ℤ) (n : ℕ) (μ : ℕ→ℤ) : Prop :=
  ∀i < n, ∀c : Fin 4, μ (cell I c i)=values i c

def Invariant (I : Input) (values : ℕ→Fin 4→ℤ) (μ : ℕ→ℤ) (n : ℕ) (ν : ℕ→ℤ) : Prop :=
  KeepInputs I μ ν ∧ Scores I values n ν

theorem initial (I : Input) (values : ℕ→Fin 4→ℤ) (μ : ℕ→ℤ) :
    Invariant I values μ 0 μ := by
  exact ⟨fun _ _ => rfl, fun _ h => by omega⟩

variable {p r : ℕ} [Fact p.Prime]

def values {I : Input} {A : Inputs} (D : Family (config p r I A 0)) (K i : ℕ) : Fin 4→ℤ :=
  ![D.flag i,D.scoreB i,D.scoreC i,D.scoreP K i]

theorem done_keep {I : Input} {A : Inputs} {D : Family (config p r I A 0)}
    {K i : ℕ} {ν ξ : ℕ→ℤ} (hi : i < I.capacity)
    (done : (D.candidate i).Done K ν ξ) : KeepInputs I ν ξ := by
  obtain ⟨ζ,hkeep,rfl⟩ := done
  change KeepInputs I ν (store I i (values D K i) ζ)
  intro x hx
  rw [store_other (fun c hc => cell_protected_ne hc hi hx)]
  exact hkeep x hx.2.1 hx.2.2

theorem reads {I : Input} {A : Inputs} {D : Family (config p r I A 0)}
    {K n U : ℕ} {μ ν : ℕ→ℤ} (h : Invariant I (values D K) μ n ν)
    (hf : ∀i < n, |D.flag i|≤1) (hb : ∀i < n, |D.scoreB i|≤U)
    (hc : ∀i < n, |D.scoreC i|≤U) (hp : ∀i < n, |D.scoreP K i|≤U) :
    (∀i < n, ν ((config p r I A 0).flags+i)=D.flag i ∧ |D.flag i|≤1) ∧
    (∀i < n, ν ((config p r I A 0).scoreB+i)=D.scoreB i ∧ |D.scoreB i|≤U) ∧
    (∀i < n, ν ((config p r I A 0).scoreC+i)=D.scoreC i ∧ |D.scoreC i|≤U) ∧
    (∀i < n, ν ((config p r I A 0).scorePaired+i)=D.scoreP K i ∧ |D.scoreP K i|≤U) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i hi
    exact ⟨h.2 i hi 0,hf i hi⟩
  · intro i hi
    exact ⟨h.2 i hi 1,hb i hi⟩
  · intro i hi
    exact ⟨h.2 i hi 2,hc i hi⟩
  · intro i hi
    exact ⟨h.2 i hi 3,hp i hi⟩

/-- A checked candidate preserves every previously collected score and
every immutable arena input, and writes the four new scores exactly. -/
theorem next {I : Input} {A : Inputs} {D : Family (config p r I A 0)}
    {K i : ℕ} {μ ν ξ : ℕ→ℤ} (hcapacity : 106 ≤ I.capacity) (hi : i < I.capacity)
    (h : Invariant I (values D K) μ i ν) (done : (D.candidate i).Done K ν ξ) :
    Invariant I (values D K) μ (i+1) ξ := by
  obtain ⟨ζ,hkeep,rfl⟩ := done
  change Invariant I (values D K) μ (i+1) (store I i (values D K i) ζ)
  constructor
  · intro x hx
    rw [store_other (fun c hc => cell_protected_ne hc hi hx)]
    exact (hkeep x hx.2.1 hx.2.2).trans (h.1 x hx)
  · intro j hj c
    by_cases hji : j=i
    · subst j
      exact store_read hi _ _ c
    · have hjlt : j < i := by omega
      rw [store_other (fun d _ => cell_ne (lt_trans hjlt hi) hi (Or.inr hji))]
      have hbelow : cell I c j < addr I.free I.capacity 16 := by
        have hh := cell_lt (I:=I) (c:=c.val) (lt_trans hjlt hi)
        have hm := Nat.mul_le_mul_right I.capacity (show 10+c.val ≤ 16 by omega)
        unfold addr at *
        omega
      have hheader : cell I c j ≠ addr I.free I.capacity 1+104 := by
        have hh := cell_ge I c.val j
        unfold addr at *
        have hm : 1*I.capacity ≤ (9+c.val)*I.capacity := Nat.mul_le_mul_right _ (by omega)
        nlinarith
      rw [hkeep _ hbelow hheader]
      exact h.2 j hjlt c

end ThreeSum.TernaryArenaScoreScan
