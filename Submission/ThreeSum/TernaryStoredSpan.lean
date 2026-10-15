import Submission.ThreeSum.LightSpanCatalogTest

/-! A genuine stored-matrix invariant for incremental span construction. -/
noncomputable section
namespace ThreeSum.TernaryStoredSpan
open ThreeSum
set_option maxHeartbeats 3000000

variable {p J n : ℕ}

def Represents (f : ℕ → ℕ → ℕ) (n : ℕ) (rows : List (Fin J → ZMod p)) : Prop :=
  ∀ w : Fin J → ZMod p, w∈Submodule.span (ZMod p) {v | v∈rows} ↔
    ∃ k<n, ∀ i : Fin J, (f k i.val : ZMod p)=w i

/-- Quotients below describe the mathematical output order only. The actual
program obtains coefficients and old indices from its two bounded loops. -/
def next (f : ℕ → ℕ → ℕ) (row : ℕ → ℕ) (p n k i : ℕ) : ℕ :=
  (f (k%n) i+(k/n)*row i)%p

theorem represents_zero : Represents (p := p) (J := J) (fun _ _ => 0) 1 [] := by
  intro w
  have he : {v | v∈([] : List (Fin J → ZMod p))}=(∅ : Set (Fin J → ZMod p)) := by ext v; simp
  rw [he,Submodule.span_empty,Submodule.mem_bot]
  constructor
  · intro h
    subst w
    exact ⟨0,by decide,by intro i; simp⟩
  · rintro ⟨k,hk,he⟩
    exact funext (fun i => by simpa using (he i).symm)

theorem next_at (f : ℕ → ℕ → ℕ) (row : ℕ → ℕ) (hp : 0<n) {a k : ℕ} (hk : k<n) (i : ℕ) :
    next f row p n (a*n+k) i=(f k i+a*row i)%p := by
  have hd : (a*n+k)/n=a := by
    rw [Nat.add_comm,Nat.add_mul_div_right k a hp,Nat.div_eq_of_lt hk,Nat.zero_add]
  unfold next
  rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hk,hd]

theorem represents_next [Fact p.Prime] (f : ℕ → ℕ → ℕ) (row : Fin J → ZMod p)
    (rows : List (Fin J → ZMod p)) (hn : 0<n) (H : Represents f n rows) :
    Represents (next f (fun i => if hi : i<J then (row ⟨i,hi⟩).val else 0) p n) (p*n) (row::rows) := by
  intro w
  have hs : {v | v∈row::rows}=insert row {v | v∈rows} := by
    ext v
    simp only [Set.mem_setOf_eq,Set.mem_insert_iff,List.mem_cons]
  rw [hs]
  constructor
  · intro hw
    obtain ⟨a,v,hv,he⟩ := (Submodule.mem_span_insert (R := ZMod p) (x := w) (y := row)
      (s := {v | v∈rows})).mp hw
    obtain ⟨k,hk,hvrep⟩ := (H v).mp hv
    have ha := ZMod.val_lt a
    refine ⟨a.val*n+k,?_,?_⟩
    · have hb := Nat.mul_le_mul_right n (show a.val+1≤p by omega)
      nlinarith
    · intro i
      rw [next_at _ _ hn hk i.val]
      simp only [dif_pos i.isLt,ZMod.natCast_mod,Nat.cast_add,Nat.cast_mul,ZMod.natCast_zmod_val]
      rw [hvrep i]
      have hi := congrArg (fun v : Fin J → ZMod p => v i) he
      simpa [Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_comm] using hi.symm
  · rintro ⟨q,hq,hrep⟩
    let k := q%n
    let a : ZMod p := (q/n : ℕ)
    let v : Fin J → ZMod p := fun i => (f k i.val : ZMod p)
    have hk : k<n := Nat.mod_lt _ hn
    have hv : v∈Submodule.span (ZMod p) {v | v∈rows} := (H v).mpr ⟨k,hk,fun _ => rfl⟩
    have hw : w=a • row+v := by
      funext i
      have hh := hrep i
      simp only [next,dif_pos i.isLt,ZMod.natCast_mod,Nat.cast_add,Nat.cast_mul,ZMod.natCast_zmod_val] at hh
      simpa [a,v,k,Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_comm] using hh.symm
    exact (Submodule.mem_span_insert (R := ZMod p) (x := w) (y := row)
      (s := {v | v∈rows})).mpr ⟨a,v,hv,hw⟩

/-- The actual coefficient/old-row nested output is the complete next matrix. -/
theorem read_next {μ : ℕ → ℤ} {src J p n : ℕ} (f : ℕ → ℕ → ℕ) (row : ℕ → ℕ) (hn : 0<n)
    (H : ∀ a<p, ∀ k<n, ∀ i<J, μ (src+J*n*a+J*k+i)=LightSpanAxpy.values (f k) row a p i) :
    ∀ q<p*n, ∀ i<J, μ (src+J*q+i)=(next f row p n q i : ℤ) := by
  intro q hq i hi
  have ha : q/n<p := (Nat.div_lt_iff_lt_mul hn).mpr (by simpa only [Nat.mul_comm] using hq)
  have hk : q%n<n := Nat.mod_lt _ hn
  have hh := H (q/n) ha (q%n) hk i hi
  have he : J*q=J*n*(q/n)+J*(q%n) := by
    have hz := Nat.div_add_mod q n
    calc
      J*q=J*(n*(q/n)+q%n) := congrArg (fun x => J*x) hz.symm
      _=_ := by ring
  simpa only [he,LightSpanAxpy.values,next,Nat.add_assoc] using hh

/-- Exact digit-restriction admissibility follows from actual coordinate
comparisons and the established physical catalog invariant. -/
theorem present_iff [Fact p.Prime] (f : ℕ → ℕ → ℕ) (n : ℕ)
    (rows : List (Fin J → ZMod p)) (row : Fin J → ZMod p)
    (H : Represents f n rows) (hf : ∀ k<n, ∀ i<J, f k i<p) :
    LightSpanCatalogTest.Present (fun k i => (f k i : ℤ))
      (fun i => if hi : i<J then ((row ⟨i,hi⟩).val : ℤ) else 0) J n ↔
      row∈Submodule.span (ZMod p) {v | v∈rows} := by
  rw [H row]
  constructor
  · rintro ⟨k,hk,he⟩
    refine ⟨k,hk,?_⟩
    intro i
    have hh := he i.val i.isLt
    simp only [dif_pos i.isLt] at hh
    have hn : f k i.val=(row i).val := by exact_mod_cast hh
    rw [hn,ZMod.natCast_zmod_val]
  · rintro ⟨k,hk,he⟩
    refine ⟨k,hk,?_⟩
    intro i hi
    have hh := congrArg ZMod.val (he ⟨i,hi⟩)
    simpa [ZMod.val_natCast,Nat.mod_eq_of_lt (hf k hk i hi),hi] using
      congrArg (fun x : ℕ => (x : ℤ)) hh

end ThreeSum.TernaryStoredSpan
