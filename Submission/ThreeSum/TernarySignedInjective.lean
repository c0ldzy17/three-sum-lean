import Submission.ThreeSum.TernarySignedModes

/-! Original integer identities survive the bounded tagged digit encoding. -/
namespace ThreeSum.TernarySignedInjective
open TernarySignedDigits TernarySignedReduction TernarySignedModes Finset

private theorem digits_determine {radix J x y : ℕ}
    (hx : x<radix^J) (hy : y<radix^J)
    (h : ∀ j : Fin J, digit radix x j=digit radix y j) : x=y := by
  have he : evaluate radix J (fun j => (digit radix x j : ℤ))=
      evaluate radix J (fun j => (digit radix y j : ℤ)) := by
    apply sum_congr rfl
    intro j hj
    dsimp only
    rw [h ⟨j,mem_range.mp hj⟩]
  rw [evaluate_digits_of_lt hx,evaluate_digits_of_lt hy] at he
  exact_mod_cast he

theorem leftRaw_injective {U radix J : ℕ} {b b' : ℤ}
    (hb : |b|≤(U : ℤ)) (hb' : |b'|≤(U : ℤ)) (hcap : 4*U<radix^J)
    (he : leftRaw U radix J b=leftRaw U radix J b') : b=b' := by
  have h : shiftOne U b=shiftOne U b' := digits_determine
    (shiftOne_lt hb hcap) (shiftOne_lt hb' hcap) (fun j => by
      have hh := congrFun he (.inl j)
      simp only [leftRaw,neg_inj] at hh
      exact_mod_cast hh)
  have hcast : (shiftOne U b : ℤ)=(shiftOne U b' : ℤ) := by exact_mod_cast h
  rw [shiftOne_cast hb,shiftOne_cast hb'] at hcast
  omega

theorem rightRaw_injective {U radix J : ℕ} {c c' : ℤ}
    (hc : |c|≤(U : ℤ)) (hc' : |c'|≤(U : ℤ)) (hcap : 4*U<radix^J)
    (he : rightRaw U radix J c=rightRaw U radix J c') : c=c' := by
  have h : shiftTwo U c=shiftTwo U c' := digits_determine
    (shiftTwo_lt hc hcap) (shiftTwo_lt hc' hcap) (fun j => by
      have hh := congrFun he (.inl j)
      simp only [rightRaw] at hh
      exact_mod_cast hh)
  have hcast : (shiftTwo U c : ℤ)=(shiftTwo U c' : ℤ) := by exact_mod_cast h
  rw [shiftTwo_cast hc,shiftTwo_cast hc'] at hcast
  omega

theorem fieldLeft_injective {p U radix J : ℕ} (hb : 1<radix) (hp : 2*radix<p)
    {b b' : ℤ} (hB : |b|≤(U : ℤ)) (hB' : |b'|≤(U : ℤ))
    (hcap : 4*U<radix^J)
    (he : fieldLeft p U radix J b=fieldLeft p U radix J b') : b=b' := by
  apply leftRaw_injective hB hB' hcap
  funext k
  exact intCast_bounded_injective hp (leftRaw_abs hb b k) (leftRaw_abs hb b' k) (congrFun he k)

theorem fieldRight_injective {p U radix J : ℕ} (hb : 1<radix) (hp : 2*radix<p)
    {c c' : ℤ} (hC : |c|≤(U : ℤ)) (hC' : |c'|≤(U : ℤ))
    (hcap : 4*U<radix^J)
    (he : fieldRight p U radix J c=fieldRight p U radix J c') : c=c' := by
  apply rightRaw_injective hC hC' hcap
  funext k
  exact intCast_bounded_injective hp (rightRaw_abs hb c k) (rightRaw_abs hb c' k) (congrFun he k)

end ThreeSum.TernarySignedInjective
